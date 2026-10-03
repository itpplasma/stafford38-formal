#!/usr/bin/env python3
"""Behavioral adapter tests; no scheduler or proof jobs are launched."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import signal
import time
import sys
import tempfile
import unittest

GUARD = Path(__file__).resolve().parents[1] / 'linux-slurm-guard.py'
spec = importlib.util.spec_from_file_location('guard', GUARD)
a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)


class Tests(unittest.TestCase):
    def test_placement(self):
        env = dict(SLURM_CLUSTER_NAME='acluster', SLURM_JOB_ID='123', SLURMD_NODENAME='node14',
                   SLURM_CPUS_PER_TASK='2', SLURM_STEP_ID='0', SLURM_NTASKS='1', SLURM_JOB_NUM_NODES='1')
        self.assertEqual(a.placement(env, 'node14', '0::/slurm/job_123/step_0', {2, 3}), [])
        for host, cg, cpus in [('faepop1', '/job_123/', {2, 3}), ('node14', '/job_124/', {2, 3}),
                               ('node14', '/job_123/', {2, 3, 4}), ('acluster', '/job_123/', {2, 3})]:
            self.assertTrue(a.placement(env, host, cg, cpus))

    def run_child(self, child, mode='normal', timeout=1):
        with tempfile.TemporaryDirectory() as root:
            driver = '''import importlib.util,os,sys,time
from pathlib import Path
spec=importlib.util.spec_from_file_location('adapter',sys.argv[1]); a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
a.placement=lambda:[]
a.foreign_lean=lambda:[]
a.g.snapshot=lambda:{'mem_total_bytes':128*a.g.GIB,'mem_available_bytes':64*a.g.GIB,'swap_used_bytes':0,'psi':{'some':0,'full':0}}
start=time.monotonic()
mode=sys.argv[3]
def disk(paths):
 free=(20 if mode=='disk-start' or (mode=='disk-kill' and time.monotonic()-start>.4) else 200)*a.g.GIB
 return free,{'fixture-storage':free}
a.g.disk_sample=disk
if mode=='pressure':
 a.g.snapshot=lambda:{'mem_total_bytes':128*a.g.GIB,'mem_available_bytes':64*a.g.GIB,'swap_used_bytes':0,'psi':{'some':0,'full':2 if time.monotonic()-start>.4 else 0}}
os.environ.update(HOME=sys.argv[2],SLURM_CLUSTER_NAME='acluster',SLURM_JOB_ID='123',SLURM_STEP_ID='0')
sys.argv=['guard','run','--timeout',sys.argv[4],'--log',sys.argv[2]+'/job.log','--cwd',sys.argv[2],'--',sys.executable,'-c',sys.argv[5]]
raise SystemExit(a.main())
'''
            command = [sys.executable, '-c', driver, str(GUARD), root, mode, str(timeout), child]
            if mode == 'signal':
                running = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                time.sleep(2.4)
                self.assertTrue(Path(root, 'job.progress.json').exists())
                running.send_signal(signal.SIGTERM)
                stdout, stderr = running.communicate(timeout=8)
                proc = subprocess.CompletedProcess(command, running.returncode, stdout, stderr)
            else:
                proc = subprocess.run(command, capture_output=True, text=True, timeout=12)
            receipt = Path(root, 'job.json')
            return proc, json.loads(receipt.read_text()) if receipt.exists() else None, Path(root, 'job.log').read_text() if Path(root, 'job.log').exists() else ''

    def test_real_affinity_exit(self):
        p, r, log = self.run_child('import os;print(len(os.sched_getaffinity(0)));raise SystemExit(7)')
        self.assertEqual(p.returncode, 7, p.stderr)
        self.assertEqual(log.strip(), '2')
        self.assertEqual(r['command_exit_code'], 7)

    def test_start_disk_refusal(self):
        p, r, log = self.run_child('raise RuntimeError("must never run")', 'disk-start')
        self.assertEqual(p.returncode, 96)
        self.assertIsNone(r)
        self.assertEqual(log, '')

    def test_runtime_pressure_disk(self):
        for mode, cause in [('pressure', 'memory-psi-full'), ('disk-kill', 'disk-free-below-50gib')]:
            p, r, log = self.run_child('import time;time.sleep(30)', mode, 10)
            self.assertEqual(p.returncode, 91, p.stderr)
            self.assertIn(cause, r['stop_cause'])
            self.assertEqual(r['live_child_pids_at_exit'], [])

    def test_signal_drain_and_progress(self):
        p, r, log = self.run_child('import time;time.sleep(30)', 'signal', 10)
        self.assertEqual(p.returncode, 143, p.stderr)
        self.assertEqual(r['live_child_pids_at_exit'], [])
        self.assertEqual(r['stop_cause'], ['signal-15'])

    def test_atomic_slot_contention(self):
        with tempfile.TemporaryDirectory() as root:
            a.g.LOCK_PATH = Path(root, 'slot')
            lock = a.g.acquire_slot()
            self.assertIsNotNone(lock)
            p = subprocess.run([sys.executable, '-c',
                'import fcntl,sys;f=open(sys.argv[1],"a+");fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB)',
                str(a.g.LOCK_PATH)], capture_output=True)
            self.assertNotEqual(p.returncode, 0)
            lock.close()
            fresh = a.g.acquire_slot()
            self.assertIsNotNone(fresh)
            fresh.close()

    def test_escaped_descendant(self):
        child = 'import os,time; p=os.fork();\nif p==0:\n os.setsid(); print(os.getpid(),flush=True);time.sleep(30)\n'
        p, r, log = self.run_child(child)
        self.assertEqual(p.returncode, 93, p.stderr)
        self.assertEqual(r['live_child_pids_at_exit'], [])
        pid = int(log.strip())
        try:
            state = Path('/proc', str(pid), 'stat').read_text().rsplit(')', 1)[1].split()[0]
        except FileNotFoundError:
            state = 'gone'
        self.assertIn(state, ('gone', 'Z'))


if __name__ == '__main__':
    unittest.main(verbosity=2)
