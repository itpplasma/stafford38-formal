# Userspace curl runtime for the isolated bootstrap

Prepared 2026-10-03 after the bounded bootstrap jobs on acluster
21805716 and scluster 3108325 exited before the prerequisite proof build because `curl`
was absent from the compute-node PATH. The login hosts provide Debian 12
`/usr/bin/curl`; the root owns remote staging, job submission, monitoring, and
the resulting receipt.

`cluster-curl-bootstrap-20261003.py` stages only into
`<run>/bootstrap/curl-runtime`. It calls login-host `ldd` on the trusted curl
binary, copies its reported shared-library closure and ELF loader under their
runtime basenames, copies the Debian CA bundle, and writes a manifest with
source paths and SHA-256 hashes. It creates a local `curl` wrapper that sets
`CURL_CA_BUNDLE` and executes the copied loader with `--library-path` pointing
at the bundle. It refuses unresolved dependencies, an absent loader or CA
bundle, basename collisions, and an existing destination. It does not run
curl, alter system files, contact the network, or submit a job.

After review, the controller can run the staging script on the approved login
host, targeting the existing unique run tree. Inside a newly approved guarded
`srun` step, before `elan toolchain install` or `lake update`, set:

```sh
curl_runtime="$stafford_run/bootstrap/curl-runtime"
test -x "$curl_runtime/curl"
export CURL_CA_BUNDLE="$curl_runtime/ca-certificates.crt"
export PATH="$curl_runtime:$PATH"
"$curl_runtime/curl" --version | tee "$stafford_run/bootstrap/curl-version.log"
grep -Eq '^curl [0-9]' "$stafford_run/bootstrap/curl-version.log"
grep -Fq 'libcurl/' "$stafford_run/bootstrap/curl-version.log"
```

That allocation-local probe exercises the wrapper, bundled ELF loader, and
shared-library loading before the network bootstrap. The subsequent existing
bootstrap recipe remains responsible for checking the exact Lean and Lake
pins, manifest hash, and package revisions. Do not run the bundle or the
bootstrap on a login host. Do not use apt, system installation, a Mac, or a
protected host.

This is a retry recipe, not evidence that the staged runtime works on a
compute node. Accept it only after the new guarded allocation records the
`--version` probe and completes the existing pin checks. No existing script,
campaign state, verifier, or task ledger was changed for this repair.
