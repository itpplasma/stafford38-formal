#!/usr/bin/env bash
set -euo pipefail

CDPATH=
repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
repo_root=$(cd -- "$repo_root" && pwd)
tmp_root=$(mktemp -d "${TMPDIR:-/tmp}/palomar-comparator-behavior.XXXXXX")
trap 'status=$?; if [ "$status" -eq 0 ]; then rm -rf "$tmp_root"; else echo "Failed fixture retained at $tmp_root" >&2; fi' EXIT
mkdir -p "$tmp_root/scripts"
cp "$repo_root/scripts/check-palomar-policy.py" \
  "$repo_root/scripts/source_requirements.py" \
  "$repo_root/scripts/verification_errors.py" \
  "$repo_root/scripts/palomar-policy-LICENSE" \
  "$repo_root/scripts/bootstrap-palomar-tools.sh" \
  "$repo_root/scripts/run-palomar-comparator.sh" "$tmp_root/scripts/"

cat >"$tmp_root/lean-toolchain" <<'EOF'
leanprover/lean4:v4.35.0-rc3
EOF
cat >"$tmp_root/lakefile.toml" <<'EOF'
name = "palomarComparatorBehavior"
version = "0.1.0"
defaultTargets = ["Challenge", "Solution", "FixedSourceChallenge", "FixedSourceSolution", "AlternativeSolution", "AlternativeFixedSourceSolution"]

[[lean_lib]]
name = "Challenge"

[[lean_lib]]
name = "Solution"

[[lean_lib]]
name = "FixedSourceChallenge"

[[lean_lib]]
name = "FixedSourceSolution"

[[lean_lib]]
name = "AlternativeSolution"

[[lean_lib]]
name = "AlternativeFixedSourceSolution"
EOF
cat >"$tmp_root/Challenge.lean" <<'EOF'
module

@[expose] public section

namespace Stafford38Challenge

theorem universalStatement : True := by
  trivial

end Stafford38Challenge
EOF
cat >"$tmp_root/Solution.lean" <<'EOF'
module

@[expose] public section

namespace Stafford38Challenge

theorem universalStatement : True := by
  trivial

end Stafford38Challenge
EOF
cat >"$tmp_root/FixedSourceChallenge.lean" <<'EOF'
module

@[expose] public section

namespace Stafford38FixedSourceChallenge

theorem universalFixedSourceStatement : True := by
  trivial

end Stafford38FixedSourceChallenge
EOF
cat >"$tmp_root/FixedSourceSolution.lean" <<'EOF'
module

@[expose] public section

namespace Stafford38FixedSourceChallenge

theorem universalFixedSourceStatement : True := by
  trivial

end Stafford38FixedSourceChallenge
EOF
cp "$tmp_root/Solution.lean" "$tmp_root/AlternativeSolution.lean"
cp "$tmp_root/FixedSourceSolution.lean" "$tmp_root/AlternativeFixedSourceSolution.lean"
cat >"$tmp_root/comparator.json" <<'EOF'
{
  "challenge_module": "Challenge",
  "solution_module": "Solution",
  "theorem_names": ["Stafford38Challenge.universalStatement"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
cat >"$tmp_root/comparator-fixed-source.json" <<'EOF'
{
  "challenge_module": "FixedSourceChallenge",
  "solution_module": "FixedSourceSolution",
  "theorem_names": ["Stafford38FixedSourceChallenge.universalFixedSourceStatement"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
cat >"$tmp_root/comparator-alternative.json" <<'EOF'
{
  "challenge_module": "Challenge",
  "solution_module": "AlternativeSolution",
  "theorem_names": ["Stafford38Challenge.universalStatement"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF
cat >"$tmp_root/comparator-alternative-fixed-source.json" <<'EOF'
{
  "challenge_module": "FixedSourceChallenge",
  "solution_module": "AlternativeFixedSourceSolution",
  "theorem_names": ["Stafford38FixedSourceChallenge.universalFixedSourceStatement"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
}
EOF

(
  cd "$tmp_root"
  ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc3 lake update >setup.log 2>&1
  bash scripts/bootstrap-palomar-tools.sh >bootstrap.log 2>&1
  ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0-rc3 lake build Challenge Solution FixedSourceChallenge FixedSourceSolution AlternativeSolution AlternativeFixedSourceSolution >>setup.log 2>&1
  bash scripts/run-palomar-comparator.sh comparator.json .lake/verification/correct.log >correct-run.log 2>&1
  grep -Fq 'con-ron kernel accepts the solution' .lake/verification/correct.log
  grep -Fq 'nanoda kernel accepts the solution' .lake/verification/correct.log
  grep -Fq 'Lean default kernel accepts the solution' .lake/verification/correct.log
  grep -Fq 'Your solution is okay!' .lake/verification/correct.log

  cat >Solution.lean <<'EOF'
module

@[expose] public section

namespace Stafford38Challenge

theorem universalStatement : True ∧ True := by
  constructor <;> trivial

end Stafford38Challenge
EOF
  if bash scripts/run-palomar-comparator.sh comparator.json .lake/verification/wrong.log >wrong-run.log 2>&1; then
    echo "Comparator accepted a theorem with the wrong statement" >&2
    exit 1
  fi
  grep -Fq 'Challenge and solution theorem statement do not match' .lake/verification/wrong.log

  cat >Solution.lean <<'EOF'
module

@[expose] public section

namespace Stafford38Challenge

axiom rogue : False

theorem universalStatement : True := False.elim rogue

end Stafford38Challenge
EOF
  if bash scripts/run-palomar-comparator.sh comparator.json .lake/verification/axiom.log >axiom-run.log 2>&1; then
    echo "Comparator accepted a proof using an unpermitted axiom" >&2
    exit 1
  fi
  grep -Fq 'Illegal axiom detected' .lake/verification/axiom.log

  bash scripts/run-palomar-comparator.sh comparator-fixed-source.json .lake/verification/fixed-correct.log >fixed-correct-run.log 2>&1
  grep -Fq 'con-ron kernel accepts the solution' .lake/verification/fixed-correct.log
  grep -Fq 'nanoda kernel accepts the solution' .lake/verification/fixed-correct.log
  grep -Fq 'Lean default kernel accepts the solution' .lake/verification/fixed-correct.log
  grep -Fq 'Your solution is okay!' .lake/verification/fixed-correct.log

  bash scripts/run-palomar-comparator.sh comparator-alternative.json .lake/verification/alternative-correct.log >alternative-correct-run.log 2>&1
  grep -Fq 'Your solution is okay!' .lake/verification/alternative-correct.log
  bash scripts/run-palomar-comparator.sh comparator-alternative-fixed-source.json .lake/verification/alternative-fixed-correct.log >alternative-fixed-correct-run.log 2>&1
  grep -Fq 'Your solution is okay!' .lake/verification/alternative-fixed-correct.log

  cat >FixedSourceSolution.lean <<'EOF'
module

@[expose] public section

namespace Stafford38FixedSourceChallenge

theorem universalFixedSourceStatement : True ∧ True := by
  constructor <;> trivial

end Stafford38FixedSourceChallenge
EOF
  if bash scripts/run-palomar-comparator.sh comparator-fixed-source.json .lake/verification/fixed-wrong.log >fixed-wrong-run.log 2>&1; then
    echo "Comparator accepted a fixed-source theorem with the wrong statement" >&2
    exit 1
  fi
  grep -Fq 'Challenge and solution theorem statement do not match' .lake/verification/fixed-wrong.log
)

mkdir -p "$tmp_root/pin-guard/scripts"
cp "$repo_root/scripts/check-palomar-policy.py" \
  "$repo_root/scripts/source_requirements.py" \
  "$repo_root/scripts/verification_errors.py" \
  "$repo_root/scripts/palomar-policy-LICENSE" \
  "$tmp_root/pin-guard/scripts/"
cat >"$tmp_root/pin-guard/lean-toolchain" <<'EOF'
leanprover/lean4:v4.35.0-rc3
EOF
cat >"$tmp_root/pin-guard/lakefile.toml" <<'EOF'
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4"
rev = "c55e6e786f49471c72fbddbec5415808896aec1e"

[[require]]
name = "algebraicAnalysis"
git = "https://github.com/itpplasma/algebraic-analysis.git"
rev = "1111111111111111111111111111111111111111"
EOF
cat >"$tmp_root/pin-guard/lake-manifest.json" <<'EOF'
{"packages":[
 {"name":"mathlib","url":"https://github.com/leanprover-community/mathlib4","rev":"c55e6e786f49471c72fbddbec5415808896aec1e","inputRev":"c55e6e786f49471c72fbddbec5415808896aec1e"},
 {"name":"algebraicAnalysis","url":"https://github.com/itpplasma/algebraic-analysis.git","rev":"1111111111111111111111111111111111111111","inputRev":"1111111111111111111111111111111111111111"}
]}
EOF
if (cd "$tmp_root/pin-guard" && python3 scripts/check-palomar-policy.py >policy.log 2>&1); then
  echo "pin preflight accepted an unpinned AlgebraicAnalysis revision" >&2
  exit 1
fi
grep -Fq 'lakefile.toml does not pin the frozen AlgebraicAnalysis commit' "$tmp_root/pin-guard/policy.log"

receipt_dir="$repo_root/.lake/verification/palomar-behavior"
mkdir -p "$receipt_dir"
cp "$tmp_root/.lake/verification/"*.log "$receipt_dir/"
cp "$tmp_root/.lake/palomar-tools/revisions.txt" "$receipt_dir/tools.txt"
cp "$tmp_root/pin-guard/policy.log" "$receipt_dir/pin-rejection.log"
printf 'Palomar behavior oracle passed: main, fixed-source, and both alternative pairings accepted when matching, mismatches and an unpermitted proof axiom rejected, and an unfrozen AA pin fails closed.\n'
