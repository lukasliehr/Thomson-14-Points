#!/usr/bin/env bash
# Complete verification of the theorem, using only this repository.
# Usage: PYTHON=/path/to/python bash verify.sh [1-8 OpenMP threads]
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT"
VERIFY_PY=${PYTHON:-python3}
NT=${1:-4}
[[ "$NT" =~ ^[1-8]$ ]] || { echo 'Choose 1 through 8 threads'; exit 2; }
export OMP_NUM_THREADS="$NT" OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
export PYTHONDONTWRITEBYTECODE=1 PYTHONOPTIMIZE=0 TMAX=0.8 TYPING=PR
ulimit -v 8000000
C=Certificates/common
R=build/work/regen
mkdir -p build/logs build/bin "$R/local"
rm -f build/logs/FULL_PROOF_VERIFIED build/logs/audit_closure.txt
exec > >(tee build/logs/full_verification.txt) 2>&1
trap 'rc=$?; if ((rc != 0)); then echo "VERIFICATION FAILED (exit $rc); no proof-verification success is claimed."; fi' EXIT
echo 'Checking the source and certificate manifest...'
sha256sum --quiet -c SHA256SUMS
{
  uname -sm
  g++ --version | head -1
  "$VERIFY_PY" - <<'PY'
import sys, flint
assert sys.flags.optimize == 0, 'Python assertions must be enabled'
print(sys.version)
print('python-flint', flint.__version__)
PY
} > build/logs/environment.txt
cat build/logs/environment.txt
for stage in enclose_h audit_geometry audit_local audit_identity; do
  echo "Verifying $stage..."
  "$VERIFY_PY" "$C/$stage.py" > "build/logs/$stage.txt" 2>&1
  tail -1 "build/logs/$stage.txt"
done
echo 'Regenerating exact global root data...'
"$VERIFY_PY" "$C/make_case0.py" Certificates/Case0_separation_T0.8_D16/certificate.json 8 0.8 0.0459 "$R/case0" > build/logs/regen_case0.txt
"$VERIFY_PY" "$C/run_case1_ts_v2.py" Certificates/CaseI_a-0.98_D40/certificate.json 8 -0.98 "$R/case1" > build/logs/regen_case1.txt
"$VERIFY_PY" "$C/run_typed_ts.py" Certificates/Slab_m099_m098/certificate.json -0.99 -0.98 1 10 "$R/case2" > build/logs/regen_case2.txt
"$VERIFY_PY" "$C/make_cap_global4.py" Certificates/CaseIII_cap_D20/certificate.json 0.2 0.0095 1e-12 inf "$R/cap" > build/logs/regen_global.txt
echo 'Verifying and regenerating all 22 local node calculations...'
"$VERIFY_PY" "$C/prep_local3.py" Certificates/CaseIII_cap_D20/certificate.json 4e-14 0.01 0.0095 "$R/local" all > build/logs/regen_local.txt
echo 'Compiling the interval verifiers...'
for name in bnb_global4 bnb_local3; do
  g++ -O2 -fopenmp -ffp-contract=off -fno-fast-math -o "build/bin/$name" "$C/$name.cpp"
done
run() {
  local verifier=$1 problem=$2 roots=$3 label=$4
  echo "Verifying $label..."
  "build/bin/$verifier" "$problem" "$roots" > "build/logs/verified_$label.txt" 2> "build/logs/verified_$label.stderr"
  grep '^RESULT VERIFIED ' "build/logs/verified_$label.txt"
}
for name in pos close; do run bnb_global4 "$R/case0_${name}_ts.txt" "$R/case0_roots.txt" "case0_$name"; done
run bnb_global4 "$R/case1_ts.txt" "$R/case1_roots.txt" case1
for name in PPR PRR RRR; do run bnb_global4 "$R/case2_${name}_ts.txt" "$R/case2_${name}_roots.txt" "case2_$name"; done
for problem in "$R"/local/n*_ts.txt; do
  name=$(basename "$problem" _ts.txt)
  run bnb_local3 "$problem" "$R/local/${name}_roots.txt" "cap_$name"
done
for name in PPR PRR RRR; do run bnb_global4 "$R/cap_${name}_ts.txt" "$R/cap_${name}_roots.txt" "cap_global_$name"; done
echo 'Checking exact coverage, tube bounds and proof closure...'
"$VERIFY_PY" "$C/audit_closure.py" > build/logs/audit_closure.txt
cat build/logs/audit_closure.txt
printf 'FULL PROOF VERIFIED\n' > build/logs/FULL_PROOF_VERIFIED
echo 'FULL PROOF VERIFIED'
