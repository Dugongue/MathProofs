# Reproduce the crossed-flattening benchmark

Run commands from the directory containing these scripts. The exact crossed solvers and the audit use the Python standard library. The run recorded here used Python 3.13.5 on a Windows machine with an Intel Core i7-10700F at 2.90 GHz. Cold runs launch a fresh Python interpreter for each path. Resident runs keep Python loaded and still read each pair file and verify every returned transporter. Use an otherwise idle machine when comparing timings.

## 1. Normalize the sources

Download the MatTen `crystal_elasticity_tensor.json` and the UCI Semeion ZIP from their respective releases. The normalizers verify the original archive hashes. The Sloane normalizer downloads the exact listed source files and emits a hash manifest. The normalized corpora and original publisher files are regenerated locally. [MatTen](https://doi.org/10.5281/zenodo.8190849) · [Semeion ZIP](https://archive.ics.uci.edu/static/public/178/semeion+handwritten+digit.zip) · [Sloane](https://neilsloane.com/oadir/index.html)

```powershell
python data_elasticity.py crystal_elasticity_tensor.json inputs
python data_semeion.py semeion.zip inputs
python data_sloane_oa.py inputs
```

These scripts create input objects with exact decimal strings over the rationals or a declared reduction to the binary field. The [data notes](data_sources.md) describe the axis order and each derived representation. The benchmark keeps the fields and views separate.

## 2. Exhaustive coverage

```powershell
$cohorts = @(
    'semeion-native', 'semeion-regrouped', 'data_elasticity_native-q',
    'data_elasticity_regrouped-q', 'data_elasticity_regrouped-f2', 'data_sloane_oa'
)
foreach ($name in $cohorts) {
    python run_benchmark.py coverage "inputs/$name.jsonl" "inputs/$name-coverage.jsonl"
}
python audit_results.py layouts inputs/semeion-native.jsonl inputs/semeion-regrouped.jsonl inputs/data_sloane_oa.jsonl
```

The coverage checker only uses a modular result over the rationals when it certifies two nonsingular cuts and scalar commutants. Other rational cases fall back to exact arithmetic. The independent source scan in `data_elasticity.py` uses integer elimination. The per-system counts are in [the elasticity ledger](data_elasticity_coverage.json). The all-layout scan reports the union over the 24 permutations, counting each publisher row once per corpus.

## 3. Pairs, engines and end-to-end timing

Install CaDiCaL and point `$Cadical` at its executable. Install the Z3 binding for the additional rational comparison. The measured engines reported CaDiCaL 2.1.2 and Z3 5.4.1. The direct Boolean and real encodings, plus the binary-seeded rational lifting baseline, are explained in [the comparator note](baseline_notes.md). [CaDiCaL releases](https://github.com/arminbiere/cadical/releases) · [Z3](https://github.com/Z3Prover/z3)

```powershell
python -m pip install z3-solver==5.4.1.0
New-Item -ItemType Directory -Force results | Out-Null
foreach ($name in $cohorts) {
    $covered = if ($name.StartsWith('semeion')) { 4 } else { 5 }
    python run_benchmark.py pairs "inputs/$name.jsonl" "inputs/$name-coverage.jsonl" "pairs/$name" --label $name --seed 191743 --unconditional 4 --covered $covered --negative 3
    python run_benchmark.py time "pairs/$name" "results/$name.jsonl" --cadical $Cadical --timeout 3 --rational-backend hensel
}
```

The pair generator separates unconditional positives, positives sampled from the accepted class, rank negatives, and same-rank negatives with a crossed-covariant trace certificate. A positive uses a planted invertible rebase of a published object. The independent negative and witness checks use exact arithmetic. Each solver input excludes the planted answer and matrices.

For a resident run add `--warm` and choose a separate result file. For rational input, append `--q-exact` to measure the accelerated integer-arithmetic implementation. To measure direct Z3 instead of Hensel lifting, pass `--rational-backend z3`. The timing budget was 3 seconds per baseline attempt, with an 11-second cold watchdog. The hybrid records an actual sequential run, invoking the baseline only if crossed flattening returns unknown. The reference baseline and hybrid are separate runs. Crossed-only wall time is the median of three runs per pair.

```powershell
$name = 'data_elasticity_regrouped-q'
python run_benchmark.py time "pairs/$name" "results/$name-fast-warm.jsonl" --cadical $Cadical --timeout 3 --rational-backend hensel --q-exact --warm
python run_benchmark.py time "pairs/$name" "results/$name-z3.jsonl" --cadical $Cadical --timeout 3 --rational-backend z3
python baseline_corank.py --timeout 2 --all-cuts pairs/semeion-native/semeion-native-004.json
python audit_results.py timings pairs results --corank baseline_corank_results.json
```

The timing audit replays the archived crossed and baseline witnesses and checks negative invariants separately. The replay is outside the recorded wall time. It supplements each solver's own verification, which is included in its reported duration. Results may differ with timing budgets and machine load. The published-data instances are fixed by the source hashes and pair-generation seed.
