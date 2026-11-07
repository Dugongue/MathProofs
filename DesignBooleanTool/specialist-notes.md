# Actual GAP DESIGN benchmark

## Runtime and provenance

The specialist backend is actual GAP 4.16.1 with Leonard H. Soicher's DESIGN package 1.8.2. The official Windows distribution was downloaded from the GAP GitHub release and checked against its published SHA-256:

- Release: https://github.com/gap-system/gap/releases/tag/v4.16.1
- Installer: `gap-4.16.1-x86_64.exe`, 820,472,871 bytes
- SHA-256: `b26346c3febb31f3e44600973207a37f50dd36c65cd22668264d55617b43081a`

The installer could not resolve the sandbox's Windows `localappdata` shell-folder constant. Its files were therefore extracted portably without registry or global PATH changes. Official innoextract 1.9 could not read the new installer format; the updated open-source Windows build from https://github.com/UserUnknownFactor/innoextract_win/releases/tag/670 read it successfully. No runtime or extraction utility is bundled with the tool.

GAP must be launched with `-A` here: this disables unrelated automatic package loading, including terminal-dependent packages. DESIGN is explicitly loaded and its real functions are called. This is not a Python emulation of DESIGN. The adapter supplies the separate mathematical reconstruction code that DESIGN does not provide as a built-in entry point.

## Full contract and timing

`benchmarks/gap_pipeline.g` implements a complete GAP-side pipeline:

1. Validate rectangular binary input and theorem shape.
2. Construct a real `BlockDesign` object and call `IsBinaryBlockDesign`, `IsSimpleBlockDesign`, and `PairwiseBalancedLambda`; check every block size.
3. Normalize compressed GF(2) columns and call GAP `SemiEchelonMat` for the rank test and coordinate reconstruction.
4. Recover a full truth table, bijective block coordinates and Walsh-support point coordinates.
5. Verify the exact Walsh transform, complete support/sign correspondence, every incidence identity, and full affine support span using `RankMat`.

Every timed repetition creates fresh design and representation objects; it does not reuse cached pair counts across repetitions. The input is already parsed as a native GAP integer matrix. GAP process startup, package loading and input-script parsing are excluded from the individual pipeline timers and separately included in a process-wall total. The wrapper uses GAP's nanosecond wall clock and reports repeated samples. It independently checks every positive certificate afterward using the separate Python reference verifier. This check is additional corroboration; the full GAP-side checker is already timed.

The benchmark is a comparison with these actual software calls and this explicitly written wrapper. It is not a claim that DESIGN contains a built-in plateaued-function reconstructor, nor that this wrapper is the fastest possible GAP program. In particular the package's `PairwiseBalancedLambda` calls its general `TSubsetStructure` machinery, whose generality can be expensive on dense designs.

## Reproduction

With a runnable GAP root containing `gap.exe` and DESIGN, run:

```console
python benchmarks/gap_baseline.py --gap-root GAP_ROOT --runtime-bin CYGWIN_BIN --repeats 5 --max-m 10 --output benchmarks/gap-results.json --timeout 600
```

The runtime-bin option is needed for the isolated Windows Cygwin runtime; use the relevant directory for your installation. Paths are intentionally absent from the report. `--max-m 7` runs only the eight shipped fixtures. Cases at m=8,9,10 are clearly labeled generated stress cases.

The specialist worker ran one-repeat smoke checks on all eight shipped fixtures. All expected outcomes agreed, including the two published positive functions, the published negative design and the proof's ordinary-rank collision counterexample; all positive certificates passed independent verification. These were smoke checks, not the final fair timing run. Final timings must be run serially after all background runtime extraction completes; the root worker owns that run.

## Independent theorem audit

The proposed optimization replacing explicit pair enumeration by a full reconstruction certificate is valid. Let N=2^m, S be the distinct Walsh support, and W_f(u)=A(-1)^g(u). For incidence I(u,x)=f(x)+u·x+g(u), the row sign sum is A. Two distinct rows have zero sign correlation by character orthogonality, so their intersection count is (N−2A)/4. Walsh inversion makes every column sign sum N/A, hence block size (|S|−N/A)/2. If two columns at x≠y were equal, all support frequencies would satisfy u·(x+y)=f(x)+f(y), contradicting full affine span. Thus complete certificate verification establishes all required simple-design conditions without assuming them. This is a sufficient certificate route with the same full contract.

## Licensing

GAP and DESIGN remain externally installed dependencies with their original licenses; DESIGN declares GPL-2.0-or-later. The adapter is original code that calls their public functions. No DESIGN implementation source or runtime binary is copied into the publication payload. Software authorship, version and the exact timing scope are preserved.


## Checkpointed runs and bounded case selection

`gap_streaming.py` preserves completed per-case certificates and timing samples in closed files, independently verifies positive certificates, and updates an aggregate report after each case. It emits warmup and per-repeat progress. If an overall timeout occurs, completed cases remain in the report with status `TIMEOUT`; incomplete-case samples remain explicitly unverified rather than being presented as a completed benchmark. `--resume` accepts a checkpoint only when the exact fixture, source and repetition contract matches.

For a bounded run, select exact IDs:

```console
python benchmarks/gap_streaming.py --gap-root GAP_ROOT --runtime-bin CYGWIN_BIN --max-m 10 --cases stress-quadratic-family-m10 --repeats 5 --timeout 600 --output benchmarks/gap-large.json
```

A subsequent identical command with `--resume` reuses completed cases. `--checkpoint-dir` chooses storage; `--prepare-only` writes the GAP script and contract without starting GAP. Existing nonempty checkpoints are never silently overwritten under a different contract. Runtime stdout/stderr logs stay in the checkpoint folder and are not part of the public benchmark report.

The transport layer has three tests using a fake subprocess rather than GAP, covering timeout preservation of a verified completed case, resumption of only pending cases, and rejection of changed contracts. These transport tests are distinct from actual GAP correctness/timing runs.
