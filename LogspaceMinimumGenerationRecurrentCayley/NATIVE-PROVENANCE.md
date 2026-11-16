# Native Reingold port provenance

- Checked with Lean v4.33.0 against Mathlib commit
  `db584cd6d46c92f209a44c0f1c829460d327499d`. The capsule imports Mathlib
  from that pin. It contains zero Mathlib sources.
- Complexitylib v0.2.0 October 29 snapshot
  (`cslib-community/cslib-frontier` commit
  `51c60ccb7f1e0143470b487cc059c0cb307db3c2`) supplies Reader, Reingold's
  rotation graph, and the resource compiler. The original package targets Lean
  v4.36.0-rc1. Its archive snapshot is the source recorded by the prior
  v4.33 Reader port's source manifest. The 40 modules selected by that earlier
  port were already checked against the cited revision after line-ending
  normalization. The current port hashes every actual staged source, including
  all further compatibility edits, separately.
- CSLib's 24 selected modules are based on `leanprover/cslib` revision
  `ee99dd30bd1a9f466c25a51b39a5cb0bfe4d2342` from the isolated rc2 audit.
  Its original source tarball SHA-256 is
  `e237903340b8bd4e8fe29a8e227986d41ad18261b1a0898f7bf01b22954261db`.
  The RepeatUntilBlank implementation, including its native state type and
  proof, comes from the October package's exact CSLib dependency
  `f4a472560f78c59bbedd795fe041ec507f7d0582`, adapted to v4.33. The latter
  archive SHA-256 is
  `dc8f998c17f4db56e792d649bbb2d695d194ef6ebdaa5bd42fb116ed6127ff21`.
  The official Git tree independently matched that archive's 400 blobs.
- Third-party code in the selected closure comprises 168 Complexitylib and
  24 CSLib modules, both Apache-2.0. Their existing source copyright headers
  and vendoring notes remain. Include `src/LICENSE-COMPLEXITY`,
  `src/NOTICE-COMPLEXITY`, and `src/LICENSE-CSLIB` in any distributed capsule.
  The NOTICE sections crediting Anthropic's ThreeSumApsp result identify
  modules outside this closure. Their source files do not enter the capsule.
  The NOTICE itself is preserved. No other external sources are copied.
- `native-closure-manifest.json` records the exact 192-module import closure
  in successful check order, including per-file source and object hashes and
  copy or adaptation status. The root `SpaceKernel.lean` retains only the
  original space proof's construction of the actual finite binary witness,
  with its upstream author Samuel Schlesinger credited. The machine library
  and source headers retain the original authors, including Christian
  Reitwiessner and other contributors.
- The three MathProof bridge modules are independently audited separately
  under `reports/native-{lowering,cayley,execution}-exact-audit.json` and
  their corresponding logs. The stages are isolated because CSLib uses the
  same module names as the older project revision. Import this port's CSLib
  and Complexity sources together in a pinned environment.
