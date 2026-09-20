# Third-party provenance and redistribution

The MEDS-derived code in implementations/legacy, implementations/official, and implementations/rectangular retains upstream GPL-3.0 licensing and notices. See LICENSE and source headers. The MEDS derivative trees retain their upstream GPL-3.0 terms and source notices. Licensing of the separate miniMEDS upstream source remains unresolved.

Historical AVX2 MEDS: https://github.com/IIS-summer-2023/meds-simd-lowlevel at commit 4ba53049dab9519a816ccc820f63edbc3c1bcff9.
Official MEDS: https://github.com/MEDSpqc/meds at commit 0ba7868bc060a1cda19af943ee0c7f8c25bf754e.
Rectangular MEDS reference: https://github.com/MeItsLars/MEDS-ARMv8-optimization-thesis at commit a072af947a98bf19cb10114d87f5f4a12018a823.

miniMEDS: https://github.com/IIS-ACE-lab/MiniMEDS at commit 4314054773d5d51ec764f95f4f19b1cd3e827dcf. The inspected repository contained no license file. This package excludes its third-party source and instead provides our source additions and a script to fetch and hash-verify it locally. Do not infer that the GPL license above applies to miniMEDS itself. miniMEDS paper: https://eprint.iacr.org/2026/1323, by Dinand Blom, Giuseppe Lamorgese, Ruben Niederhagen, Lars Ran, and Simona Samardjiska.

The Lean theorem uses Mathlib, pinned to commit db584cd6d46c92f209a44c0f1c829460d327499d. Mathlib is an external dependency and is not vendored here.
