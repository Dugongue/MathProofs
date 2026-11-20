import Mathlib.Tactic

/-!
# IMP automation: the `imp_simp` simp set

Registered in its own module because a simp attribute cannot be used in the module
that declares it. `IMPAutoCore20261004` and `IMPAutoTactics20261004` populate it, and
the tactics `imp_vcgen` and `imp_eval` run `simp only [imp_simp, …]`.
-/

register_simp_attr imp_simp
