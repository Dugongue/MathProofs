import EvenP15ScalarWordMeaning
import Mathproof.Meta.Problem18P37Isolation20261004

set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace EvenTI.P17Scalar

open EvenTI.Contract EvenTI.P12Scalar EvenTI.P15Scalar
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18P37Isolation20261004 (Iso Fresh iso Inv)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Run the literal matrix scalarity scanner inside a fresh namespace and
redirect its exact single-bit output to the host's private result array.
The host's real input and output tapes and other namespaces are preserved. -/
theorem isolatedScalarWords_run (D : FieldEncoding K)
    {d n W : ℕ} (M : Fin d → Matrix (Fin n) (Fin n) K) (payload : List ℕ)
    (hd : 0 < d) (hn : 0 < n) (hlen : payload.length=d*(n*n))
    (hDigits : ∀ a ∈ payload, a ≤ Fintype.card K)
    (hRows : ∀ (i : Fin d) (j k : Fin n),
      (d::n::payload).getD (2+i.val*(n*n)+(j.val*n+k.val)) 0 = (D (M i j k)).val)
    (I : Iso) (hI : Fresh I) (hRedirect : I.redirect=true) (s : Env)
    (hWords : (d::n::payload).length+Fintype.card K+(D 0).val+4 < W)
    (hZero : ∀ x, s.vars (I.ren x)=0)
    (hArrays : ∀ a, s.arrs (I.ren a) =
      List.replicate ((d::n::payload).length+1) 0)
    (hPin : s.vars I.pin=0)
    (hTape : ∃ junk, s.arrs I.tin=(d::n::payload).length::(d::n::payload)++junk)
    (hTapeLength : (s.arrs I.tin).length < W)
    (hTapeDigits : ∀ v ∈ s.arrs I.tin, v < W)
    (hPout : s.vars I.pout=0)
    (hResultLength : 1 ≤ (s.arrs I.tout).length)
    (hResultWord : (s.arrs I.tout).length < W) :
    ∃ t, Run W (iso I (scalarWordProgram (D 0).val)) s t
      (7*(120*(d::n::payload).length+80)) ∧
      t.vars I.pout=1 ∧
      (t.arrs I.tout).take 1 = [if rawScalarModes M then 1 else 0] ∧
      Mathproof.Problem18P37Isolation20261004.Frame I s t := by
  have hv : MatrixWords (Fintype.card K) (d::n::payload) :=
    ⟨d,n,payload,rfl,hd,hn,hlen,hDigits⟩
  obtain ⟨u,ru,hu⟩ := scalarWordProgram_run (D 0).val (Fintype.card K)
    (d::n::payload) hv hWords
  have hSpec := scalarWordSpec_eq_rawScalarModes D hn M payload hRows
  have huOut : u.out = [if rawScalarModes M then 1 else 0] := by
    rw [hu,hSpec]
    split <;> rfl
  have huLen : u.out.length=1 := by rw [huOut]; rfl
  obtain ⟨t,rt,ht,hFrame⟩ :=
    Mathproof.Problem18P37Isolation20261004.iso_run hI ru s [] (s.arrs I.tout)
      hZero hArrays hPin hTape hTapeLength hTapeDigits
      (fun hf => by rw [hRedirect] at hf; contradiction)
      (fun _ => by simpa using hPout)
      (fun _ => by simp)
      (fun _ => rfl)
      (fun _ => hResultWord)
      (fun _ => by simp)
      (fun _ => by simpa [huLen] using hResultLength)
  have hp := ht.outPtr hRedirect
  have hOut := ht.outArr hRedirect
  have hp' : t.vars I.pout=1 := by simpa [huLen] using hp
  exact ⟨t,rt,hp',by simpa [hp',huOut] using hOut,hFrame⟩

#print axioms isolatedScalarWords_run
end EvenTI.P17Scalar
