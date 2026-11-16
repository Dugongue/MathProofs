import Mathproof.MinimumGenerationPhysicalGreedyHeaderInstall
import Mathproof.MinimumGenerationPhysicalGreedyRegisters

namespace Mathproof.MinimumGeneration.PhysicalGreedyTemplateProgram

open SearchTransducer PhysicalGreedyHeader
open PhysicalGreedyHeaderInstall (wordAt outside_word)

set_option backward.isDefEq.respectTransparency false

variable {W : Nat}

structure Machine (W : Nat) where
  native : SearchTransducer
  width : native.workTapes = W

def Machine.banks (P : Machine W) : Fin P.native.workTapes ↪ Fin W :=
  (finCongr P.width).toEmbedding

def Machine.config (P : Machine W) (q : Fin P.native.states) (w : Nat)
    (v : Fin W → Nat) (p : Int) (o : List Bool) : P.native.Config :=
  ⟨q,p,fun _ => 0,fun i => wordAt w (v (P.banks i)),o⟩

def Machine.Run (P : Machine W) (raw prior : List Bool) (p : Int) (w : Nat)
    (old new : Fin W → Nat) : Prop :=
  ∃ (k : Nat) (q : Fin P.native.states),
    P.native.BoundedSegment raw (w+1) (P.config P.native.initialState w old p prior)
      (P.config q w new p prior) k ∧ P.native.step raw (P.config q w new p prior) = none

private theorem configEq {P : SearchTransducer} (a b : P.Config)
    (hq : a.state=b.state) (hi : a.inputHead=b.inputHead) (hh : a.workHead=b.workHead)
    (hc : a.workCell=b.workCell) (ho : a.outputReversed=b.outputReversed) : a=b := by
  cases a
  cases b
  simp_all

private theorem relocate_config (P : Machine W) (q : Fin P.native.states) (w : Nat)
    (v : Fin W → Nat) (p : Int) (o : List Bool) :
    P.native.bankConfig P.banks (P.config q w v p o) (fun _ => 0) (fun _ _ => none) =
      ⟨q,p,fun _ => 0,fun i => wordAt w (v i),o⟩ := by
  apply configEq
  · rfl
  · rfl
  · funext i
    obtain ⟨i,rfl⟩ := (finCongr P.width).surjective i
    exact P.native.bankConfig_head_image P.banks _ _ _ i
  · funext i
    obtain ⟨i,rfl⟩ := (finCongr P.width).surjective i
    exact P.native.bankConfig_cell_image P.banks _ _ _ i
  · rfl

def Machine.follow (P Q : Machine W) : Machine W :=
  ⟨thenMachine P.native Q.native P.banks Q.banks,rfl⟩

theorem Machine.Run.follow {P Q : Machine W} {raw prior : List Bool} {p : Int} {w : Nat}
    {x y z : Fin W → Nat} (first : P.Run raw prior p w x y) (second : Q.Run raw prior p w y z) :
    (P.follow Q).Run raw prior p w x z := by
  obtain ⟨a,i,r,h⟩ := first
  obtain ⟨b,j,s,k⟩ := second
  let N := P.follow Q
  let aa := P.native.bankConfig P.banks (P.config P.native.initialState w x p prior)
    (fun _ => 0) (fun _ _ => none)
  let ab := P.native.bankConfig P.banks (P.config i w y p prior) (fun _ => 0) (fun _ _ => none)
  let ba := Q.native.bankConfig Q.banks (Q.config Q.native.initialState w y p prior)
    (fun _ => 0) (fun _ _ => none)
  let bb := Q.native.bankConfig Q.banks (Q.config j w z p prior) (fun _ => 0) (fun _ _ => none)
  have ar := P.native.relocateBanks_segment P.banks r (heads := fun _ => 0)
    (cells := fun _ _ => none) (by simp)
  have br := Q.native.relocateBanks_segment Q.banks s (heads := fun _ => 0)
    (cells := fun _ _ => none) (by simp)
  have ah : (P.native.relocateBanks P.banks).step raw ab = none := by
    unfold ab
    rw [relocateBanks_step,h]
    rfl
  have bh : (Q.native.relocateBanks Q.banks).step raw bb = none := by
    unfold bb
    rw [relocateBanks_step,k]
    rfl
  have connect : thenEntry P.native Q.native P.banks Q.banks ab = ba := by
    unfold ab ba
    rw [relocate_config,relocate_config]
    rfl
  change (Q.native.relocateBanks Q.banks).BoundedSegment raw (w+1) ba bb b at br
  rw [← connect] at br
  have both := thenSegment P.native Q.native P.banks Q.banks ar ah br
  have begin : thenLeft P.native Q.native P.banks Q.banks aa = N.config N.native.initialState w x p prior := by
    unfold aa
    rw [relocate_config]
    rfl
  let sign := Fin.natAdd P.native.states j
  have finish : thenRight P.native Q.native P.banks Q.banks bb = N.config sign w z p prior := by
    unfold bb
    rw [relocate_config]
    rfl
  rw [begin,finish] at both
  refine ⟨_,sign,both,?_⟩
  rw [← finish]
  change (thenMachine P.native Q.native P.banks Q.banks).step raw _ = none
  rw [thenStep_right,bh]
  rfl

inductive Command (W : Nat)
  | copy (clock : Fin W) (source : Fin W → Option (Fin W))
  | increment (bank : Fin W)
  | add (banks : Fin 4 ↪ Fin W)

namespace Command

def machine : Command W → Machine W
  | .copy clock source => ⟨TapeInstall.machine clock source,rfl⟩
  | .increment bank => ⟨TapeArithmetic.machine bank .increment,rfl⟩
  | .add e => ⟨TapeAddition.machine.relocateBanks e,rfl⟩

def update (c : Command W) (old : Fin W → Nat) : Fin W → Nat :=
  match c with
  | .copy _ source => fun i => (source i).elim (old i) old
  | .increment i => Function.update old i (old i+1)
  | .add e => Function.update (Function.update old (e 0) (old (e 0)+old (e 1))) (e 2) 0

def safe (c : Command W) (w : Nat) (old : Fin W → Nat) : Prop :=
  match c with
  | .copy clock source => source clock = none
  | .increment _ => True
  | .add e => old (e 1) < 2^w ∧ old (e 3)=0

private theorem runCopy {raw prior : List Bool} {p : Int} {w : Nat} (old : Fin W → Nat)
    (clock : Fin W) (source : Fin W → Option (Fin W))
    (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length) (safe : source clock = none) :
    (machine (.copy clock source)).Run raw prior p w old (update (.copy clock source) old) := by
  let c := machine (.copy clock source)
  let cells := fun i : Fin W => wordAt w (old i)
  obtain ⟨r,h⟩ := TapeInstall.execute clock source safe raw (encodeLabel w (old clock))
    prior p cells rfl bounds
  rw [length_encodeLabel] at r h
  have layout : TapeInstall.installed source cells w =
      fun j => wordAt w (update (.copy clock source) old j) := by
    funext i
    cases hi : source i with
    | none =>
      exact (TapeInstall.installed_source _ _ _ _ hi).trans (by simp [cells,update,hi])
    | some j =>
      exact (TapeInstall.installed_exact _ _ _ _ _ hi (by
        intro p hp
        exact (outside_word w (old i) p hp).trans (outside_word w (old j) p hp).symm)).trans
        (by simp [cells,update,hi])
  have exit : TapeInstall.stop clock source p cells prior w =
      c.config (3 : Fin 4) w (update (.copy clock source) old) p prior :=
    configEq _ _ rfl rfl rfl layout rfl
  rw [exit] at r h
  exact ⟨_,(3 : Fin 4),r,h⟩

private theorem runIncrement {raw prior : List Bool} {p : Int} {w : Nat} (old : Fin W → Nat)
    (i : Fin W) (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length) :
    (machine (.increment i)).Run raw prior p w old (update (.increment i) old) := by
  let P := machine (.increment i)
  let a := P.config P.native.initialState w old p prior
  have park : PhysicalGreedyRegisters.Parked raw a := ⟨bounds.1,bounds.2,rfl⟩
  obtain ⟨d,r,stop,inp,head,data,out,frame⟩ := PhysicalGreedyRegisters.change i .increment
    a rfl park (old i) (by intro h; contradiction) rfl (le_refl (w+1))
  have same : d = P.config d.state w (update (.increment i) old) p prior := by
    apply configEq
    · rfl
    · exact inp
    · exact head
    · funext j
      by_cases hj : j=i
      · subst j
        simpa [P,machine,Machine.config,Machine.banks,update,PhysicalGreedyRegisters.nextValue,wordAt] using data
      · have eq : a.workCell j = wordAt w (old j) := rfl
        simpa [P,machine,Machine.config,Machine.banks,update,hj] using (frame j hj).trans eq
    · exact out
  rw [same] at r stop
  exact ⟨_,_,r,stop⟩

private theorem addFrame (P : SearchTransducer) (e : Fin P.workTapes ↪ Fin W)
    (c : P.Config) (w : Nat) (old new : Fin W → Nat) (q : Fin P.states) (p : Int)
    (prior : List Bool) (st : c.state=q) (hi : c.inputHead=p)
    (hh : c.workHead=(fun _ => 0)) (ho : c.outputReversed=prior)
    (owned : ∀ i, c.workCell i = wordAt w (new (e i)))
    (fixed : ∀ j ∉ Set.range e, old j = new j) :
    P.bankConfig e c (fun _ => 0) (fun j => wordAt w (old j)) =
      ⟨q,p,fun _ => 0,fun j => wordAt w (new j),prior⟩ := by
  apply configEq
  · exact st
  · exact hi
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      exact (P.bankConfig_head_image e c _ _ i).trans (congrFun hh i)
    · exact (P.bankConfig_frame e c _ _ hj).1
  · funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i,rfl⟩ := hj
      exact (P.bankConfig_cell_image e c _ _ i).trans (owned i)
    · exact (P.bankConfig_frame e c _ _ hj).2.trans (congrArg (wordAt w) (fixed j hj))
  · exact ho

private theorem runAdd {raw prior : List Bool} {p : Int} {w : Nat} (old : Fin W → Nat)
    (e : Fin 4 ↪ Fin W) (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length)
    (safe : (Command.add e).safe w old) :
    (machine (.add e)).Run raw prior p w old (update (.add e) old) := by
  let A := TapeAddition.machine
  let P := machine (.add e)
  let x := old (e 0)
  let y := old (e 1)
  let z := old (e 2)
  let new := update (.add e) old
  let a := TapeAddition.startConfig w x y z p prior
  let b := TapeAddition.stopConfig w (x+y) y p prior
  have zero : old (e 3) = 0 := safe.2
  have fit : y < 2^w := safe.1
  obtain ⟨r,stop⟩ := TapeAddition.executeAddition raw prior p w x y z bounds fit
  have run := A.relocateBanks_segment e r (heads := fun _ => 0) (cells := fun j => wordAt w (old j)) (by simp)
  have halt : P.native.step raw (A.bankConfig e b (fun _ => 0) (fun j => wordAt w (old j))) = none := by
    change (A.relocateBanks e).step raw _ = none
    rw [relocateBanks_step,stop]
    rfl
  have hs : A.bankConfig e a (fun _ => 0) (fun j => wordAt w (old j)) =
      P.config P.native.initialState w old p prior := by
    apply addFrame _ _ _ _ old old _ _ _ rfl rfl rfl rfl ?_ (fun _ _ => rfl)
    intro i
    fin_cases i <;> change TapeAddition.register w _ = _ <;> rw [register_work]
    · rfl
    · rfl
    · rfl
    · change wordAt w 0 = wordAt w (old (e 3))
      rw [zero]
  have he : A.bankConfig e b (fun _ => 0) (fun j => wordAt w (old j)) =
      P.config b.state w new p prior := by
    apply addFrame _ _ _ _ old new _ _ _ rfl rfl rfl rfl
    · intro i
      have key (a b : Fin 4) (ne : a ≠ b) : e a ≠ e b := fun h => ne (e.injective h)
      fin_cases i
      · change TapeAddition.register w (x+y) = wordAt w (new (e 0))
        rw [register_work]
        simp [wordAt,new,update,x,y,key 0 2 (by decide)]
      · change TapeAddition.register w y = wordAt w (new (e 1))
        rw [register_work]
        simp [wordAt,new,update,y,key 1 0 (by decide),key 1 2 (by decide)]
      · change TapeAddition.register w 0 = wordAt w (new (e 2))
        rw [register_work]
        simp [wordAt,new,update]
      · change TapeAddition.register w 0 = wordAt w (new (e 3))
        rw [register_work]
        simp [wordAt,new,update,zero,key 3 0 (by decide),key 3 2 (by decide)]
    · intro j hj
      have h0 : j ≠ e 0 := fun h => hj ⟨0,h.symm⟩
      have h2 : j ≠ e 2 := fun h => hj ⟨2,h.symm⟩
      simp [new,update,h0,h2]
  change P.native.BoundedSegment raw (w+1)
    (A.bankConfig e a (fun _ => 0) (fun j => wordAt w (old j)))
    (A.bankConfig e b (fun _ => 0) (fun j => wordAt w (old j))) _ at run
  rw [hs,he] at run
  rw [he] at halt
  exact ⟨_,b.state,run,halt⟩

theorem execute {raw prior : List Bool} {p : Int} {w : Nat} (c : Command W) (old : Fin W → Nat)
    (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length) (enabled : c.safe w old) :
    c.machine.Run raw prior p w old (c.update old) := by
  cases c with
  | copy clock source => exact runCopy old clock source bounds enabled
  | increment i => exact runIncrement old i bounds
  | add e => exact runAdd old e bounds enabled

end Command

private def stop (W : Nat) : Machine W :=
  ⟨⟨1,W,0,fun _ _ _ => none⟩,rfl⟩

def compile : List (Command W) → Machine W
  | [] => stop W
  | c::cs => c.machine.follow (compile cs)

def eval : List (Command W) → (Fin W → Nat) → Fin W → Nat
  | [], v => v
  | c::cs, v => eval cs (c.update v)

def safe (w : Nat) : List (Command W) → (Fin W → Nat) → Prop
  | [], _ => True
  | c::cs, v => c.safe w v ∧ safe w cs (c.update v)

theorem execute {raw prior : List Bool} {p : Int} {w : Nat}
    (bounds : (-1 : Int) ≤ p ∧ p ≤ raw.length)
    (commands : List (Command W)) (initial : Fin W → Nat) (enabled : safe w commands initial) :
    (compile commands).Run raw prior p w initial (eval commands initial) := by
  induction commands generalizing initial with
  | nil =>
    refine ⟨0,(0 : Fin 1),⟨rfl,?_⟩,rfl⟩
    intro k hk x hx
    have he : k=0 := by omega
    subst k
    change some _ = some x at hx
    cases hx
    exact ⟨bounds.1,bounds.2,by simp [Machine.config]⟩
  | cons c cs ih =>
    exact Machine.Run.follow (c.execute initial bounds enabled.1) (ih _ enabled.2)

end Mathproof.MinimumGeneration.PhysicalGreedyTemplateProgram
