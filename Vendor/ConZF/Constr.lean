import Vendor.ConZF.LHier
/-!
The guarded hierarchy interface and constructibility. The unguarded `lhistF` and `levelF` do not
force their index to be an ordinal (with `1 = {∅}` and the non-ordinal `a = {1}`, the rows
`1 ↦ ∅, a ↦ {∅}` satisfy the recurrence on `succ a`), so the exported formulas `ordLhistF` and
`ordLevelF` conjoin the ordinal formula, and their readings carry `IsOrd`.

Ordinal identification: the ordinal formula is exact over any transitive set structure (no pair
closure), so an ordinal `ξ` lies in `L_α` exactly when `ξ ∈ α`; hence `α ∈ L_{succ α}` and
`L_α ∈ L_{succ α}`. Levels are absolute between `SynZF` classes containing the index, since
`IsLHist` is class-independent and any two histories agree. Constructibility (`constrF`, `Bound 1`):
`x` lies in some ordinal level; the class `Constr M` is stable, respects `≈`, is transitive, and
contains every ordinal of `M`.
-/
universe u

namespace PSet
open Fml CardF LF

namespace LF

/-- Guarded history: `α` is an ordinal and `h` is a history on `α`. Variables `α = 0, h = 1`. -/
def ordLhistF : Fml := and (ordF 0) lhistF

/-- Guarded level: `α` is an ordinal and `A` is its level. Variables `α = 0, A = 1`. -/
def ordLevelF : Fml := and (ordF 0) levelF

/-- Constructibility: some ordinal level contains `x`. Variable `x = 0`. -/
def constrF : Fml :=
  ex (ex (and (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else k) ordLevelF) (mem 2 0)))

set_option maxRecDepth 200000 in
theorem bound_ordLhistF : Bound 2 ordLhistF := by decide

set_option maxRecDepth 200000 in
theorem bound_ordLevelF : Bound 2 ordLevelF := by decide

set_option maxRecDepth 200000 in
theorem bound_constrF : Bound 1 constrF := by decide

end LF

/-! ### The ordinal formula over a transitive set structure -/

section SetOrd
variable {A : PSet.{u}} (hA : Trans A) {e : Nat → PSet.{u}} (he : ∀ i, e i ∈ A)
include hA he

theorem sat_transF_set (x : Nat) : Sat (fun z => z ∈ A) (transF x) e ↔ Trans (e x) :=
  ⟨fun h y hy z hz => h y (hA _ (he x) y hy) z (hA _ (hA _ (he x) y hy) z hz) hz hy,
   fun h y _ z _ hz hy => h y hy z hz⟩

/-- The ordinal formula is exact over a transitive set; pair closure is not needed. -/
theorem sat_ordF_set (x : Nat) : Sat (fun z => z ∈ A) (ordF x) e ↔ IsOrd (e x) := by
  refine sat_and.trans ⟨fun ⟨h1, h2⟩ => ⟨(sat_transF_set hA he x).1 h1, fun y hy => ?_⟩,
    fun h => ⟨(sat_transF_set hA he x).2 h.trans, fun y hy hyx => ?_⟩⟩
  · exact (sat_transF_set hA (Env.cons_mem (hA _ (he x) y hy) he) 0).1 (h2 y (hA _ (he x) y hy) hy)
  · exact (sat_transF_set hA (Env.cons_mem hy he) 0).2 (h.mem_trans y hyx)

end SetOrd

/-- Ambient guarded level. -/
def OrdLevel (M : PSet.{u} → Prop) (α A : PSet.{u}) : Prop := IsOrd α ∧ SynZF.Level M α A

instance {M : PSet.{u} → Prop} {α A : PSet.{u}} : Stable (OrdLevel M α A) := inferInstanceAs (Stable (_ ∧ _))

/-- Ambient constructibility in the class `M`. -/
def Constr (M : PSet.{u} → Prop) (x : PSet.{u}) : Prop := ¬¬∃ α A, IsOrd α ∧ SynZF.Level M α A ∧ x ∈ A

instance {M : PSet.{u} → Prop} {x : PSet.{u}} : Stable (Constr M x) := inferInstanceAs (Stable (¬_))

theorem Constr.congr {M : PSet.{u} → Prop} {x x' : PSet.{u}} (e : x ≈ x') (h : Constr M x) : Constr M x' :=
  nn_map (fun ⟨α, A, hα, hA, hx⟩ => ⟨α, A, hα, hA, (mem_congr_left e).1 hx⟩) h

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- Both components of a level are in the class. -/
theorem level_mem_class {α A : PSet.{u}} (h : Level M α A) : M α ∧ M A :=
  have := hM.stable α
  have := hM.stable A
  Stable.of_nn h fun ⟨_, hh, _, hr⟩ => hM.toTransClass.of_pair_mem hh hr

theorem sat_ordLhistF {α h : PSet.{u}} {E : Nat → PSet.{u}} (hα : M α) (hh : M h) (hE : ∀ i, M (E i)) :
    Sat M ordLhistF (Env.cons α (Env.cons h E)) ↔ IsOrd α ∧ IsLHist α h :=
  sat_and.trans (and_congr (hM.toTransClass.sat_ordF (Env.cons_mem hα (Env.cons_mem hh hE)) 0) (hM.sat_lhistF hα hh hE))

/-- **The guarded level bridge.** -/
theorem sat_ordLevelF {α A : PSet.{u}} {E : Nat → PSet.{u}} (hα : M α) (hA : M A) (hE : ∀ i, M (E i)) :
    Sat M ordLevelF (Env.cons α (Env.cons A E)) ↔ OrdLevel M α A :=
  sat_and.trans (and_congr (hM.toTransClass.sat_ordF (Env.cons_mem hα (Env.cons_mem hA hE)) 0) (hM.sat_levelF hα hA hE))

/-! ### Ordinal identification -/

/-- An ordinal lies in `L_α` exactly when it lies in `α`. -/
theorem ord_mem_level : ∀ α : PSet.{u}, IsOrd α → M α → ∀ A, Level M α A → ∀ ξ, IsOrd ξ → (ξ ∈ A ↔ ξ ∈ α) := by
  refine mem_induction (P := fun α => IsOrd α → M α → ∀ A, Level M α A → ∀ ξ, IsOrd ξ → (ξ ∈ A ↔ ξ ∈ α))
    fun α ih hα hαM A hA ξ hξ => ?_
  constructor
  · intro hξA
    refine Stable.of_nn ((hM.level_rec hα hαM hA ξ).1 hξA) fun ⟨γ, hγ, k⟩ => Stable.of_nn k fun ⟨B, hB, hξB⟩ => ?_
    have hγo := hα.mem hγ
    have sub : ∀ η, η ∈ ξ → η ∈ γ := fun η hη =>
      (ih γ hγ hγo (hM.trans hαM hγ) B hB η (hξ.mem hη)).1 ((mem_defPow.1 hξB).subset η hη)
    refine Stable.of_nn (mem_succ.1 (hξ.mem_succ_of_subset hγo sub)) fun
      | .inl h => hα.trans γ hγ ξ h
      | .inr e => (mem_congr_left e).2 hγ
  · intro hξα
    have hξM := hM.trans hαM hξα
    refine Stable.of_nn (hM.level_exists hξ hξM) fun ⟨B, _, hB⟩ => ?_
    have htB := hM.level_trans hξ hξM hB
    have ihξ := ih ξ hξα hξ hξM B hB
    refine hM.defPow_level_sub hα hαM hξα hA hB ξ (mem_defPow.2 (nn_intro ⟨0, ordF 0, fun _ => ξ, by decide,
      fun _ h => (Nat.not_lt_zero _ h).elim, ext fun x => ?_⟩))
    refine ⟨fun hx => ?_, fun h => ?_⟩
    · have hxB := (ihξ x (hξ.mem hx)).2 hx
      exact mem_dval.2 ⟨hxB, (sat_ordF_set htB (Env.cons_mem hxB fun _ => hxB) 0).2 (hξ.mem hx)⟩
    · have ⟨hxB, hs⟩ := mem_dval.1 h
      exact (ihξ x ((sat_ordF_set htB (Env.cons_mem hxB fun _ => hxB) 0).1 hs)).1 hxB

/-- `α ∈ L_{succ α}`. -/
theorem ord_mem_succ_level {α A : PSet.{u}} (hα : IsOrd α) (hαM : M α) (hA : Level M (succ α) A) : α ∈ A :=
  (hM.ord_mem_level (succ α) hα.succ (hM.succ_mem hαM) A hA α hα).2 (self_mem_succ α)

/-- `L_α ∈ L_{succ α}`. -/
theorem level_mem_succ_level {α A B : PSet.{u}} (hα : IsOrd α) (hαM : M α) (hA : Level M (succ α) A) (hB : Level M α B) :
    B ∈ A :=
  hM.defPow_level_sub hα.succ (hM.succ_mem hαM) (self_mem_succ α) hA hB B (self_mem_defPow B)

/-! ### Comparison between classes -/

omit hM in
/-- Levels are absolute: a level in one class is the level in any other class containing the index. -/
theorem level_absolute {M' : PSet.{u} → Prop} (hM' : SynZF M') {α A : PSet.{u}} (hα : IsOrd α) (hαM' : M' α)
    (h : Level M α A) : Level M' α A := by
  refine Stable.of_nn h fun ⟨h, _, hl, hr⟩ => nn_bind (hM'.lhist_exists α hα hαM') fun ⟨h', hh', hl'⟩ => ?_
  refine nn_map (fun ⟨A', hr'⟩ => ⟨h', hh', hl', ?_⟩) (hl'.1.2.1 α (self_mem_succ α))
  exact (mem_congr_left (pair_congr (Equiv.refl _) (lhist_agree hα hα hl' hl α A' A hr' hr))).1 hr'

omit hM in
theorem ordLevel_absolute {M' : PSet.{u} → Prop} (hM' : SynZF M') {α A : PSet.{u}} (hαM' : M' α)
    (h : OrdLevel M α A) : OrdLevel M' α A :=
  ⟨h.1, level_absolute hM' h.1 hαM' h.2⟩

/-- The guarded level formula is absolute between classes containing its data. -/
theorem sat_ordLevelF_absolute {M' : PSet.{u} → Prop} (hM' : SynZF M') {α A : PSet.{u}} {E E' : Nat → PSet.{u}}
    (hα : M α) (hA : M A) (hE : ∀ i, M (E i)) (hα' : M' α) (hA' : M' A) (hE' : ∀ i, M' (E' i)) :
    Sat M ordLevelF (Env.cons α (Env.cons A E)) ↔ Sat M' ordLevelF (Env.cons α (Env.cons A E')) :=
  (hM.sat_ordLevelF hα hA hE).trans (Iff.trans ⟨ordLevel_absolute hM' hα', ordLevel_absolute hM hα⟩
    (hM'.sat_ordLevelF hα' hA' hE').symm)

/-! ### Constructibility -/

/-- **The constructibility bridge**: `Bound 1`, exact membership. -/
theorem sat_constrF {x : PSet.{u}} {E : Nat → PSet.{u}} (hx : M x) (hE : ∀ i, M (E i)) :
    Sat M constrF (Env.cons x E) ↔ Constr M x := by
  have key : ∀ α A, M α → M A → (Sat M (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else k) ordLevelF)
      (Env.cons A (Env.cons α (Env.cons x E))) ↔ OrdLevel M α A) := by
    intro α A hα hA
    refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_ordLevelF hα hA (E := Env.cons x E) (Env.cons_mem hx hE)))
    refine Sat.resp_iff (fun _ => Iff.rfl) _ fun i => ?_
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
  refine sat_ex.trans ⟨fun k => nn_bind k fun ⟨α, hα, s⟩ => nn_map (fun ⟨A, hA, s⟩ => ?_) (sat_ex.1 s),
    fun k => nn_map (fun ⟨α, A, hαo, hA, hxA⟩ => ?_) k⟩
  · have ⟨h1, h2⟩ := sat_and.1 s
    exact ⟨α, A, ((key α A hα hA).1 h1).1, ((key α A hα hA).1 h1).2, h2⟩
  · have ⟨hαM, hAM⟩ := hM.level_mem_class hA
    exact ⟨α, hαM, sat_ex.2 (nn_intro ⟨A, hAM, sat_and.2 ⟨(key α A hαM hAM).2 ⟨hαo, hA⟩, hxA⟩⟩)⟩

/-- Constructible sets are in the class. -/
theorem Constr.mem_class {x : PSet.{u}} (h : Constr M x) : M x :=
  have := hM.stable x
  Stable.of_nn h fun ⟨_, _, _, hA, hx⟩ => hM.trans (hM.level_mem_class hA).2 hx

/-- The constructible class is transitive. -/
theorem Constr.trans {x y : PSet.{u}} (h : Constr M x) (hy : y ∈ x) : Constr M y :=
  nn_map (fun ⟨α, A, hα, hA, hx⟩ => ⟨α, A, hα, hA, hM.level_trans hα (hM.level_mem_class hA).1 hA x hx y hy⟩) h

/-- Every ordinal of the class is constructible: `ξ ∈ L_{succ ξ}`. -/
theorem constr_of_ord {ξ : PSet.{u}} (hξ : IsOrd ξ) (hξM : M ξ) : Constr M ξ :=
  nn_map (fun ⟨A, _, hA⟩ => ⟨succ ξ, A, hξ.succ, hA, hM.ord_mem_succ_level hξ hξM hA⟩)
    (hM.level_exists hξ.succ (hM.succ_mem hξM))

/-- Levels themselves are constructible. -/
theorem constr_of_level {α A : PSet.{u}} (hα : IsOrd α) (hA : Level M α A) : Constr M A :=
  nn_map (fun ⟨B, _, hB⟩ => ⟨succ α, B, hα.succ, hB, hM.level_mem_succ_level hα (hM.level_mem_class hA).1 hB hA⟩)
    (hM.level_exists hα.succ (hM.succ_mem (hM.level_mem_class hA).1))

end SynZF

/-- info: 'PSet.SynZF.ord_mem_level' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.ord_mem_level
/-- info: 'PSet.SynZF.level_absolute' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.level_absolute
/-- info: 'PSet.SynZF.sat_constrF' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.sat_constrF
/-- info: 'PSet.SynZF.constr_of_ord' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.constr_of_ord

end PSet
