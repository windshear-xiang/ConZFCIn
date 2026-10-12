import Vendor.ConZF.Lift
import Vendor.ConZF.NativeBound
/-!
The mixed-universe Hartogs bound (con22 §1.3). For a lower set `a`, the lower ordinal
`wfBound a.Idx` (the bound decoded from all well-founded certificates on the carrier of `a`)
dominates every upper ordinal `α` with an upper set-coded injection into `lift a`
(`mem_lift_wfBound`), under excluded middle. The injection is pulled back to a relation on the
lower carrier whose fields mention the upper objects only in `Prop`; excluded middle turns
upper membership induction into accessibility of the pullback; and full predecessor coverage
identifies the lift of the lower collapse of a point with the original upper ordinal it is
mapped from (`lift_tree`), not merely with the order type of a range. Nothing chooses inverse
values: the injection is opened only inside propositional proofs.

Consequence: `K` is an initial ordinal of the upper universe, in that it has no set-coded
injection (even in the relational sense) into any of its members (`K_initial`).
-/
universe u

namespace PSet

/-- **The relational injection condition** from `α` into `X`: a set of pairs, total on `α`,
with inverse uniqueness. Functionality is not required, so this is weaker than an ordinary
injection and the bound below is correspondingly stronger; the adapter `IsInjFun.toRel` covers
ordinary set-coded injections. -/
structure IsInjRel (α X f : PSet.{u}) : Prop where
  total : ∀ ξ, ξ ∈ α → ¬¬∃ w, w ∈ X ∧ pair ξ w ∈ f
  inj : ∀ ξ ξ' w w', pair ξ w ∈ f → pair ξ' w' ∈ f → w ≈ w' → ξ ≈ ξ'

theorem IsInjRel.congr_right {α X X' f : PSet.{u}} (e : X ≈ X') (h : IsInjRel α X f) :
    IsInjRel α X' f :=
  ⟨fun ξ hξ => nn_map (fun ⟨w, hw, hp⟩ => ⟨w, (mem_congr_right e).1 hw, hp⟩) (h.total ξ hξ), h.inj⟩

theorem IsInjRel.mono {α X X' f : PSet.{u}} (h' : ∀ w, w ∈ X → w ∈ X') (h : IsInjRel α X f) :
    IsInjRel α X' f :=
  ⟨fun ξ hξ => nn_map (fun ⟨w, hw, hp⟩ => ⟨w, h' w hw, hp⟩) (h.total ξ hξ), h.inj⟩

/-- An ordinary set-coded injection: a total function on `α` into `X` with injective values. -/
structure IsInjFun (α X f : PSet.{u}) : Prop where
  dom : ∀ ξ w, pair ξ w ∈ f → ξ ∈ α ∧ w ∈ X
  func : ∀ ξ w w', pair ξ w ∈ f → pair ξ w' ∈ f → w ≈ w'
  total : ∀ ξ, ξ ∈ α → ¬¬∃ w, pair ξ w ∈ f
  inj : ∀ ξ ξ' w w', pair ξ w ∈ f → pair ξ' w' ∈ f → w ≈ w' → ξ ≈ ξ'

/-- An ordinary injection satisfies the relational condition. -/
theorem IsInjFun.toRel {α X f : PSet.{u}} (h : IsInjFun α X f) : IsInjRel α X f :=
  ⟨fun ξ hξ => nn_map (fun ⟨w, hp⟩ => ⟨w, (h.dom ξ w hp).2, hp⟩) (h.total ξ hξ), h.inj⟩

theorem WFCode.mem_tree {X : Type u} (c : WFCode X) {x : {x : X // c.S x}} {z : PSet.{u}} :
    z ∈ c.tree x ↔ ¬¬∃ y : {y : {x : X // c.S x} // c.R y x}, z ≈ c.tree y.1 := by
  rw [c.tree_eq x]; exact Iff.rfl

section
variable (a : PSet.{u}) (α f : PSet.{u+1})

/-- The points of the lower carrier hit by the injection. -/
def pullS (x : a.Idx) : Prop := ∃ ξ, ξ ∈ α ∧ pair ξ (lift (a.Func x)) ∈ f

/-- The pulled-back order: the ordinals mapped to the points are members. -/
def pullR (x y : {x : a.Idx // pullS a α f x}) : Prop :=
  ∀ ξ ξ', pair ξ (lift (a.Func x.1)) ∈ f → pair ξ' (lift (a.Func y.1)) ∈ f → ξ ∈ ξ'

variable {a α f} (em : ∀ p : Prop, p ∨ ¬p) (hα : IsOrd α) (hf : IsInjRel α (lift a) f)
include em

/-- Under excluded middle, membership induction in the upper universe gives accessibility. -/
theorem pull_acc : ∀ ξ : PSet.{u+1}, ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → Acc (pullR a α f) x := by
  haveI : ∀ x, Stable (Acc (pullR a α f) x) := fun _ => ⟨fun h => (em _).resolve_right h⟩
  refine mem_induction (P := fun ξ => ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → Acc (pullR a α f) x) fun ξ ih x hx => ?_
  refine ⟨x, fun y hy => ?_⟩
  obtain ⟨ζ, _, hζf⟩ := y.2
  exact ih ζ (hy ζ ξ hζf hx) y hζf

theorem pull_wf : WellFounded (pullR a α f) :=
  ⟨fun x => x.2.elim fun ξ h => pull_acc em ξ x h.2⟩

/-- The pullback as a well-founded certificate on the lower carrier. -/
def pullCode : WFCode a.Idx := ⟨pullS a α f, pullR a α f, pull_wf em⟩

include hα hf

/-- **Full predecessor coverage.** The lift of the lower collapse of a point is the upper
ordinal mapped to it. -/
theorem lift_tree : ∀ ξ : PSet.{u+1}, ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → lift ((pullCode (α := α) (f := f) em).tree x) ≈ ξ := by
  refine mem_induction (P := fun ξ => ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → lift ((pullCode (α := α) (f := f) em).tree x) ≈ ξ)
    fun ξ ih x hx => ?_
  have hξα : ξ ∈ α := x.2.elim fun ξ₀ h => (mem_congr_left (hf.inj ξ ξ₀ _ _ hx h.2 (Equiv.refl _))).2 h.1
  refine ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · refine Stable.of_nn (mem_lift.1 hw) fun ⟨z, hz, e⟩ => ?_
    refine Stable.of_nn ((pullCode em).mem_tree.1 hz) fun ⟨⟨y, hy⟩, e'⟩ => ?_
    obtain ⟨ζ, _, hζf⟩ := y.2
    have hζ : ζ ∈ ξ := hy ζ ξ hζf hx
    exact (mem_congr_left ((e.trans (lift_congr e')).trans (ih ζ hζ y hζf))).2 hζ
  · have hwα : w ∈ α := hα.trans ξ hξα w hw
    refine Stable.of_nn (hf.total w hwα) fun ⟨v, hv, hp⟩ => ?_
    refine Stable.of_nn (mem_lift.1 hv) fun ⟨z, hz, ev⟩ => Stable.of_nn hz fun ⟨b, ez⟩ => ?_
    have hp' : pair w (lift (a.Func b)) ∈ f :=
      (mem_congr_left (pair_congr (Equiv.refl _) (ev.trans (lift_congr ez)))).1 hp
    let y : {x : a.Idx // pullS a α f x} := ⟨b, w, hwα, hp'⟩
    have hR : pullR a α f y x := fun ξ₁ ξ₂ h₁ h₂ =>
      (mem_congr_left (hf.inj w ξ₁ _ _ hp' h₁ (Equiv.refl _))).1
        ((mem_congr_right (hf.inj ξ ξ₂ _ _ hx h₂ (Equiv.refl _))).1 hw)
    exact mem_lift.2 (nn_intro ⟨_, (pullCode em).mem_tree.2 (nn_intro ⟨⟨y, hR⟩, Equiv.refl _⟩),
      (ih w hw y hp').symm⟩)

/-- **The mixed-universe Hartogs bound.** An upper ordinal with a set-coded injection into the
lift of a lower set `a` is below the lift of the lower bound `wfBound a.Idx`. -/
theorem mem_lift_wfBound : α ∈ lift (wfBound a.Idx) := by
  let c := pullCode (a := a) (α := α) (f := f) em
  have sub : ∀ ζ, ζ ∈ α → ζ ∈ lift c.height := by
    intro ζ hζ
    refine Stable.of_nn (hf.total ζ hζ) fun ⟨v, hv, hp⟩ => ?_
    refine Stable.of_nn (mem_lift.1 hv) fun ⟨z, hz, ev⟩ => Stable.of_nn hz fun ⟨b, ez⟩ => ?_
    have hp' : pair ζ (lift (a.Func b)) ∈ f :=
      (mem_congr_left (pair_congr (Equiv.refl _) (ev.trans (lift_congr ez)))).1 hp
    let y : {x : a.Idx // pullS a α f x} := ⟨b, ζ, hζ, hp'⟩
    have e := lift_tree em hα hf ζ y hp'
    have ho : IsOrd (c.tree y) := isOrd_of_lift ((hα.mem hζ).resp e.symm)
    have hm : c.tree y ∈ c.height :=
      (mem_congr_left ho.rank_equiv).1 (rank_mem (func_mem (range c.tree) y))
    exact (mem_congr_left e).1 (lift_mem_of_mem hm)
  refine Stable.of_nn (hα.subset (isOrd_lift c.isOrd_height) sub) fun
    | .inl h => (isOrd_lift (isOrd_wfBound _)).trans _ (lift_mem_of_mem (height_mem_wfBound c)) α h
    | .inr e => (mem_congr_left e.symm).1 (lift_mem_of_mem (height_mem_wfBound c))

end

/-- **`K` is an initial ordinal**: it has no set-coded injection into any of its members. -/
theorem K_initial (em : ∀ p : Prop, p ∨ ¬p) {δ f : PSet.{u+1}} (hδ : δ ∈ K.{u})
    (hf : IsInjRel K.{u} δ f) : False := by
  refine Stable.of_nn (mem_K.1 hδ) fun ⟨η, hη, e⟩ => ?_
  have h := mem_lift_wfBound em isOrd_K (hf.congr_right e)
  exact not_mem_self K.{u} (isOrd_K.trans _ (lift_mem_K (isOrd_wfBound _)) _ h)

/-- info: 'PSet.mem_lift_wfBound' does not depend on any axioms -/
#guard_msgs in #print axioms mem_lift_wfBound
/-- info: 'PSet.K_initial' does not depend on any axioms -/
#guard_msgs in #print axioms K_initial

/-! ### The pullback from accessibility of the source ordinal (con33 §2) -/

section
variable {a : PSet.{u}} {α f : PSet.{u+1}}

/-- The pulled-back order is accessible below any accessible upper ordinal mapped to a point;
the existential in the carrier's guard is eliminated into the propositional `Acc` goal. -/
theorem pull_acc_of_acc : ∀ ξ : PSet.{u+1}, Acc (· ∈ ·) ξ → ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → Acc (pullR a α f) x := by
  intro ξ hξ
  induction hξ with
  | intro ξ _ ih =>
    intro x hx
    refine ⟨x, fun y hy => ?_⟩
    obtain ⟨ζ, _, hζf⟩ := y.2
    exact ih ζ (hy ζ ξ hζf hx) y hζf

theorem pull_wf_of_acc (hα : Acc (· ∈ ·) α) : WellFounded (pullR a α f) :=
  ⟨fun x => x.2.elim fun ξ h => pull_acc_of_acc ξ (hα.inv h.1) x h.2⟩

/-- The pullback as a well-founded certificate, from actual accessibility of the source. -/
def pullCodeAcc (hα : Acc (· ∈ ·) α) : WFCode a.Idx := ⟨pullS a α f, pullR a α f, pull_wf_of_acc hα⟩

variable (hacc : Acc (· ∈ ·) α) (hα : IsOrd α) (hf : IsInjRel α (lift a) f)
include hacc hα hf

theorem lift_tree_acc : ∀ ξ : PSet.{u+1}, ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → lift ((pullCodeAcc (a := a) (α := α) (f := f) hacc).tree x) ≈ ξ := by
  refine mem_induction (P := fun ξ => ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift (a.Func x.1)) ∈ f → lift ((pullCodeAcc (a := a) (α := α) (f := f) hacc).tree x) ≈ ξ)
    fun ξ ih x hx => ?_
  have hξα : ξ ∈ α := x.2.elim fun ξ₀ h => (mem_congr_left (hf.inj ξ ξ₀ _ _ hx h.2 (Equiv.refl _))).2 h.1
  refine ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · refine Stable.of_nn (mem_lift.1 hw) fun ⟨z, hz, e⟩ => ?_
    refine Stable.of_nn ((pullCodeAcc hacc).mem_tree.1 hz) fun ⟨⟨y, hy⟩, e'⟩ => ?_
    obtain ⟨ζ, _, hζf⟩ := y.2
    have hζ : ζ ∈ ξ := hy ζ ξ hζf hx
    exact (mem_congr_left ((e.trans (lift_congr e')).trans (ih ζ hζ y hζf))).2 hζ
  · have hwα : w ∈ α := hα.trans ξ hξα w hw
    refine Stable.of_nn (hf.total w hwα) fun ⟨v, hv, hp⟩ => ?_
    refine Stable.of_nn (mem_lift.1 hv) fun ⟨z, hz, ev⟩ => Stable.of_nn hz fun ⟨b, ez⟩ => ?_
    have hp' : pair w (lift (a.Func b)) ∈ f :=
      (mem_congr_left (pair_congr (Equiv.refl _) (ev.trans (lift_congr ez)))).1 hp
    let y : {x : a.Idx // pullS a α f x} := ⟨b, w, hwα, hp'⟩
    have hR : pullR a α f y x := fun ξ₁ ξ₂ h₁ h₂ =>
      (mem_congr_left (hf.inj w ξ₁ _ _ hp' h₁ (Equiv.refl _))).1
        ((mem_congr_right (hf.inj ξ ξ₂ _ _ hx h₂ (Equiv.refl _))).1 hw)
    exact mem_lift.2 (nn_intro ⟨_, (pullCodeAcc hacc).mem_tree.2 (nn_intro ⟨⟨y, hR⟩, Equiv.refl _⟩),
      (ih w hw y hp').symm⟩)

/-- **The mixed-universe Hartogs bound from accessibility of the source.** -/
theorem mem_lift_wfBound_of_acc : α ∈ lift (wfBound a.Idx) := by
  let c := pullCodeAcc (a := a) (α := α) (f := f) hacc
  have sub : ∀ ζ, ζ ∈ α → ζ ∈ lift c.height := by
    intro ζ hζ
    refine Stable.of_nn (hf.total ζ hζ) fun ⟨v, hv, hp⟩ => ?_
    refine Stable.of_nn (mem_lift.1 hv) fun ⟨z, hz, ev⟩ => Stable.of_nn hz fun ⟨b, ez⟩ => ?_
    have hp' : pair ζ (lift (a.Func b)) ∈ f :=
      (mem_congr_left (pair_congr (Equiv.refl _) (ev.trans (lift_congr ez)))).1 hp
    let y : {x : a.Idx // pullS a α f x} := ⟨b, ζ, hζ, hp'⟩
    have e := lift_tree_acc hacc hα hf ζ y hp'
    have ho : IsOrd (c.tree y) := isOrd_of_lift ((hα.mem hζ).resp e.symm)
    have hm : c.tree y ∈ c.height :=
      (mem_congr_left ho.rank_equiv).1 (rank_mem (func_mem (range c.tree) y))
    exact (mem_congr_left e).1 (lift_mem_of_mem hm)
  refine Stable.of_nn (hα.subset (isOrd_lift c.isOrd_height) sub) fun
    | .inl h => (isOrd_lift (isOrd_wfBound _)).trans _ (lift_mem_of_mem (height_mem_wfBound c)) α h
    | .inr e => (mem_congr_left e.symm).1 (lift_mem_of_mem (height_mem_wfBound c))

end

/-- The bound from negative accessibility, since its conclusion is stable. -/
theorem mem_lift_wfBound_of_nnacc {a : PSet.{u}} {α f : PSet.{u+1}} (hacc : ¬¬Acc (· ∈ ·) α) (hα : IsOrd α)
    (hf : IsInjRel α (lift a) f) : α ∈ lift (wfBound a.Idx) :=
  Stable.of_nn hacc fun h => mem_lift_wfBound_of_acc h hα hf

/-- **The localized height hypothesis**: negative accessibility of `K` in the upper universe. -/
def NNAccK : Prop := ¬¬Acc (fun a b : PSet.{u+1} => a ∈ b) K.{u}

/-- `K` has no relational injection into the lift of a lower set. -/
theorem not_injRel_K_lift (hK : NNAccK.{u}) (a : PSet.{u}) {f : PSet.{u+1}} (hf : IsInjRel K.{u} (lift a) f) : False :=
  not_mem_self K.{u} (isOrd_K.trans _ (lift_mem_K (isOrd_wfBound _)) _ (mem_lift_wfBound_of_nnacc hK isOrd_K hf))

/-- An upper ordinal injecting into the lift of a lower set is below `K`: otherwise `K` would
inject by restriction. -/
theorem mem_K_of_injRel (hK : NNAccK.{u}) {a : PSet.{u}} {θ f : PSet.{u+1}} (hθ : IsOrd θ) (hf : IsInjRel θ (lift a) f) : θ ∈ K.{u} := by
  refine Stable.of_nn (hθ.trichotomy isOrd_K) fun
    | .inl h => h
    | .inr (.inl e) => (not_injRel_K_lift hK a ⟨fun ξ hξ => hf.total ξ ((mem_congr_right e).2 hξ), hf.inj⟩).elim
    | .inr (.inr h) => (not_injRel_K_lift hK a ⟨fun ξ hξ => hf.total ξ (hθ.trans _ h ξ hξ), hf.inj⟩).elim

/-- `K` is initial from negative accessibility of `K`. -/
theorem K_initial_of_nnacc (hK : NNAccK.{u}) {δ f : PSet.{u+1}} (hδ : δ ∈ K.{u}) (hf : IsInjRel K.{u} δ f) : False :=
  Stable.of_nn (mem_K.1 hδ) fun ⟨η, _, e⟩ => not_injRel_K_lift hK η (hf.congr_right e)

/-- info: 'PSet.mem_lift_wfBound_of_acc' does not depend on any axioms -/
#guard_msgs in #print axioms mem_lift_wfBound_of_acc
/-- info: 'PSet.mem_K_of_injRel' does not depend on any axioms -/
#guard_msgs in #print axioms mem_K_of_injRel

end PSet
