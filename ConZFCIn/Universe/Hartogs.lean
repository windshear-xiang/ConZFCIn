import ConZFCIn.Universe.Embedding
import Vendor.ConZF.MixedHartogs

/-! The excluded-middle proofs from the pinned upstream `MixedHartogs.lean`,
generalized to an arbitrary common upper universe. -/
universe u v
namespace PSet.Multi

section
variable (a : PSet.{u}) (α f : PSet.{max u v + 1})

/-- The points of the lower carrier hit by the injection. -/
def pullS (x : a.Idx) : Prop := ∃ ξ, ξ ∈ α ∧ pair ξ (lift.{u,v+1} (a.Func x)) ∈ f

/-- The pulled-back order: the ordinals mapped to the points are members. -/
def pullR (x y : {x : a.Idx // pullS a α f x}) : Prop :=
  ∀ ξ ξ', pair ξ (lift.{u,v+1} (a.Func x.1)) ∈ f → pair ξ' (lift.{u,v+1} (a.Func y.1)) ∈ f → ξ ∈ ξ'

variable {a α f} (em : ∀ p : Prop, p ∨ ¬p) (hα : IsOrd α) (hf : IsInjRel α (lift.{u,v+1} a) f)
include em

/-- Under excluded middle, membership induction in the upper universe gives accessibility. -/
theorem pull_acc : ∀ ξ : PSet.{max u v + 1}, ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift.{u,v+1} (a.Func x.1)) ∈ f → Acc (pullR a α f) x := by
  haveI : ∀ x, Stable (Acc (pullR a α f) x) := fun _ => ⟨fun h => (em _).resolve_right h⟩
  refine mem_induction (P := fun ξ => ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift.{u,v+1} (a.Func x.1)) ∈ f → Acc (pullR a α f) x) fun ξ ih x hx => ?_
  refine ⟨x, fun y hy => ?_⟩
  obtain ⟨ζ, _, hζf⟩ := y.2
  exact ih ζ (hy ζ ξ hζf hx) y hζf

theorem pull_wf : WellFounded (pullR a α f) :=
  ⟨fun x => x.2.elim fun ξ h => pull_acc em ξ x h.2⟩

/-- The pullback as a well-founded certificate on the lower carrier. -/
def pullCode : WFCode a.Idx := ⟨pullS a α f, pullR a α f, pull_wf em⟩

include hα hf

/-- **Full predecessor coverage.** The lift.{u,v+1} of the lower collapse of a point is the upper
ordinal mapped to it. -/
theorem lift_tree : ∀ ξ : PSet.{max u v + 1}, ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift.{u,v+1} (a.Func x.1)) ∈ f → lift.{u,v+1} ((pullCode (α := α) (f := f) em).tree x) ≈ ξ := by
  refine mem_induction (P := fun ξ => ∀ x : {x : a.Idx // pullS a α f x},
    pair ξ (lift.{u,v+1} (a.Func x.1)) ∈ f → lift.{u,v+1} ((pullCode (α := α) (f := f) em).tree x) ≈ ξ)
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
    have hp' : pair w (lift.{u,v+1} (a.Func b)) ∈ f :=
      (mem_congr_left (pair_congr (Equiv.refl _) (ev.trans (lift_congr ez)))).1 hp
    let y : {x : a.Idx // pullS a α f x} := ⟨b, w, hwα, hp'⟩
    have hR : pullR a α f y x := fun ξ₁ ξ₂ h₁ h₂ =>
      (mem_congr_left (hf.inj w ξ₁ _ _ hp' h₁ (Equiv.refl _))).1
        ((mem_congr_right (hf.inj ξ ξ₂ _ _ hx h₂ (Equiv.refl _))).1 hw)
    exact mem_lift.2 (nn_intro ⟨_, (pullCode em).mem_tree.2 (nn_intro ⟨⟨y, hR⟩, Equiv.refl _⟩),
      (ih w hw y hp').symm⟩)

/-- **The mixed-universe Hartogs bound.** An upper ordinal with a set-coded injection into the
lift.{u,v+1} of a lower set `a` is below the lift.{u,v+1} of the lower bound `wfBound a.Idx`. -/
theorem mem_lift_wfBound : α ∈ lift.{u,v+1} (wfBound a.Idx) := by
  let c := pullCode (a := a) (α := α) (f := f) em
  have sub : ∀ ζ, ζ ∈ α → ζ ∈ lift.{u,v+1} c.height := by
    intro ζ hζ
    refine Stable.of_nn (hf.total ζ hζ) fun ⟨v, hv, hp⟩ => ?_
    refine Stable.of_nn (mem_lift.1 hv) fun ⟨z, hz, ev⟩ => Stable.of_nn hz fun ⟨b, ez⟩ => ?_
    have hp' : pair ζ (lift.{u,v+1} (a.Func b)) ∈ f :=
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
theorem K_initial (em : ∀ p : Prop, p ∨ ¬p) {δ f : PSet.{max u v + 1}} (hδ : δ ∈ K.{u,v+1})
    (hf : IsInjRel K.{u,v+1} δ f) : False := by
  refine Stable.of_nn (mem_K.1 hδ) fun ⟨η, hη, e⟩ => ?_
  have h := mem_lift_wfBound em isOrd_K (hf.congr_right e)
  exact not_mem_self K.{u,v+1} (isOrd_K.trans _ (lift_mem_K (isOrd_wfBound _)) _ h)


end PSet.Multi
