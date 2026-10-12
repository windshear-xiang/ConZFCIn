import Vendor.ConZF.VLevel
/-!
Native bounds. A small type `C : Type u` of certificates with a decoder `δ : C → PSet.{u}`
gives an unconditional ordinal `natBound δ = rank (range δ)`, and every ordinal that is not not
dominated by some `δ c` belongs to it (`mem_natBound_of_dominated`). Nothing is selected: the
range collects the values decoded from every certificate, and the negative existential is used
only to prove the stable membership.

The certificates of interest are well-founded relations on a small carrier `X`, with their
proof of well-foundedness (`WFCode X : Type u`). The decoder builds the tree of a point by
`Acc`-recursion on the certificate, and the height of a code is the rank of the range of its
trees. This is the same mechanism as the materializing recursion (`Mat.lean`): large
elimination of `Acc`, here on certificates that are data of a small type, rather than an
accessibility hypothesis about the sets.
-/
universe u

namespace PSet

/-! ### The bound of a decoded family -/

section
variable {C : Type u} (δ : C → PSet.{u})

/-- The ordinal bounding the values of a decoder on a small type of certificates. -/
def natBound : PSet.{u} := rank (range δ)

theorem isOrd_natBound : IsOrd (natBound δ) := isOrd_rank _

theorem rank_mem_natBound (c : C) : rank (δ c) ∈ natBound δ := rank_mem (func_mem (range δ) c)

/-- `η` is not not included in the value of some certificate. -/
def Dominated (η : PSet.{u}) : Prop := ¬¬∃ c, ∀ z, z ∈ η → z ∈ δ c

instance {η : PSet.{u}} : Stable (Dominated δ η) := inferInstanceAs (Stable (¬_))

/-- A dominated ordinal is below the bound. -/
theorem mem_natBound_of_dominated {η : PSet.{u}} (hη : IsOrd η) (hδ : ∀ c, IsOrd (δ c))
    (h : Dominated δ η) : η ∈ natBound δ := by
  refine Stable.of_nn h fun ⟨c, hc⟩ => ?_
  have h2 : δ c ∈ natBound δ := (mem_congr_left (hδ c).rank_equiv).1 (rank_mem_natBound δ c)
  refine Stable.of_nn (mem_succ.1 (hη.mem_succ_of_subset (hδ c) hc)) fun
    | .inl h => (isOrd_natBound δ).trans _ h2 _ h
    | .inr e => (mem_congr_left e).2 h2

/-- Ranks of a family whose members are all dominated are all below the bound: the bound is
formed before any member is considered. -/
theorem rank_mem_natBound_of_dominated {A : PSet.{u} → PSet.{u} → Prop} (hδ : ∀ c, IsOrd (δ c))
    (h : ∀ x y, A x y → Dominated δ (rank y)) : ∀ x y, A x y → rank y ∈ natBound δ :=
  fun x y hxy => mem_natBound_of_dominated δ (isOrd_rank y) hδ (h x y hxy)

end

/-! ### Well-founded certificates on a small carrier -/

/-- A well-founded relation on a subset of a small carrier, with its certificate. The fields are
predicates and a proof, so the type of codes is small. -/
structure WFCode (X : Type u) : Type u where
  S : X → Prop
  R : {x : X // S x} → {x : X // S x} → Prop
  wf : WellFounded R

namespace WFCode
variable {X : Type u} (c : WFCode X)

/-- The tree of a point: its children are the trees of its predecessors. `Acc`-recursion with
motive `PSet`. -/
def treeAcc : (x : {x : X // c.S x}) → Acc c.R x → PSet.{u} :=
  fun _ acc => Acc.rec (motive := fun _ _ => PSet.{u})
    (fun x _ ih => ⟨{y : {x : X // c.S x} // c.R y x}, fun y => ih y.1 y.2⟩) acc

theorem treeAcc_eq (x : {x : X // c.S x}) (acc : Acc c.R x) :
    c.treeAcc x acc = ⟨{y : {x : X // c.S x} // c.R y x}, fun y => c.treeAcc y.1 (acc.inv y.2)⟩ := by
  cases acc; rfl

def tree (x : {x : X // c.S x}) : PSet.{u} := c.treeAcc x (c.wf.apply x)

theorem tree_eq (x : {x : X // c.S x}) :
    c.tree x = ⟨{y : {x : X // c.S x} // c.R y x}, fun y => c.tree y.1⟩ :=
  c.treeAcc_eq x _

/-- The height of a code: the rank of the range of its trees. -/
def height : PSet.{u} := rank (range c.tree)

theorem isOrd_height : IsOrd c.height := isOrd_rank _

end WFCode

/-- The bound decoded from all well-founded certificates on a carrier `X`. -/
def wfBound (X : Type u) : PSet.{u} := natBound (WFCode.height (X := X))

theorem isOrd_wfBound (X : Type u) : IsOrd (wfBound X) := isOrd_natBound _

theorem height_mem_wfBound {X : Type u} (c : WFCode X) : c.height ∈ wfBound X :=
  (mem_congr_left c.isOrd_height.rank_equiv).1 (rank_mem_natBound _ c)

theorem mem_wfBound_of_dominated {X : Type u} {η : PSet.{u}} (hη : IsOrd η)
    (h : Dominated (WFCode.height (X := X)) η) : η ∈ wfBound X :=
  mem_natBound_of_dominated _ hη WFCode.isOrd_height h

/-! ### A test: the natural numbers present `ω`

The usual order on `Nat` has a certificate, and the height of the resulting code is `ω`: the
tree of `n` has rank `ofNat n`. So `ω` is below the bound decoded from the certificates on
`ULift Nat`. This is a native presentation of `ω`; it does not give, and does not need,
accessibility of `ω` under membership. -/

theorem mem_ofNat_of_le {z : PSet.{u}} : ∀ {m n : Nat}, m ≤ n → z ∈ ofNat m → z ∈ ofNat n
  | _, 0, h, hz => Nat.le_zero.1 h ▸ hz
  | _, n+1, h, hz => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact mem_succ_of_mem (mem_ofNat_of_le (Nat.le_of_lt_succ h) hz)
    · exact h ▸ hz

theorem mem_ofNat {z : PSet.{u}} : ∀ {n : Nat}, z ∈ ofNat n ↔ ¬¬∃ m, m < n ∧ z ≈ ofNat m
  | 0 => ⟨fun h => (not_mem_empty z h).elim, fun h => Stable.of_nn h fun ⟨_, h, _⟩ =>
      (Nat.not_lt_zero _ h).elim⟩
  | n+1 => ⟨fun h => Stable.of_nn (mem_succ.1 h) fun
      | .inl h => nn_map (fun ⟨m, hm, e⟩ => ⟨m, Nat.lt_succ_of_lt hm, e⟩) (mem_ofNat.1 h)
      | .inr e => nn_intro ⟨n, Nat.lt_succ_self n, e⟩,
    fun h => Stable.of_nn h fun ⟨_, hm, e⟩ => mem_ofNat_of_le hm (mem_succ_of_equiv e)⟩

/-- The certificate of the order on the natural numbers. -/
def natCode : WFCode (ULift.{u} Nat) where
  S _ := True
  R a b := a.1.down < b.1.down
  wf := (measure fun p : Subtype fun _ : ULift.{u} Nat => True => p.1.down).wf

/-- The tree of `n` has rank `ofNat n`. -/
theorem rank_natCode_tree : ∀ (n : Nat) (x : {x : ULift.{u} Nat // natCode.S x}),
    x.1.down = n → rank (natCode.tree x) ≈ ofNat n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro x hx
    subst hx
    refine ext fun z => ?_
    rw [natCode.tree_eq]
    refine mem_rank.trans (Iff.trans ?_ mem_ofNat.symm)
    constructor
    · intro h
      refine nn_bind h fun ⟨⟨y, hy⟩, hz⟩ => ?_
      have hz' : z ∈ ofNat (y.1.down + 1) :=
        (mem_congr_right (succ_congr (ih y.1.down hy y rfl))).1 hz
      exact nn_map (fun ⟨m, hm, e⟩ => ⟨m, Nat.lt_of_le_of_lt (Nat.le_of_lt_succ hm) hy, e⟩)
        (mem_ofNat.1 hz')
    · exact nn_map fun ⟨m, hm, e⟩ => ⟨⟨⟨⟨m⟩, trivial⟩, hm⟩,
        (mem_congr_right (succ_congr (ih m hm ⟨⟨m⟩, trivial⟩ rfl))).2 (mem_succ_of_equiv e)⟩

theorem omega_subset_natCode_height : ∀ z, z ∈ omega.{u} → z ∈ natCode.height := fun _ hz =>
  Stable.of_nn (mem_omega.1 hz) fun ⟨n, e⟩ =>
    (mem_congr_left (e.trans (rank_natCode_tree n ⟨⟨n⟩, trivial⟩ rfl).symm)).2
      (rank_mem (func_mem (range natCode.tree) ⟨⟨n⟩, trivial⟩))

/-- `ω` is below the bound decoded from the certificates on `ULift Nat`. -/
theorem omega_mem_wfBound : omega.{u} ∈ wfBound (ULift.{u} Nat) :=
  mem_wfBound_of_dominated isOrd_omega (nn_intro ⟨natCode, omega_subset_natCode_height⟩)

/-- info: 'PSet.mem_natBound_of_dominated' does not depend on any axioms -/
#guard_msgs in #print axioms mem_natBound_of_dominated
/-- info: 'PSet.mem_wfBound_of_dominated' does not depend on any axioms -/
#guard_msgs in #print axioms mem_wfBound_of_dominated
/-- info: 'PSet.omega_mem_wfBound' does not depend on any axioms -/
#guard_msgs in #print axioms omega_mem_wfBound

end PSet
