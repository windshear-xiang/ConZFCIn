import Vendor.ConZF.Model
/-!
Native ordinal bounding from an all-good interpreter (con22 §5). If every ordinal is
hereditarily good for an interpreter `I`, then under excluded middle the root of the tree glued
from the assignments of any functional ordinal-valued relation `φ` on a supplied source `s` is
accessible, and the value of the materializing recursion there is an actual ordinal
(`ordBound`) above every value of `φ` (`mem_ordBound_of`). The bound is a term built from the
source, the relation, and the proofs; nothing is extracted from a propositional existential.
The relation may mention arbitrary parameters, including from higher universes, inside `Prop`.
-/
universe u

namespace PSet

variable [B : Budget.{u}] {I : PSet.{u} → PSet.{u} → PSet.{u} → PSet.{u} → Prop}
  (I_resp : ∀ {η η' q q' x x' y y' : PSet.{u}},
    η ≈ η' → q ≈ q' → x ≈ x' → y ≈ y' → I η q x y → I η' q' x' y')
  (hall : ∀ η : PSet.{u}, IsOrd η → Cls I η)
  (em : ∀ p : Prop, p ∨ ¬p)
  (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop)
  (φ_resp : ∀ {x x' y y' : PSet.{u}}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
  (φ_func : ∀ {x y y' : PSet.{u}}, x ∈ s → φ x y → φ x y' → y ≈ y')
  (φ_ord : ∀ {x y : PSet.{u}}, x ∈ s → φ x y → IsOrd y)

/-- The glued assignment of the definability rule over the source. -/
abbrev glued : Path.{u} → PSet.{u} → Prop := Glue (Tr (rule I)) s φ

include I_resp hall em φ_resp φ_func φ_ord in
/-- Under excluded middle the glued root is accessible. -/
theorem glued_acc : Acc (Rel (glued (I := I) s φ)) [] :=
  have desc : Desc (glued (I := I) s φ) :=
    (glue_coherent (D := D) (fun η hη => (reach_rule I_resp s).coherent (η := η) hη)
      (fun e h => Rule.tr_resp_root e h) φ_resp φ_func fun hx h => hall _ (φ_ord hx h)).desc
  swf_root_of_desc desc (Acc _) (fun _ => ⟨fun hp => (em _).resolve_right hp⟩) fun x ih => ⟨x, ih⟩

/-- **The native bound**: the value of the materializing recursion at the glued root. -/
def ordBound : PSet.{u} :=
  F D s (Rel (glued (I := I) s φ)) [] (glued_acc I_resp hall em s φ φ_resp φ_func φ_ord)

theorem mem_ordBound (y : PSet.{u}) :
    y ∈ ordBound I_resp hall em s φ φ_resp φ_func φ_ord ↔ ¬¬∃ x η, x ∈ s ∧ φ x η ∧ y ∈ succ η :=
  mem_F_root (fun η hη => (reach_rule I_resp s).coherent (η := η) hη)
    (fun e h => Rule.tr_resp_root e h) φ_resp φ_func (fun hx h => hall _ (φ_ord hx h)) _ y

/-- Every value of `φ` is below the bound. -/
theorem mem_ordBound_of {x η : PSet.{u}} (hx : x ∈ s) (h : φ x η) :
    η ∈ ordBound I_resp hall em s φ φ_resp φ_func φ_ord :=
  (mem_ordBound I_resp hall em s φ φ_resp φ_func φ_ord η).2 (nn_intro ⟨x, η, hx, h, self_mem_succ η⟩)

/-- The bound is an ordinal. -/
theorem isOrd_ordBound : IsOrd (ordBound I_resp hall em s φ φ_resp φ_func φ_ord) := by
  have key : ∀ y, y ∈ ordBound I_resp hall em s φ φ_resp φ_func φ_ord → IsOrd y ∧
      ∀ z, z ∈ y → z ∈ ordBound I_resp hall em s φ φ_resp φ_func φ_ord := by
    intro y hy
    refine Stable.of_nn ((mem_ordBound I_resp hall em s φ φ_resp φ_func φ_ord y).1 hy)
      fun ⟨x, η, hx, hη, hyη⟩ => ?_
    have hηo := φ_ord hx hη
    refine Stable.of_nn (mem_succ.1 hyη) fun
      | .inl h => ⟨hηo.mem h, fun z hz => (mem_ordBound I_resp hall em s φ φ_resp φ_func φ_ord z).2
          (nn_intro ⟨x, η, hx, hη, mem_succ_of_mem (hηo.trans y h z hz)⟩)⟩
      | .inr e => ⟨hηo.resp e.symm, fun z hz => (mem_ordBound I_resp hall em s φ φ_resp φ_func φ_ord z).2
          (nn_intro ⟨x, η, hx, hη, mem_succ_of_mem ((mem_congr_right e).1 hz)⟩)⟩
  exact ⟨fun y hy z hz => (key y hy).2 z hz, fun y hy => (key y hy).1.trans⟩

/-- info: 'PSet.isOrd_ordBound' does not depend on any axioms -/
#guard_msgs in #print axioms isOrd_ordBound
/-- info: 'PSet.mem_ordBound_of' does not depend on any axioms -/
#guard_msgs in #print axioms mem_ordBound_of

end PSet
