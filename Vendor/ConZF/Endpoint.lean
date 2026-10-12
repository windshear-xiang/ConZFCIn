import Vendor.ConZF.ChoiceN
/-!
The pointwise-accessibility endpoint (conzf20, con33). The interval theorem no longer uses
excluded middle: negative accessibility of the height `K` of the lower universe, in the upper
universe (`NNAccK`), gives non-injectability of `K` into lifted lower sets by the accessibility
pullback, hence initiality and strong limitness; it gives lower membership accessibility
through the rank map, hence the interval regularity by the exact image of the definability
rule's Replacement; and the final split is by stability. Pointwise accessibility of the
hereditarily good ordinals of the seeded upper budget supplies both the syntactic class `MU` and
`NNAccK` (the seeded class contains its seed, whose rank is itself), so
`con_ZFCI_of_pointwise` derives the consistency of `ZFC + ∃ inaccessible` from that single
premise. Alternatively it suffices to supply the two ingredients separately: the syntactic class
from the upper accessibility hypothesis or from a bound producer, and `NNAccK`. Corollaries: from
double-negated well-foundedness of upper membership, from the upper accessibility hypothesis alone
(which already gives negative accessibility of `K`), from irrefutable excluded middle, and from
excluded middle. The reverse implication to pointwise accessibility is not established.
-/
universe u

namespace PSet

/-- Accessibility transfers along bisimulation. -/
theorem Acc.of_equiv {x y : PSet.{u}} (e : x ≈ y) (h : Acc (· ∈ ·) x) : Acc (· ∈ ·) y :=
  ⟨y, fun _ hz => h.inv ((mem_congr_right e).2 hz)⟩

/-- Pointwise accessibility of the seeded upper budget gives negative accessibility of `K`. -/
theorem nnAccK_of_pointwise (h : @PointwiseHGAcc.{u+1} (seeded K.{u})) : NNAccK.{u} :=
  nn_map (fun k => Acc.of_equiv isOrd_K.rank_equiv k) (h _ (hg_seed K.{u}))

/-- **Consistency from the seeded syntactic class and negative accessibility of `K`.** -/
theorem con_ZFCI_of_MU_nnacc (hMU : SynZF MU.{0}) (hK : NNAccK.{0}) : Con ZFCI :=
  con_ZFCI_of_nnacc hK (upperModel_NL hMU) (synZF_NL hMU).toTransClass (synZF_NL hMU).valid (valid_ac_NL hMU)

/-- **The pointwise endpoint**: consistency of `ZFC + ∃ inaccessible` from pointwise
accessibility of the hereditarily good ordinals of the seeded upper budget. -/
theorem con_ZFCI_of_pointwise (h : @PointwiseHGAcc.{1} (seeded K.{0})) : Con ZFCI :=
  con_ZFCI_of_MU_nnacc (synZF_MU_of_pointwise h) (nnAccK_of_pointwise h)

/-- From double-negated well-foundedness of membership in the upper universe. -/
theorem con_ZFCI_of_upper_mem_wf (h : ¬¬∀ x : PSet.{1}, Acc (· ∈ ·) x) : Con ZFCI :=
  con_ZFCI_of_pointwise fun η _ => nn_map (fun k => k η) h

/-- From the upper accessibility hypothesis together with negative accessibility of `K`. -/
theorem con_ZFCI_of_accHyp_nnacc (hacc : AccHyp.{1}) (hK : NNAccK.{0}) : Con ZFCI :=
  con_ZFCI_of_MU_nnacc (synZF_MU_of_acc hacc) hK

/-- From the upper accessibility hypothesis alone: it already gives negative accessibility of `K`. -/
theorem con_ZFCI_of_upper_accHyp (hacc : AccHyp.{1}) : Con ZFCI :=
  con_ZFCI_of_accHyp_nnacc hacc (not_not_acc_of_accHyp hacc K.{0})

/-- **The bound-producing route**: a bound producer for the seeded upper budget supplies the
syntactic class without any accessibility; negative accessibility of `K` is then the separate
remaining obligation. -/
theorem con_ZFCI_of_bounds_nnacc (hb : @BoundHyp.{1} (seeded K.{0})) (hK : NNAccK.{0}) : Con ZFCI :=
  con_ZFCI_of_MU_nnacc (SynZF.of_zfModel (hg_model_of_bounds (B := seeded K.{0}) hb)
    (fun x => inferInstanceAs (Stable (HG (B := seeded K.{0}) x))) fun e h => HG.resp (B := seeded K.{0}) e h) hK

/-- From irrefutable excluded middle, since consistency is negative. -/
theorem con_ZFCI_of_not_not_em (h : ¬¬∀ p : Prop, p ∨ ¬p) : Con ZFCI :=
  fun hp => h fun em => con_ZFCI_of_em em hp

/-- info: 'PSet.con_ZFCI_of_pointwise' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_pointwise
/-- info: 'PSet.con_ZFCI_of_upper_mem_wf' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_upper_mem_wf
/-- info: 'PSet.con_ZFCI_of_upper_accHyp' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_upper_accHyp
/-- info: 'PSet.con_ZFCI_of_bounds_nnacc' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_bounds_nnacc
/-- info: 'PSet.con_ZFCI_of_not_not_em' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_not_not_em

end PSet
