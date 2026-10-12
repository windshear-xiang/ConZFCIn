import Vendor.ConZF.CofinalCut
import Vendor.ConZF.Pointwise
/-!
The model. The class `HG` of the sets of hereditarily good rank is a model of `ZF` provided the
output ranks of every admissible Replacement instance are bounded by an ordinal (`BoundHyp`, an
instancewise `¬¬∃ κ`). The bound is consumed by one Separation (`hg_replacement_of_rank_bound`).

Two producers of the bounds are given here, both through the materializing recursion. The
accessibility hypothesis `AccHyp` for the glued root gives the exact rank image, whose rank is a
bound (`boundHyp_of_accHyp`); `hg_model` and `con_ZF` keep their previous statements as
corollaries. Pointwise double-negated accessibility of the hereditarily good ordinals
(`PointwiseHGAcc`) gives the bound by separately guarded evaluations
(`boundHyp_of_pointwise`), with the quantifier outside the double negation.
-/
universe u

namespace PSet
variable [B : Budget.{u}]
open Fml

/-- The bound hypothesis: for every admissible Replacement instance over `HG`, the output ranks
are not not bounded by an ordinal. The double negation is inside the quantifiers over instances;
no bound is selected. -/
def BoundHyp : Prop :=
  ∀ (ψ : Fml) (e : Nat → PSet.{u}), (∀ i, HG (e i)) → ∀ a, HG a →
    (∀ x y y', x ∈ a → HG y → HG y' → Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y') →
    RankBounded ψ e a

/-- `HG` is a model of `ZF`, from the rank bounds alone. -/
theorem hg_model_of_bounds (hb : BoundHyp.{u}) : ZFModel HG.{u} := by
  refine ⟨fun hx hz => hx.mem hz, ?_, fun {x y} hx hy => ?_, fun {x} hx => ?_,
    fun {x} hx => ?_, ?_, fun P x hx => ?_, fun ψ e he a ha hf => ?_⟩
  · exact HG.of_bound cls_empty fun _ h => (not_mem_empty _ h).elim
  · exact HG.upair hx hy
  · exact HG.of_bound hx fun z hz => Stable.of_nn (mem_sUnion.1 hz) fun ⟨w, hw, hzw⟩ =>
      (isOrd_rank _).trans _ (rank_mem hw) _ (rank_mem hzw)
  · exact HG.of_bound (Cls.succ hx) fun z hz =>
      rank_mem_succ (isOrd_rank _) fun w hw => rank_mem (mem_powerset.1 hz w hw)
  · exact Cls.resp isOrd_omega.rank_equiv.symm cls_omega
  · exact HG.of_bound hx fun z hz => Stable.of_nn hz fun ⟨⟨i, _⟩, e⟩ =>
      rank_mem (nn_intro ⟨i, e⟩)
  -- Replacement: a bound gives the collecting set `Vl (rankCofinalCut ψ e a κ)`
  exact nn_bind (hb ψ e he a ha hf) fun ⟨κ, hk, hbound⟩ =>
    hg_replacement_of_rank_bound hk ha he hf hbound

omit [Budget.{u}] in
theorem con_ZF_of_bounds (hb : BoundHyp.{0}) : Con ZF := (hg_model_of_bounds hb).con

/-! ### Bounds from the materializing recursion -/

/-- The accessibility hypothesis: the root of a target assignment with the descent condition is
not not accessible. It follows from the well-foundedness of membership (`accHyp_of_mem_wf`), and
from the irrefutability of excluded middle. -/
def AccHyp : Prop :=
  ∀ τ : Path.{u} → PSet.{u} → Prop, Desc τ → ¬¬Acc (Rel τ) []

/-- Under `AccHyp` the recursion returns the exact image of the output ranks, whose rank is a
strict common bound. -/
theorem boundHyp_of_accHyp (hacc : AccHyp.{u}) : BoundHyp.{u} := by
  intro ψ e he a ha hf
  let φ : PSet.{u} → PSet.{u} → Prop := fun x η =>
    ¬¬∃ y, HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e)) ∧ η ≈ rank y
  have hrepl := (reach_rule ISat_resp a).replacement a rfl φ
    (fun ex eη => nn_map fun ⟨y, h1, h2, h3⟩ => ⟨y, h1,
      Sat.resp ψ (Env.cons_resp ex fun _ => Equiv.refl _) h2, eη.symm.trans h3⟩)
    (fun hx h h' => Stable.of_nn h fun ⟨y, h1, h2, h3⟩ => Stable.of_nn h' fun ⟨y', h1', h2', h3'⟩ =>
      h3.trans ((rank_congr (hf _ y y' hx h1 h1' h2 h2')).trans h3'.symm))
    (fun _ h => Stable.of_nn h fun ⟨y, h1, _, h3⟩ => Cls.resp h3.symm h1) (hacc _)
  refine nn_map (fun ⟨R, hR⟩ => ⟨rank R, isOrd_rank R, fun x y hx hy h => ?_⟩) hrepl
  exact (mem_congr_left (isOrd_rank y).rank_equiv).1
    (rank_mem ((hR (rank y)).2 (nn_intro ⟨x, hx, nn_intro ⟨y, hy, h, Equiv.refl _⟩⟩)))

theorem hg_model (hacc : AccHyp.{u}) : ZFModel HG.{u} := hg_model_of_bounds (boundHyp_of_accHyp hacc)

omit [Budget.{u}] in
/-- **The consistency of `ZF`**, from the accessibility hypothesis alone. -/
theorem con_ZF (hacc : AccHyp.{0}) : Con ZF := (hg_model hacc).con

omit [Budget.{u}] in
/-- The accessibility hypothesis follows from the well-foundedness of (stable) membership:
no paths, no rule, no formulas are involved in what is missing. -/
theorem accHyp_of_mem_wf (h : ¬¬∀ x : PSet.{u}, Acc (· ∈ ·) x) : AccHyp.{u} :=
  fun _ desc => nn_map (acc_root_of_desc desc) h

omit [Budget.{u}] in
/-- **`Con ZF` from the well-foundedness of membership on the sets-as-trees.** -/
theorem con_ZF_of_mem_wf (h : ¬¬∀ x : PSet.{0}, Acc (· ∈ ·) x) : Con ZF :=
  con_ZF (accHyp_of_mem_wf h)

omit [Budget.{u}] in
theorem accHyp_of_not_not_em (h : ¬¬∀ p : Prop, p ∨ ¬p) : AccHyp.{u} := fun τ desc hn =>
  h fun em => hn <| swf_root_of_desc desc (Acc (Rel τ))
    (fun p => ⟨fun hp => (em (Acc (Rel τ) p)).resolve_right hp⟩) fun x ih => ⟨x, ih⟩

omit [Budget.{u}] in
theorem con_ZF_of_not_not_em (h : ¬¬∀ p : Prop, p ∨ ¬p) : Con ZF :=
  con_ZF (accHyp_of_not_not_em h)

/-! ### Bounds from pointwise accessibility -/

/-- Every hereditarily good ordinal is not not accessible under membership. The quantifier is
outside the double negation. -/
def PointwiseHGAcc : Prop := ∀ η : PSet.{u}, Cls ISat η → ¬¬Acc (· ∈ ·) η

/-- The image of the output ranks from separately guarded evaluations; its rank is a bound. -/
theorem boundHyp_of_pointwise (hacc : PointwiseHGAcc.{u}) : BoundHyp.{u} := by
  intro ψ e he a ha hf
  let φ : PSet.{u} → PSet.{u} → Prop := fun x η =>
    ¬¬∃ y, HG y ∧ Sat HG ψ (Env.cons x (Env.cons y e)) ∧ η ≈ rank y
  have ⟨R, hR⟩ := (reach_rule ISat_resp a).replacement_pointwise a rfl φ
    (fun ex eη => nn_map fun ⟨y, h1, h2, h3⟩ => ⟨y, h1,
      Sat.resp ψ (Env.cons_resp ex fun _ => Equiv.refl _) h2, eη.symm.trans h3⟩)
    (fun hx h h' => Stable.of_nn h fun ⟨y, h1, h2, h3⟩ => Stable.of_nn h' fun ⟨y', h1', h2', h3'⟩ =>
      h3.trans ((rank_congr (hf _ y y' hx h1 h1' h2 h2')).trans h3'.symm))
    (fun _ h => Stable.of_nn h fun ⟨y, h1, _, h3⟩ => Cls.resp h3.symm h1) hacc
  refine nn_intro ⟨rank R, isOrd_rank R, fun x y hx hy h => ?_⟩
  exact (mem_congr_left (isOrd_rank y).rank_equiv).1
    (rank_mem ((hR (rank y)).2 (nn_intro ⟨x, hx, nn_intro ⟨y, hy, h, Equiv.refl _⟩⟩)))

theorem hg_model_of_pointwise (hacc : PointwiseHGAcc.{u}) : ZFModel HG.{u} :=
  hg_model_of_bounds (boundHyp_of_pointwise hacc)

omit [Budget.{u}] in
theorem con_ZF_of_pointwise (hacc : PointwiseHGAcc.{0}) : Con ZF :=
  (hg_model_of_pointwise hacc).con

omit [Budget.{u}] in
theorem con_ZF_of_pointwise_mem_acc (h : ∀ x : PSet.{0}, ¬¬Acc (· ∈ ·) x) : Con ZF :=
  con_ZF_of_pointwise fun η _ => h η

/-- info: 'PSet.con_ZF_of_bounds' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF_of_bounds
/-- info: 'PSet.con_ZF' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF
/-- info: 'PSet.con_ZF_of_pointwise' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZF_of_pointwise

end PSet
