import Vendor.ConZF.Model
/-!
The seeded budget and the seeded model (con22 §2). For a supplied seed `b`, the budget
`seeded b` uses the label set `stdD (upair G b)`: the standard one around the pair of the
source and the seed. It is a `Budget`, contains the standard budget, and contains
`succ (rank b)` already at source `∅`. With the identity formula on that fixed domain every
nonzero ordinal `μ ≤ rank b` is reached from any of its elements (`reachable_of_le`), so every
ordinal up to `rank b` is hereditarily good and `b ∈ HG` for this budget (`hg_seed`). The
generic model theorem then gives, under the accessibility hypothesis (hence under irrefutable
excluded middle), an explicitly defined transitive class model of `ZF` containing `b`
(`hg_model_seeded`).
-/
universe u

namespace PSet

/-- The seeded label set. -/
def seededD (b G : PSet.{u}) : PSet.{u} := stdD (upair G b)

theorem rank_sub_rank_upair_left {G b : PSet.{u}} : ∀ z, z ∈ rank G → z ∈ rank (upair G b) :=
  fun _ hz => mem_rank'.2 (nn_intro ⟨G, mem_upair_left _ _, mem_succ_of_mem hz⟩)

theorem rank_upair_mono {G G' b : PSet.{u}} (h : ∀ z, z ∈ rank G → z ∈ rank G') :
    ∀ z, z ∈ rank (upair G b) → z ∈ rank (upair G' b) := by
  intro z hz
  refine Stable.of_nn (mem_rank'.1 hz) fun ⟨y, hy, hz⟩ => ?_
  refine Stable.of_nn (mem_upair.1 hy) fun
    | .inl e => ?_
    | .inr e => mem_rank'.2 (nn_intro ⟨b, mem_upair_right _ _,
        (mem_congr_right (succ_congr (rank_congr e))).1 hz⟩)
  refine mem_rank'.2 (nn_intro ⟨G', mem_upair_left _ _, ?_⟩)
  refine Stable.of_nn (mem_succ.1 ((mem_congr_right (succ_congr (rank_congr e))).1 hz)) fun
    | .inl hz => mem_succ_of_mem (h z hz)
    | .inr e' => (mem_congr_left e').2 ((isOrd_rank G).mem_succ_of_subset (isOrd_rank G') h)

/-- **The seeded budget.** -/
@[instance_reducible] def seeded (b : PSet.{u}) : Budget.{u} where
  D := seededD b
  congr e := stdD_congr (upair_congr e (Equiv.refl _))
  mono h := stdD_mono (rank_upair_mono (rank_mono_of_mem h))
  trans := stdD_trans
  self_mem G := stdD_trans (self_mem_stdD _) (mem_upair_left G b)
  omega_mem _ := omega_mem_stdD _
  upair_mem := upair_mem_stdD
  mem_of_subset hR h := stdD_mono rank_sub_rank_upair_left (mem_stdD_of_subset hR h)

/-- The seeded budget contains the standard one. -/
theorem std_sub_seeded {b G y : PSet.{u}} (h : y ∈ stdD G) : y ∈ seededD b G :=
  stdD_mono rank_sub_rank_upair_left h

/-- The seeded label set at `∅` is contained in every other one. -/
theorem seededD_empty_sub {b ν y : PSet.{u}} (h : y ∈ seededD b empty) : y ∈ seededD b ν :=
  stdD_mono (rank_upair_mono fun _ hz => (Stable.of_nn (mem_rank'.1 hz) fun ⟨w, hw, _⟩ =>
    (not_mem_empty w hw).elim)) h

/-- The successor of the rank of the seed lies in the seeded label set at `∅`. -/
theorem succ_rank_mem_seededD (b : PSet.{u}) : succ (rank b) ∈ seededD b empty := by
  have h1 : rank b ∈ rank (upair empty b) := rank_mem (mem_upair_right _ _)
  have h2 : ∀ z, z ∈ succ (rank b) → z ∈ rank (upair empty b) := fun z hz =>
    Stable.of_nn (mem_succ.1 hz) fun
      | .inl hz => (isOrd_rank _).trans _ h1 z hz
      | .inr e => (mem_congr_left e).2 h1
  refine mem_stdD_of_rank ((mem_congr_left (isOrd_rank b).succ.rank_equiv).2 ?_)
  refine mem_rank'.2 (nn_intro ⟨upair empty b, mem_upair_left _ _, ?_⟩)
  exact (isOrd_rank b).succ.mem_succ_of_subset (isOrd_rank _) h2

/-- **Identity-source reachability.** A nonzero ordinal `μ ≤ rank b` is reached from any of
its elements, by the identity on the fixed domain `succ (rank b)`. -/
theorem reachable_of_le (b : PSet.{u}) {μ ζ₀ : PSet.{u}} (hμ : IsOrd μ)
    (hle : μ ∈ succ (rank b)) (hζ₀ : ζ₀ ∈ μ) : Reachable (B := seeded b) ISat μ := by
  have hsub : ∀ ζ, ζ ∈ μ → ζ ∈ succ (rank b) := fun ζ hζ => Stable.of_nn (mem_succ.1 hle) fun
    | .inl h => mem_succ_of_mem ((isOrd_rank b).trans _ h ζ hζ)
    | .inr e => mem_succ_of_mem ((mem_congr_right e).1 hζ)
  have hV : ∀ {ζ : PSet.{u}}, ζ ∈ μ → ζ ∈ Vl μ := fun hζ =>
    (mem_Vl_ord hμ).2 ((mem_congr_left (hμ.mem hζ).rank_equiv).2 hζ)
  refine reachable_of (B := seeded b) (ψ := .eq 0 1) (m := 0) (e := fun _ => empty)
    (s := succ (rank b)) ⟨by decide, by decide⟩ hζ₀ (fun _ h => (Nat.not_lt_zero _ h).elim)
    (seededD_empty_sub (succ_rank_mem_seededD b)) (fun x y y' _ _ _ h1 h2 => h1.symm.trans h2)
    (fun ζ hζ => nn_intro ⟨ζ, ζ, hsub ζ hζ, hV hζ, hV hζ, Equiv.refl ζ, ?_⟩) hμ
  exact mem_succ_of_equiv (hμ.mem hζ).rank_equiv.symm

/-- Every ordinal up to `rank b` is hereditarily good for the seeded budget. -/
theorem cls_of_le (b : PSet.{u}) {μ : PSet.{u}} (hμ : IsOrd μ) (hle : μ ∈ succ (rank b)) :
    Cls (B := seeded b) ISat μ := by
  refine ⟨hμ, fun μ' hμ' ζ hζ => ?_⟩
  have hμ'o : IsOrd μ' := hμ.succ.mem hμ'
  have hle' : μ' ∈ succ (rank b) := Stable.of_nn (mem_succ.1 hμ') fun
    | .inl h => Stable.of_nn (mem_succ.1 hle) fun
      | .inl h' => mem_succ_of_mem ((isOrd_rank b).trans _ h' _ h)
      | .inr e => mem_succ_of_mem ((mem_congr_right e).1 h)
    | .inr e => (mem_congr_left e).2 hle
  exact reachable_of_le b hμ'o hle' hζ

/-- **The seed is in the seeded class.** -/
theorem hg_seed (b : PSet.{u}) : HG (B := seeded b) b :=
  cls_of_le b (isOrd_rank b) (self_mem_succ _)

/-- **The seeded model.** Under the accessibility hypothesis, the class `HG` of the seeded
budget is a transitive model of `ZF` containing `b`. -/
theorem hg_model_seeded (b : PSet.{u}) (hacc : AccHyp.{u}) :
    ZFModel (HG (B := seeded b)) ∧ HG (B := seeded b) b ∧
      ∀ x z, HG (B := seeded b) x → z ∈ x → HG (B := seeded b) z :=
  ⟨hg_model (B := seeded b) hacc, hg_seed b, fun _ _ hx hz => HG.mem (B := seeded b) hx hz⟩

/-- The seeded model from irrefutable excluded middle. -/
theorem hg_model_seeded_of_not_not_em (b : PSet.{u}) (h : ¬¬∀ p : Prop, p ∨ ¬p) :
    ZFModel (HG (B := seeded b)) ∧ HG (B := seeded b) b :=
  ⟨hg_model (B := seeded b) (accHyp_of_not_not_em h), hg_seed b⟩

/-- info: 'PSet.hg_model_seeded' does not depend on any axioms -/
#guard_msgs in #print axioms hg_model_seeded
/-- info: 'PSet.hg_model_seeded_of_not_not_em' does not depend on any axioms -/
#guard_msgs in #print axioms hg_model_seeded_of_not_not_em

end PSet
