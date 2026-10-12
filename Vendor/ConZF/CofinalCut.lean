import Vendor.ConZF.ModelBase
/-!
Cofinal cuts of a definable rank family. For an admissible Replacement instance over `HG` (a
domain `a`, parameters `e`, a formula `ψ` functional on `a`), `CoveredRank ψ e a ζ` says that
some actual output rank reaches `ζ`, and `rankCofinalCut ψ e a κ` is its cut at an ordinal cap
`κ`: one Separation, an unconditional term.

* `cls_rankCofinalCut`: every capped cut is hereditarily good, whether or not the cap is large
  enough. This is the endpoint argument of the model's Replacement clause, made available before
  any common bound is known.
* `hg_replacement_of_rank_bound`: a strict common ordinal bound on the output ranks gives the
  collecting set required by Replacement, namely `Vl (rankCofinalCut ψ e a κ)`. No materializing
  recursion and no accessibility proof appear.
* `RankBounded ψ e a`: the instancewise hypothesis, a double-negated existential bound.
* Stopping criteria: successor stationarity of the cut is exactly a strict common bound
  (`rankCofinalCut_successor_stationary_iff`); idempotence holds always and detects nothing.
* Failure of one bound forces every ordinal to be hereditarily good, so `HG` is the whole
  universe (`hg_universal_of_not_rankBounded`).
-/
universe u
namespace PSet
variable [B : Budget.{u}]
open Fml

/-- The downward closure of the successor ranks of actual outputs. -/
def CoveredRank (ψ : Fml) (e : Nat → PSet.{u}) (a ζ : PSet.{u}) : Prop :=
  ¬¬∃ x y, x ∈ a ∧ HG y ∧
    Sat HG ψ (Env.cons x (Env.cons y e)) ∧ ζ ∈ succ (rank y)

instance {ψ : Fml} {e : Nat → PSet.{u}} {a ζ : PSet.{u}} :
    Stable (CoveredRank ψ e a ζ) := inferInstanceAs (Stable (¬_))

/-- An unconditional set term, obtained by one Separation. -/
def rankCofinalCut (ψ : Fml) (e : Nat → PSet.{u}) (a κ : PSet.{u}) : PSet.{u} :=
  sep (CoveredRank ψ e a) κ

section
variable {ψ : Fml} {e : Nat → PSet.{u}} {a : PSet.{u}}

theorem coveredRank_resp {ζ ζ' : PSet.{u}} (h : ζ ≈ ζ') :
    CoveredRank ψ e a ζ → CoveredRank ψ e a ζ' :=
  nn_map fun ⟨x, y, hx, hy, hs, hz⟩ =>
    ⟨x, y, hx, hy, hs, (mem_congr_left h).1 hz⟩

theorem mem_rankCofinalCut {κ ζ : PSet.{u}} :
    ζ ∈ rankCofinalCut ψ e a κ ↔ ζ ∈ κ ∧ CoveredRank ψ e a ζ :=
  mem_sep fun _ _ h => coveredRank_resp h

theorem coveredRank_down {ζ z : PSet.{u}} (h : CoveredRank ψ e a ζ) (hz : z ∈ ζ) :
    CoveredRank ψ e a z :=
  nn_map (fun ⟨x, y, hx, hy, hs, hr⟩ =>
    ⟨x, y, hx, hy, hs, (isOrd_rank y).succ.trans ζ hr z hz⟩) h

theorem coveredRank_cls {ζ : PSet.{u}} (h : CoveredRank ψ e a ζ) : Cls ISat ζ :=
  Stable.of_nn h fun ⟨_, _, _, hy, _, hz⟩ =>
    Stable.of_nn (mem_succ.1 hz) fun
      | .inl hz => Cls.mem hy hz
      | .inr h => Cls.resp h.symm hy

theorem isOrd_rankCofinalCut {κ : PSet.{u}} (hk : IsOrd κ) :
    IsOrd (rankCofinalCut ψ e a κ) := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · have h := mem_rankCofinalCut.1 hy
    exact mem_rankCofinalCut.2 ⟨hk.trans y h.1 z hz, coveredRank_down h.2 hz⟩
  · exact hk.mem_trans y (mem_rankCofinalCut.1 hy).1

theorem cls_below_rankCofinalCut {κ μ : PSet.{u}}
    (h : μ ∈ rankCofinalCut ψ e a κ) : Cls ISat μ :=
  coveredRank_cls (mem_rankCofinalCut.1 h).2

/-- The new closure lemma. No common bound or accessibility assumption. -/
theorem cls_rankCofinalCut {κ : PSet.{u}} (hk : IsOrd κ)
    (ha : HG a) (he : ∀ i, HG (e i))
    (hf : ∀ x y y', x ∈ a → HG y → HG y' →
      Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :
    Cls ISat (rankCofinalCut ψ e a κ) := by
  let θ := rankCofinalCut ψ e a κ
  have hθo : IsOrd θ := isOrd_rankCofinalCut hk
  have below : ∀ μ, μ ∈ θ → Cls ISat μ :=
    fun _ h => cls_below_rankCofinalCut h
  have cover : ∀ ζ, ζ ∈ θ → CoveredRank ψ e a ζ :=
    fun _ h => (mem_rankCofinalCut.1 h).2
  have hgood : Good ISat θ := by
    refine Stable.by_cases (Good ISat θ) id fun hg ζ₀ hζ₀ => ?_
    have top : ∀ x, HG x ↔ x ∈ Vl θ := fun x => by
      refine ⟨fun hx => (mem_Vl_ord hθo).2 ?_,
        fun hx => below _ ((mem_Vl_ord hθo).1 hx)⟩
      refine Stable.of_nn (hx.1.trichotomy hθo) ?_
      rintro (h | h | h)
      · exact h
      · exact (hg (hx.good.resp ISat_resp h)).elim
      · exact (hg (hx.2 θ (mem_succ_of_mem h))).elim
    have sat : ∀ {E}, Sat HG ψ E ↔ Sat (· ∈ Vl θ) ψ E :=
      Sat.resp_iff top ψ fun _ => Equiv.refl _
    have ⟨m, hm⟩ := exists_bound ψ
    have hb : Bound (m+2) ψ := hm.mono (Nat.le_add_right m 2)
    have rθ : ∀ {z}, HG z → rank z ∈ θ :=
      fun hz => (mem_Vl_ord hθo).1 ((top _).1 hz)
    refine nn_bind (exists_upper hθo (rθ ha) m
      (fun i => rank (e i)) (fun i _ => rθ (he i)))
      fun ⟨ν, hν, h1, h2⟩ => ?_
    have hνo := hθo.mem hν
    refine reachable_of hb hν (fun i hi => mem_D_of_subset hνo (h2 i hi))
      (mem_D_of_subset hνo h1)
      (fun x y y' hx hy hy' s1 s2 => hf x y y' hx
        ((top y).2 hy) ((top y').2 hy') (sat.2 s1) (sat.2 s2))
      (fun ζ hζ => nn_map (fun ⟨x, y, hx, hy, hs, hζ⟩ =>
        ⟨x, y, hx, Vl_trans ((top a).1 ha) hx,
          (top y).1 hy, sat.1 hs, hζ⟩) (cover ζ hζ)) hθo
  exact ⟨hθo, fun μ hμ => Stable.of_nn (mem_succ.1 hμ) fun
    | .inl h => (below μ h).good
    | .inr h => hgood.resp ISat_resp h.symm⟩

/-- Being below the supplied cap places an actual output rank in the cut. -/
theorem rank_mem_rankCofinalCut {κ x y : PSet.{u}}
    (hx : x ∈ a) (hy : HG y)
    (hs : Sat HG ψ (Env.cons x (Env.cons y e))) (hr : rank y ∈ κ) :
    rank y ∈ rankCofinalCut ψ e a κ :=
  mem_rankCofinalCut.2 ⟨hr, nn_intro ⟨x, y, hx, hy, hs, self_mem_succ _⟩⟩

/-- A bound now feeds directly into the model's Replacement clause.
No exact rank image, materializer, or accessibility proof is constructed. -/
theorem hg_replacement_of_rank_bound {κ : PSet.{u}} (hk : IsOrd κ)
    (ha : HG a) (he : ∀ i, HG (e i))
    (hf : ∀ x y y', x ∈ a → HG y → HG y' →
      Sat HG ψ (Env.cons x (Env.cons y e)) →
      Sat HG ψ (Env.cons x (Env.cons y' e)) → y ≈ y')
    (hb : ∀ x y, x ∈ a → HG y →
      Sat HG ψ (Env.cons x (Env.cons y e)) → rank y ∈ κ) :
    ¬¬∃ b, HG b ∧ ∀ x y, x ∈ a → HG y →
      Sat HG ψ (Env.cons x (Env.cons y e)) → y ∈ b := by
  let θ := rankCofinalCut ψ e a κ
  have hθ : Cls ISat θ := cls_rankCofinalCut hk ha he hf
  exact nn_intro ⟨Vl θ,
    HG.of_bound hθ (fun z hz => (mem_Vl_ord hθ.1).1 hz),
    fun x y hx hy hs => (mem_Vl_ord hθ.1).2
      (rank_mem_rankCofinalCut hx hy hs (hb x y hx hy hs))⟩

/-- Negative ordinal boundedness for this family. -/
def RankBounded (ψ : Fml) (e : Nat → PSet.{u}) (a : PSet.{u}) : Prop :=
  ¬¬∃ κ, IsOrd κ ∧ ∀ x y, x ∈ a → HG y →
    Sat HG ψ (Env.cons x (Env.cons y e)) → rank y ∈ κ

instance : Stable (RankBounded ψ e a) := inferInstanceAs (Stable (¬_))

/-- Outputs contained in a fixed set are rank bounded, by the rank of that set. -/
theorem rankBounded_of_mem {K : PSet.{u}}
    (h : ∀ x y, x ∈ a → HG y → Sat HG ψ (Env.cons x (Env.cons y e)) → y ∈ K) :
    RankBounded ψ e a :=
  nn_intro ⟨rank K, isOrd_rank K, fun x y hx hy hs => rank_mem (h x y hx hy hs)⟩

/-- Noncoverage at one ordinal is exactly a strict common bound. -/
theorem not_coveredRank_iff {κ : PSet.{u}} (hk : IsOrd κ) :
    (¬ CoveredRank ψ e a κ) ↔
      ∀ x y, x ∈ a → HG y →
        Sat HG ψ (Env.cons x (Env.cons y e)) → rank y ∈ κ := by
  constructor
  · intro hn x y hx hy hs
    refine Stable.of_nn ((isOrd_rank y).trichotomy hk) ?_
    rintro (hr | h | hr)
    · exact hr
    · exact (hn (nn_intro ⟨x, y, hx, hy, hs,
        (mem_congr_left h).1 (self_mem_succ _)⟩)).elim
    · exact (hn (nn_intro ⟨x, y, hx, hy, hs, mem_succ_of_mem hr⟩)).elim
  · intro hb hc
    refine Stable.of_nn hc fun ⟨x, y, hx, hy, hs, hr⟩ => ?_
    have h := hb x y hx hy hs
    refine Stable.of_nn (mem_succ.1 hr) ?_
    rintro (hr | hr)
    · exact not_mem_self κ (hk.trans _ h _ hr)
    · exact not_mem_self κ ((mem_congr_left hr).2 h)

/-- Failure of one bound implies coverage at every ambient ordinal. -/
theorem coverage_of_not_rankBounded (h : ¬ RankBounded ψ e a)
    {κ : PSet.{u}} (hk : IsOrd κ) : CoveredRank ψ e a κ := by
  refine Stable.dne fun hn => ?_
  exact h (nn_intro ⟨κ, hk, (not_coveredRank_iff hk).1 hn⟩)

/-- Thus the unresolved case has every ambient ordinal hereditarily good. -/
theorem all_cls_of_not_rankBounded (h : ¬ RankBounded ψ e a) :
    ∀ κ : PSet.{u}, IsOrd κ → Cls ISat κ :=
  fun _ hk => coveredRank_cls (coverage_of_not_rankBounded h hk)

/-- An explicit ordinal outside Cls bounds every such rank family. -/
theorem rank_bound_of_not_cls {κ : PSet.{u}} (hk : IsOrd κ)
    (hn : ¬ Cls ISat κ) :
    ∀ x y, x ∈ a → HG y →
      Sat HG ψ (Env.cons x (Env.cons y e)) → rank y ∈ κ :=
  (not_coveredRank_iff hk).1 (fun hc => hn (coveredRank_cls hc))

/-- Equality at two successive caps, not idempotence, detects no overflow. -/
theorem rankCofinalCut_successor_stationary_iff {κ : PSet.{u}} :
    (rankCofinalCut ψ e a (succ κ) ≈ rankCofinalCut ψ e a κ) ↔
      ¬ CoveredRank ψ e a κ := by
  constructor
  · intro h hc
    have hm : κ ∈ rankCofinalCut ψ e a (succ κ) :=
      mem_rankCofinalCut.2 ⟨self_mem_succ _, hc⟩
    exact not_mem_self κ (mem_rankCofinalCut.1 ((mem_congr_right h).1 hm)).1
  · intro hn
    refine ext fun z => ?_
    constructor
    · intro hz
      have h := mem_rankCofinalCut.1 hz
      refine mem_rankCofinalCut.2 ⟨?_, h.2⟩
      refine Stable.of_nn (mem_succ.1 h.1) ?_
      rintro (hz | hz)
      · exact hz
      · exact (hn (coveredRank_resp hz h.2)).elim
    · intro hz
      have h := mem_rankCofinalCut.1 hz
      exact mem_rankCofinalCut.2 ⟨mem_succ_of_mem h.1, h.2⟩

/-- Idempotence is automatic and is NOT a no-overflow criterion. -/
theorem rankCofinalCut_idempotent {κ : PSet.{u}} :
    rankCofinalCut ψ e a (rankCofinalCut ψ e a κ) ≈
      rankCofinalCut ψ e a κ :=
  ext fun _ => mem_rankCofinalCut.trans
    ⟨And.left, fun h => ⟨h, (mem_rankCofinalCut.1 h).2⟩⟩

/-- Boundedness is exactly the negation of class-wide cofinality. -/
theorem rankBounded_iff_not_cofinal :
    RankBounded ψ e a ↔
      ¬ (∀ κ : PSet.{u}, IsOrd κ → CoveredRank ψ e a κ) := by
  constructor
  · intro hb hc
    exact Stable.of_nn hb fun ⟨κ, hk, hbound⟩ =>
      ((not_coveredRank_iff hk).2 hbound) (hc κ hk)
  · intro hn
    change ¬¬∃ κ, IsOrd κ ∧ ∀ x y, x ∈ a → HG y →
      Sat HG ψ (Env.cons x (Env.cons y e)) → rank y ∈ κ
    intro hex
    have hnot : ¬ RankBounded ψ e a := fun hb => hb hex
    exact hn (fun κ hk => coverage_of_not_rankBounded hnot hk)

/-- Failure makes HG the entire ambient universe. -/
theorem hg_universal_of_not_rankBounded (h : ¬ RankBounded ψ e a) :
    ∀ x : PSet.{u}, HG x :=
  fun x => all_cls_of_not_rankBounded h (rank x) (isOrd_rank x)

/-- If a cut is strictly shorter than its cap, the cut itself is a strict bound. -/
theorem strict_rankCofinalCut_bounds {κ : PSet.{u}} (hk : IsOrd κ)
    (h : rankCofinalCut ψ e a κ ∈ κ) :
    ∀ x y, x ∈ a → HG y →
      Sat HG ψ (Env.cons x (Env.cons y e)) →
        rank y ∈ rankCofinalCut ψ e a κ := by
  apply (not_coveredRank_iff (isOrd_rankCofinalCut hk)).1
  intro hc
  exact not_mem_self _ (mem_rankCofinalCut.2 ⟨h, hc⟩)

end

/-- info: 'PSet.cls_rankCofinalCut' does not depend on any axioms -/
#guard_msgs in #print axioms cls_rankCofinalCut
/-- info: 'PSet.hg_replacement_of_rank_bound' does not depend on any axioms -/
#guard_msgs in #print axioms hg_replacement_of_rank_bound
/-- info: 'PSet.hg_universal_of_not_rankBounded' does not depend on any axioms -/
#guard_msgs in #print axioms hg_universal_of_not_rankBounded
end PSet
