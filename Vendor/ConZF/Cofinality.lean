import Vendor.ConZF.AllGood
import Vendor.ConZF.MixedHartogs
/-!
The domain-coded cofinality interpreter (con22 §3–5), against an explicit interface for an
upper class `N` (`UpperModel`). The interface states exactly what is assumed of `N`: it is
extensional and contains the lifts of lower ordinals; it has a relation `LeastCof f Q ζ`
("`f` is the least partial cofinal relation from `Q` to `ζ` of `N`") that is extensional,
unique, and cofinal (`Cof`: a functional set of pairs from `Q` into `ζ`, not necessarily total,
whose values reach every `ξ ∈ ζ` inclusively), and that exists as soon as some cofinal relation
of `N` exists; it contains the identity graphs on lifted lower ordinals; and it classifies the lifts of nonzero lower
ordinals that are not inaccessible in `N` into three cases: at most `ω`, with a cofinal map
from `ω`; of smaller cofinality, with a cofinal map from a smaller lower ordinal; or regular
and not a strong limit, with a cofinal map from an internal powerset `P ⊆ P(lift l)` of a
smaller `l` with `succ l` still below. Regularity, strong limit, initiality, and inaccessibility in `N` are
explicit set-theoretic notions quantifying over the functions and injections of `N`
(`RegularIn`, `StrongLimitIn`, `InitialIn`, `InaccIn`).

The interpreter `cofI M η q x y` reads the least cofinal map `lift q → lift η` of `N` at
`lift x`: the target `η` is an argument, and the code `q` is only the domain. It respects
bisimulation (`cofI_resp`) and is unbounded on `q` whenever `N` has a cofinal map from
`lift q` (`unb_cofI`). Every nonzero lower ordinal not inaccessible in `N` is reachable
(`reachable_cofI`); in the third case the source is `shrink (powerset l) P`, whose lift is `P`
(`lift_shrink`), lying in the budget at `succ l`. Hence, if no lift of a lower ordinal is
inaccessible in `N`, every lower ordinal is hereditarily good (`cls_cofI`), and under excluded
middle every functional ordinal-valued relation on a supplied lower source has the native
bound of `AllGood.lean` (`ordBound_of_noInacc`). That is the conditional half of the
dichotomy; the other half, an inaccessible of `N` below `K`, is the negation of the
hypothesis. The regularity of `K` against upper functions, the internal `L`, and the
strong-limit argument are not formalized.
-/
universe u

namespace PSet

/-- A cofinal relation from `Q` to `ζ`, set-coded: a functional set of pairs with inputs in `Q`
and values in `ζ`, reaching every member of `ζ` inclusively. It is **partial**: nothing requires
every member of `Q` to have a value (`Cof empty Q empty` holds for every `Q`). Partiality is
enough for `Unb`, and the least-candidate relation of `UpperModel` is understood as minimizing
partial cofinal graphs. A total cofinal function is a cofinal relation (`Cof.of_isFun`). -/
def Cof (g Q ζ : PSet.{u+1}) : Prop :=
  (∀ x y, pair x y ∈ g → x ∈ Q ∧ y ∈ ζ) ∧ (∀ x y y', pair x y ∈ g → pair x y' ∈ g → y ≈ y') ∧
  (∀ ξ, ξ ∈ ζ → ¬¬∃ x y, pair x y ∈ g ∧ ξ ∈ succ y)

theorem Cof.congr_dom {g Q Q' ζ : PSet.{u+1}} (e : Q ≈ Q') (h : Cof g Q ζ) : Cof g Q' ζ :=
  ⟨fun x y hp => ⟨(mem_congr_right e).1 (h.1 x y hp).1, (h.1 x y hp).2⟩, h.2.1, h.2.2⟩

/-- An ordinary set-coded function from `Q` to `ζ`: a functional set of pairs with inputs in
`Q` and values in `ζ`, total on `Q`. Only the pairs in `f` are constrained: `f` may contain
members that are not pairs (`IsFun {∅} ∅ ∅` holds), and only the represented relation is ever
consumed. The syntactic function predicate of `Cardinal.lean` requires every member to be a
pair, which implies this one. -/
def IsFun (f Q ζ : PSet.{u}) : Prop :=
  (∀ x y, pair x y ∈ f → x ∈ Q ∧ y ∈ ζ) ∧ (∀ x y y', pair x y ∈ f → pair x y' ∈ f → y ≈ y') ∧
  (∀ x, x ∈ Q → ¬¬∃ y, pair x y ∈ f)

/-- A total cofinal function is a cofinal relation. -/
theorem Cof.of_isFun {g Q ζ : PSet.{u+1}} (h : IsFun g Q ζ)
    (hc : ∀ ξ, ξ ∈ ζ → ¬¬∃ x y, pair x y ∈ g ∧ ξ ∈ succ y) : Cof g Q ζ :=
  ⟨h.1, h.2.1, hc⟩

/-- The identity graph on a set. -/
def idGraph (X : PSet.{u}) : PSet.{u} := range fun i : X.Idx => pair (X.Func i) (X.Func i)

theorem mem_idGraph {X p : PSet.{u}} : p ∈ idGraph X ↔ ¬¬∃ x, x ∈ X ∧ p ≈ pair x x :=
  ⟨nn_map fun ⟨i, e⟩ => ⟨X.Func i, func_mem X i, e⟩,
   fun h => nn_bind h fun ⟨_, hx, e⟩ => nn_map (fun ⟨i, e'⟩ =>
     ⟨i, e.trans (pair_congr e' e')⟩) hx⟩

/-! ### Explicit cardinal notions relative to a class -/

/-- `κ` is regular in `N`: every function of `N` from a member of `κ` into `κ` has its values
inside a member of `κ`. -/
def RegularIn (N : PSet.{u} → Prop) (κ : PSet.{u}) : Prop :=
  ∀ δ f, δ ∈ κ → N f → IsFun f δ κ → ¬¬∃ β, β ∈ κ ∧ ∀ x y, pair x y ∈ f → y ∈ β

/-- `κ` is a strong limit in `N`: every ordinal injecting relationally, by an injection of `N`,
into a set of `N` of subsets of a member of `κ` is a member of `κ`. -/
def StrongLimitIn (N : PSet.{u} → Prop) (κ : PSet.{u}) : Prop :=
  ∀ lam θ P f, lam ∈ κ → IsOrd θ → N P → N f → (∀ w, w ∈ P → w ∈ powerset lam) →
    IsInjRel θ P f → θ ∈ κ

/-- `κ` is initial in `N`: no relational injection of `N` into a member. -/
def InitialIn (N : PSet.{u} → Prop) (κ : PSet.{u}) : Prop := ∀ δ f, δ ∈ κ → N f → ¬ IsInjRel κ δ f

/-- `κ` is inaccessible in `N`: an ordinal above `ω`, initial, regular, and a strong limit, all
against the functions and injections of `N`. -/
def InaccIn (N : PSet.{u} → Prop) (κ : PSet.{u}) : Prop :=
  IsOrd κ ∧ omega ∈ κ ∧ InitialIn N κ ∧ RegularIn N κ ∧ StrongLimitIn N κ

/-- **The upper-model interface.** -/
structure UpperModel : Type (u+2) where
  N : PSet.{u+1} → Prop
  N_resp : ∀ {x y}, x ≈ y → N x → N y
  N_lift_ord : ∀ η : PSet.{u}, IsOrd η → N (lift η)
  /-- `f` is the least (partial) cofinal relation from `Q` to `ζ` of `N` -/
  LeastCof : PSet.{u+1} → PSet.{u+1} → PSet.{u+1} → Prop
  leastCof_resp : ∀ {f Q Q' ζ ζ'}, Q ≈ Q' → ζ ≈ ζ' → LeastCof f Q ζ → LeastCof f Q' ζ'
  leastCof_unique : ∀ {f f' Q ζ}, LeastCof f Q ζ → LeastCof f' Q ζ → f ≈ f'
  leastCof_cof : ∀ {f Q ζ}, LeastCof f Q ζ → Cof f Q ζ
  leastCof_exists : ∀ {Q ζ}, N Q → N ζ → IsOrd ζ → (¬¬∃ g, N g ∧ Cof g Q ζ) →
    ¬¬∃ f, N f ∧ LeastCof f Q ζ
  /-- the identity graph on a lifted lower ordinal is in `N` -/
  N_idGraph : ∀ η : PSet.{u}, IsOrd η → N (idGraph (lift η))
  /-- the height of the lower universe is in `N` -/
  N_K : N K.{u}
  /-- nonzero ordinals at most `ω` have a cofinal map from `ω` -/
  cof_small : ∀ η : PSet.{u}, IsOrd η → η ∈ succ omega → (∃ ζ, ζ ∈ η) →
    ¬¬∃ g, N g ∧ Cof g (lift omega) (lift η)
  /-- above `ω`: smaller cofinality, with a cofinal map from a smaller lower ordinal, or regular -/
  cof_lt_or_reg : ∀ η : PSet.{u}, IsOrd η → omega ∈ η →
    ¬¬((¬¬∃ d : PSet.{u}, d ∈ η ∧ ¬¬∃ g, N g ∧ Cof g (lift d) (lift η)) ∨ RegularIn N (lift η))
  /-- regular but not inaccessible: not a strong limit, so an internal powerset of a smaller
  `l` maps cofinally; `succ l` is still below -/
  cof_powerset : ∀ η : PSet.{u}, IsOrd η → omega ∈ η → RegularIn N (lift η) →
    ¬ InaccIn N (lift η) →
    ¬¬∃ (l : PSet.{u}) (P : PSet.{u+1}), succ l ∈ η ∧ N P ∧ (∀ w, w ∈ P → w ∈ powerset (lift l)) ∧
      ¬¬∃ g, N g ∧ Cof g P (lift η)

variable (M : UpperModel.{u})

/-- **The cofinality interpreter**: at target `η` and domain code `q`, the least cofinal map
`lift q → lift η` of `N`, read at `lift x`. -/
def cofI (η q x y : PSet.{u}) : Prop :=
  IsOrd η ∧ M.N (lift q) ∧ ¬¬∃ f, M.N f ∧ M.LeastCof f (lift q) (lift η) ∧ pair (lift x) (lift y) ∈ f

theorem cofI_resp {η η' q q' x x' y y' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : cofI M η q x y) : cofI M η' q' x' y' :=
  ⟨h.1.resp eη, M.N_resp (lift_congr eq) h.2.1, nn_map (fun ⟨f, hN, hl, hp⟩ => ⟨f, hN,
    M.leastCof_resp (lift_congr eq) (lift_congr eη) hl,
    (mem_congr_left (pair_congr (lift_congr ex) (lift_congr ey))).1 hp⟩) h.2.2⟩

/-- **Unboundedness.** When `N` has a cofinal map `lift q → lift η`, the interpreter is a
partial function on `q` with values of rank covering `η`. -/
theorem unb_cofI {η q : PSet.{u}} (hη : IsOrd η) (hq : M.N (lift q))
    (hg : ¬¬∃ g, M.N g ∧ Cof g (lift q) (lift η)) : Unb (cofI M) η q q := by
  have hf := M.leastCof_exists hq (M.N_lift_ord η hη) (isOrd_lift hη) hg
  refine ⟨fun x y y' _ h1 h2 => ?_, fun x y _ h1 => ?_, fun ζ hζ => ?_⟩
  · refine Stable.of_nn h1.2.2 fun ⟨f, _, hl, hp⟩ => Stable.of_nn h2.2.2 fun ⟨f', _, hl', hp'⟩ => ?_
    have e := M.leastCof_unique hl hl'
    exact lift_equiv.1 ((M.leastCof_cof hl').2.1 _ _ _ ((mem_congr_right e).1 hp) hp')
  · refine Stable.of_nn h1.2.2 fun ⟨f, _, hl, hp⟩ => ?_
    have hy : y ∈ η := lift_mem.1 ((M.leastCof_cof hl).1 _ _ hp).2
    exact (mem_congr_left (hη.mem hy).rank_equiv).2 hy
  · refine Stable.of_nn hf fun ⟨f, hN, hl⟩ => ?_
    have hc := M.leastCof_cof hl
    refine Stable.of_nn (hc.2.2 (lift ζ) (lift_mem_of_mem hζ)) fun ⟨x', y', hp, hζy⟩ => ?_
    have ⟨hx', hy'⟩ := hc.1 _ _ hp
    refine Stable.of_nn (mem_lift.1 hx') fun ⟨x, hx, ex⟩ => Stable.of_nn (mem_lift.1 hy') fun ⟨y, hy, ey⟩ => ?_
    have hp' : pair (lift x) (lift y) ∈ f := (mem_congr_left (pair_congr ex ey)).1 hp
    refine nn_intro ⟨x, y, hx, ⟨hη, hq, nn_intro ⟨f, hN, hl, hp'⟩⟩, ?_⟩
    have h1 : lift ζ ∈ lift (succ y) :=
      (mem_congr_right ((succ_congr ey).trans (lift_succ y).symm)).1 hζy
    exact (mem_congr_right (succ_congr (hη.mem hy).rank_equiv.symm)).1 (lift_mem.1 h1)

/-- **Reachability.** Every nonzero lower ordinal whose lift is not inaccessible in `N` is
reachable by the cofinality interpreter. -/
theorem reachable_cofI [B : Budget.{u}] {η : PSet.{u}} (hη : IsOrd η) (hne : ∃ ζ, ζ ∈ η)
    (hni : ¬ InaccIn M.N (lift η)) : Reachable (cofI M) η := by
  obtain ⟨ζ₀, hζ₀⟩ := hne
  have small : η ∈ succ omega → Reachable (cofI M) η := fun hle =>
    nn_intro ⟨ζ₀, hζ₀, nn_intro ⟨omega, omega, omega_mem_D ζ₀, omega_mem_D ζ₀,
      unb_cofI M hη (M.N_lift_ord omega isOrd_omega) (M.cof_small η hη hle ⟨ζ₀, hζ₀⟩)⟩⟩
  refine Stable.of_nn (hη.trichotomy isOrd_omega) fun
    | .inl h => small (mem_succ_of_mem h)
    | .inr (.inl e) => small (mem_succ_of_equiv e)
    | .inr (.inr h) => ?_
  -- case: above `ω`
  refine Stable.of_nn (M.cof_lt_or_reg η hη h) fun
    | .inl hd => ?_
    | .inr hreg => ?_
  · -- smaller cofinality: the smaller lower ordinal is its own code and source
    refine Stable.of_nn hd fun ⟨d, hdη, hg⟩ => ?_
    exact nn_intro ⟨d, hdη, nn_intro ⟨d, d, self_mem_D d, self_mem_D d,
      unb_cofI M hη (M.N_lift_ord d (hη.mem hdη)) hg⟩⟩
  · -- regular, not a strong limit: shrink the internal powerset to a lower source
    refine Stable.of_nn (M.cof_powerset η hη h hreg hni) fun ⟨l, P, hl, hP, hPsub, hg⟩ => ?_
    have hlo : IsOrd l := (hη.mem hl).mem (self_mem_succ l)
    have hsub : ∀ w, w ∈ P → w ∈ lift (powerset l) := fun w hw =>
      (mem_congr_right (lift_powerset l)).2 (hPsub w hw)
    have eq : lift (shrink (powerset l) P) ≈ P := lift_shrink hsub
    -- the source lies in the budget at `succ l`: its rank is included in `succ l`
    have hrank : ∀ z, z ∈ rank (shrink (powerset l) P) → z ∈ succ l := by
      intro z hz
      refine Stable.of_nn (mem_rank'.1 hz) fun ⟨w, hw, hzw⟩ => ?_
      have hwl : ∀ v, v ∈ rank w → v ∈ l := fun v hv =>
        Stable.of_nn (mem_rank'.1 hv) fun ⟨t, ht, hvt⟩ => by
          have htl : t ∈ l := mem_powerset.1 (mem_shrink.1 hw).1 t ht
          have hrt : rank t ∈ l := (mem_congr_left (hlo.mem htl).rank_equiv).2 htl
          exact Stable.of_nn (mem_succ.1 hvt) fun
            | .inl hv => hlo.trans _ hrt v hv
            | .inr e => (mem_congr_left e).2 hrt
      exact Stable.of_nn (mem_succ.1 hzw) fun
        | .inl hz => mem_succ_of_mem (hwl z hz)
        | .inr e => (mem_congr_left e).2 ((isOrd_rank w).mem_succ_of_subset hlo hwl)
    refine nn_intro ⟨succ l, hl, nn_intro ⟨shrink (powerset l) P, shrink (powerset l) P,
      mem_D_of_subset hlo.succ hrank, mem_D_of_subset hlo.succ hrank, ?_⟩⟩
    exact unb_cofI M hη (M.N_resp eq.symm hP)
      (nn_map (fun ⟨g, hN, hc⟩ => ⟨g, hN, hc.congr_dom eq.symm⟩) hg)

/-- **No smaller inaccessible makes every lower ordinal hereditarily good.** -/
theorem cls_cofI [B : Budget.{u}] (hni : ∀ η : PSet.{u}, IsOrd η → ¬ InaccIn M.N (lift η)) :
    ∀ η : PSet.{u}, IsOrd η → Cls (cofI M) η := fun _ hη =>
  ⟨hη, fun μ hμ ζ hζ => reachable_cofI M (hη.succ.mem hμ) ⟨ζ, hζ⟩ (hni μ (hη.succ.mem hμ))⟩

/-- **The conditional bound.** Under excluded middle and no smaller inaccessible, every
functional ordinal-valued relation on a supplied lower source has an actual ordinal bound. -/
theorem ordBound_of_noInacc [B : Budget.{u}] (hni : ∀ η : PSet.{u}, IsOrd η → ¬ InaccIn M.N (lift η))
    (em : ∀ p : Prop, p ∨ ¬p) (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop)
    (φ_resp : ∀ {x x' y y' : PSet.{u}}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (φ_func : ∀ {x y y' : PSet.{u}}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (φ_ord : ∀ {x y : PSet.{u}}, x ∈ s → φ x y → IsOrd y) :
    ∃ κ : PSet.{u}, IsOrd κ ∧ ∀ x η, x ∈ s → φ x η → η ∈ κ :=
  ⟨ordBound (cofI_resp M) (cls_cofI M hni) em s φ φ_resp φ_func φ_ord,
   isOrd_ordBound (cofI_resp M) (cls_cofI M hni) em s φ φ_resp φ_func φ_ord,
   fun _ _ hx h => mem_ordBound_of (cofI_resp M) (cls_cofI M hni) em s φ φ_resp φ_func φ_ord hx h⟩

/-- info: 'PSet.reachable_cofI' does not depend on any axioms -/
#guard_msgs in #print axioms reachable_cofI
/-- info: 'PSet.ordBound_of_noInacc' does not depend on any axioms -/
#guard_msgs in #print axioms ordBound_of_noInacc

end PSet
