import ConZFCIn.Model.JointUpper

/-! The cofinality interpreter and lower-universe reachability arguments from the
pinned upstream `Cofinality.lean`, generalized to a common upper universe.
The interpreter's upper-universe data appear through propositions, while its inputs,
budgets, and reachability constructions remain in the lower universe. -/

universe u v

namespace PSet.Multi
variable (M : UpperModel.{u,v})

/-- **The cofinality interpreter**: at target `η` and domain code `q`, the least cofinal map
`lift.{u,v+1} q → lift.{u,v+1} η` of `N`, read at `lift.{u,v+1} x`. -/
def cofI (η q x y : PSet.{u}) : Prop :=
  IsOrd η ∧ M.N (lift.{u,v+1} q) ∧ ¬¬∃ f, M.N f ∧ M.LeastCof f (lift.{u,v+1} q) (lift.{u,v+1} η) ∧ pair (lift.{u,v+1} x) (lift.{u,v+1} y) ∈ f

theorem cofI_resp {η η' q q' x x' y y' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : cofI M η q x y) : cofI M η' q' x' y' :=
  ⟨h.1.resp eη, M.N_resp (lift_congr eq) h.2.1, nn_map (fun ⟨f, hN, hl, hp⟩ => ⟨f, hN,
    M.leastCof_resp (lift_congr eq) (lift_congr eη) hl,
    (mem_congr_left (pair_congr (lift_congr ex) (lift_congr ey))).1 hp⟩) h.2.2⟩

/-- **Unboundedness.** When `N` has a cofinal map `lift.{u,v+1} q → lift.{u,v+1} η`, the interpreter is a
partial function on `q` with values of rank covering `η`. -/
theorem unb_cofI {η q : PSet.{u}} (hη : IsOrd η) (hq : M.N (lift.{u,v+1} q))
    (hg : ¬¬∃ g, M.N g ∧ Cof g (lift.{u,v+1} q) (lift.{u,v+1} η)) : Unb (cofI M) η q q := by
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
    refine Stable.of_nn (hc.2.2 (lift.{u,v+1} ζ) (lift_mem_of_mem hζ)) fun ⟨x', y', hp, hζy⟩ => ?_
    have ⟨hx', hy'⟩ := hc.1 _ _ hp
    refine Stable.of_nn (mem_lift.1 hx') fun ⟨x, hx, ex⟩ => Stable.of_nn (mem_lift.1 hy') fun ⟨y, hy, ey⟩ => ?_
    have hp' : pair (lift.{u,v+1} x) (lift.{u,v+1} y) ∈ f := (mem_congr_left (pair_congr ex ey)).1 hp
    refine nn_intro ⟨x, y, hx, ⟨hη, hq, nn_intro ⟨f, hN, hl, hp'⟩⟩, ?_⟩
    have h1 : lift.{u,v+1} ζ ∈ lift.{u,v+1} (succ y) :=
      (mem_congr_right ((succ_congr ey).trans (lift_succ y).symm)).1 hζy
    exact (mem_congr_right (succ_congr (hη.mem hy).rank_equiv.symm)).1 (lift_mem.1 h1)

/-- **Reachability.** Every nonzero lower ordinal whose lift.{u,v+1} is not inaccessible in `N` is
reachable by the cofinality interpreter. -/
theorem reachable_cofI [B : Budget.{u}] {η : PSet.{u}} (hη : IsOrd η) (hne : ∃ ζ, ζ ∈ η)
    (hni : ¬ InaccIn M.N (lift.{u,v+1} η)) : Reachable (cofI M) η := by
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
    have hsub : ∀ w, w ∈ P → w ∈ lift.{u,v+1} (powerset l) := fun w hw =>
      (mem_congr_right (lift_powerset l)).2 (hPsub w hw)
    have eq : lift.{u,v+1} (shrink (powerset l) P) ≈ P := lift_shrink hsub
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
theorem cls_cofI [B : Budget.{u}] (hni : ∀ η : PSet.{u}, IsOrd η → ¬ InaccIn M.N (lift.{u,v+1} η)) :
    ∀ η : PSet.{u}, IsOrd η → Cls (cofI M) η := fun _ hη =>
  ⟨hη, fun μ hμ ζ hζ => reachable_cofI M (hη.succ.mem hμ) ⟨ζ, hζ⟩ (hni μ (hη.succ.mem hμ))⟩

/-- **The conditional bound.** Under excluded middle and no smaller inaccessible, every
functional ordinal-valued relation on a supplied lower source has an actual ordinal bound. -/
theorem ordBound_of_noInacc [B : Budget.{u}] (hni : ∀ η : PSet.{u}, IsOrd η → ¬ InaccIn M.N (lift.{u,v+1} η))
    (em : ∀ p : Prop, p ∨ ¬p) (s : PSet.{u}) (φ : PSet.{u} → PSet.{u} → Prop)
    (φ_resp : ∀ {x x' y y' : PSet.{u}}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (φ_func : ∀ {x y y' : PSet.{u}}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (φ_ord : ∀ {x y : PSet.{u}}, x ∈ s → φ x y → IsOrd y) :
    ∃ κ : PSet.{u}, IsOrd κ ∧ ∀ x η, x ∈ s → φ x η → η ∈ κ :=
  ⟨ordBound (cofI_resp M) (cls_cofI M hni) em s φ φ_resp φ_func φ_ord,
   isOrd_ordBound (cofI_resp M) (cls_cofI M hni) em s φ φ_resp φ_func φ_ord,
   fun _ _ hx h => mem_ordBound_of (cofI_resp M) (cls_cofI M hni) em s φ φ_resp φ_func φ_ord hx h⟩
#print axioms reachable_cofI
#print axioms ordBound_of_noInacc

end PSet.Multi
