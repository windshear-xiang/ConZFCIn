import ConZFCIn.Model.SeededClass
import ConZFCIn.Universe.Embedding

/-!
A common-upper-universe version of the adjacent-universe `UpperModel` interface.
The upper type is `PSet.{max u v + 1}`, so the upstream `Cof` definitions, least-program
results, and `SynZF` classification theorems apply directly.

`upperModel_of_synZF` assembles the interface for a supplied class `N`. The same class
can therefore support interval arguments for several lower universes.
-/

universe u v

namespace PSet.Multi

structure UpperModel : Type (max u v + 2) where
  N : PSet.{max u v + 1} → Prop
  N_resp : ∀ {x y}, x ≈ y → N x → N y
  N_lift_ord : ∀ η : PSet.{u}, IsOrd η → N (lift.{u,v+1} η)
  LeastCof : PSet.{max u v + 1} → PSet.{max u v + 1} → PSet.{max u v + 1} → Prop
  leastCof_resp : ∀ {f Q Q' ζ ζ'}, Q ≈ Q' → ζ ≈ ζ' → LeastCof f Q ζ → LeastCof f Q' ζ'
  leastCof_unique : ∀ {f f' Q ζ}, LeastCof f Q ζ → LeastCof f' Q ζ → f ≈ f'
  leastCof_cof : ∀ {f Q ζ}, LeastCof f Q ζ → Cof f Q ζ
  leastCof_exists : ∀ {Q ζ}, N Q → N ζ → IsOrd ζ → (¬¬∃ g, N g ∧ Cof g Q ζ) →
    ¬¬∃ f, N f ∧ LeastCof f Q ζ
  N_idGraph : ∀ η : PSet.{u}, IsOrd η → N (idGraph (lift.{u,v+1} η))
  N_K : N K.{u,v+1}
  cof_small : ∀ η : PSet.{u}, IsOrd η → η ∈ succ omega → (∃ ζ, ζ ∈ η) →
    ¬¬∃ g, N g ∧ Cof g (lift.{u,v+1} omega) (lift.{u,v+1} η)
  cof_lt_or_reg : ∀ η : PSet.{u}, IsOrd η → omega ∈ η →
    ¬¬((¬¬∃ d : PSet.{u}, d ∈ η ∧ ¬¬∃ g, N g ∧ Cof g (lift.{u,v+1} d) (lift.{u,v+1} η)) ∨
      RegularIn N (lift.{u,v+1} η))
  cof_powerset : ∀ η : PSet.{u}, IsOrd η → omega ∈ η → RegularIn N (lift.{u,v+1} η) →
    ¬ InaccIn N (lift.{u,v+1} η) →
    ¬¬∃ (l : PSet.{u}) (P : PSet.{max u v + 1}), succ l ∈ η ∧ N P ∧
      (∀ w, w ∈ P → w ∈ powerset (lift.{u,v+1} l)) ∧
      ¬¬∃ g, N g ∧ Cof g P (lift.{u,v+1} η)

theorem cof_idGraph_le {η ζ : PSet.{u}} (hζ : IsOrd ζ) (hle : η ∈ succ ζ) :
    Cof (idGraph (lift.{u,v+1} η)) (lift.{u,v+1} ζ) (lift.{u,v+1} η) := by
  have hsub : ∀ x, x ∈ η → x ∈ ζ := fun x hx => Stable.of_nn (mem_succ.1 hle) fun
    | .inl h => hζ.trans _ h x hx
    | .inr e => (mem_congr_right e).1 hx
  refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun ξ hξ => ?_⟩
  · refine Stable.of_nn (mem_idGraph.1 hp) fun ⟨z, hz, e⟩ => ?_
    have ⟨ex, ey⟩ := pair_inj e
    refine ⟨?_, (mem_congr_left ey).2 hz⟩
    refine Stable.of_nn (mem_lift.1 hz) fun ⟨x₀, hx₀, e'⟩ => ?_
    exact (mem_congr_left (ex.trans e')).2 (lift_mem_of_mem (hsub x₀ hx₀))
  · refine Stable.of_nn (mem_idGraph.1 hp) fun ⟨z, _, e⟩ =>
      Stable.of_nn (mem_idGraph.1 hp') fun ⟨z', _, e'⟩ => ?_
    have ⟨ex, ey⟩ := pair_inj e
    have ⟨ex', ey'⟩ := pair_inj e'
    exact ey.trans ((ex.symm.trans ex').trans ey'.symm)
  · exact nn_intro ⟨ξ, ξ, mem_idGraph.2 (nn_intro ⟨ξ, hξ, Equiv.refl _⟩), self_mem_succ ξ⟩

section Assembly
variable {N : PSet.{max u v + 1} → Prop} (hN : SynZF N)
  (hself : ∀ x, N x → Constr N x) (hK : N K.{u,v+1})
include hN hK

theorem lift_ord_mem (η : PSet.{u}) (hη : IsOrd η) : N (lift.{u,v+1} η) :=
  hN.trans hK (lift_mem_K hη)

theorem cof_small (η : PSet.{u}) (hη : IsOrd η) (hle : η ∈ succ omega) (_hne : ∃ ζ, ζ ∈ η) :
    ¬¬∃ g, N g ∧ Cof g (lift.{u,v+1} omega) (lift.{u,v+1} η) :=
  nn_intro ⟨idGraph (lift.{u,v+1} η), hN.idGraph_mem (lift_ord_mem hN hK η hη),
    cof_idGraph_le isOrd_omega hle⟩

omit hN hK in
theorem cof_lt_or_reg (η : PSet.{u}) (hη : IsOrd η) (_hω : omega ∈ η) :
    ¬¬((¬¬∃ d : PSet.{u}, d ∈ η ∧ ¬¬∃ g, N g ∧ Cof g (lift.{u,v+1} d) (lift.{u,v+1} η)) ∨
      RegularIn N (lift.{u,v+1} η)) := by
  refine nn_map (fun h => h.imp (fun k => nn_bind k fun ⟨δ, hδ, k⟩ => ?_) id)
    (SynZF.cof_lt_or_reg_of_synZF (N := N) (isOrd_lift hη))
  refine nn_map (fun ⟨d, hd, ed⟩ =>
    ⟨d, hd, nn_map (fun ⟨g, hg, hc⟩ => ⟨g, hg, hc.congr_dom ed⟩) k⟩) (mem_lift.1 hδ)

theorem cof_powerset (η : PSet.{u}) (hη : IsOrd η) (hω : omega ∈ η)
    (hreg : RegularIn N (lift.{u,v+1} η)) (hni : ¬ InaccIn N (lift.{u,v+1} η)) :
    ¬¬∃ (l : PSet.{u}) (P : PSet.{max u v + 1}), succ l ∈ η ∧ N P ∧
      (∀ w, w ∈ P → w ∈ powerset (lift.{u,v+1} l)) ∧
      ¬¬∃ g, N g ∧ Cof g P (lift.{u,v+1} η) := by
  have hωl : PSet.omega ∈ lift.{u,v+1} η := (mem_congr_left lift_omega).1 (lift_mem_of_mem hω)
  refine nn_bind (hN.cof_powerset_of_synZF (lift_ord_mem hN hK η hη) (isOrd_lift hη) hωl hreg hni)
    fun ⟨lam, P, hlam, hslam, hP, hpow, hg⟩ => ?_
  refine nn_map (fun ⟨l, _, el⟩ => ⟨l, P, ?_, hP, fun w hw => ?_, hg⟩) (mem_lift.1 hlam)
  · have : lift.{u,v+1} (succ l) ∈ lift.{u,v+1} η :=
      (mem_congr_left ((lift_succ l).trans (succ_congr el.symm))).2 hslam
    exact lift_mem.1 this
  · exact (mem_congr_right (powerset_congr el)).1 (hpow w hw)

/-- Assemble every interface field from the supplied `SynZF` class, constructibility
of all its members, and membership of the lower-universe height. -/
def upperModel_of_synZF : UpperModel.{u,v} where
  N := N
  N_resp := hN.resp
  N_lift_ord := lift_ord_mem hN hK
  LeastCof := LeastCofN N
  leastCof_resp := fun eQ eζ h => SynZF.leastCofN_resp eQ eζ h
  leastCof_unique := fun h h' => hN.leastCofN_unique h h'
  leastCof_cof := fun h => SynZF.leastCofN_cof h
  leastCof_exists := fun hQ hζ hζo h => hN.leastCofN_exists hself hQ hζ hζo h
  N_idGraph := fun η hη => hN.idGraph_mem (lift_ord_mem hN hK η hη)
  N_K := hK
  cof_small := cof_small hN hK
  cof_lt_or_reg := cof_lt_or_reg
  cof_powerset := cof_powerset hN hK

end Assembly

/-- The concrete common model. Each lower universe supplies a proof that its height
is at most the same ordinal seed `b`. The resulting predicate `N` is definitionally `L b`,
independent of the lower-universe parameter. -/
def upperModel_seeded (b : PSet.{max u v + 1}) (em : ∀ p : Prop, p ∨ ¬p)
    (hb : IsOrd b) (hK : K.{u,v+1} ∈ succ b) : UpperModel.{u,v} :=
  upperModel_of_synZF (synZF_L b em) (L_self b em) (L_le_seed em hb hK)

theorem upperModel_seeded_N (b : PSet.{max u v + 1}) (em : ∀ p : Prop, p ∨ ¬p)
    (hb : IsOrd b) (hK : K.{u,v+1} ∈ succ b) :
    (upperModel_seeded b em hb hK).N = L b := rfl

#print axioms upperModel_of_synZF
#print axioms upperModel_seeded

end PSet.Multi
