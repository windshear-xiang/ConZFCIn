import ConZFCIn.Model.Cofinality
import ConZFCIn.Universe.Hartogs
import Vendor.ConZF.Interval

/-! The excluded-middle interval argument from the pinned upstream `Interval.lean`,
generalized so several lower universes can use the same upper class. -/
universe u v
namespace PSet.Multi

variable (M : UpperModel.{u,v}) (b : PSet.{u})

/-- The identity graph on a lifted ordinal `η ≤ rank b` is a partial cofinal relation from
`lift.{u,v+1} (succ (rank b))`. -/
theorem cof_idGraph {η : PSet.{u}} (hle : η ∈ succ (rank b)) :
    Cof (idGraph (lift.{u,v+1} η)) (lift.{u,v+1} (succ (rank b))) (lift.{u,v+1} η) := by
  have hsub : ∀ ζ, ζ ∈ η → ζ ∈ succ (rank b) := fun ζ hζ => Stable.of_nn (mem_succ.1 hle) fun
    | .inl h => mem_succ_of_mem ((isOrd_rank b).trans _ h ζ hζ)
    | .inr e => mem_succ_of_mem ((mem_congr_right e).1 hζ)
  refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun ξ hξ => ?_⟩
  · refine Stable.of_nn (mem_idGraph.1 hp) fun ⟨z, hz, e⟩ => ?_
    have ⟨ex, ey⟩ := pair_inj e
    refine ⟨?_, (mem_congr_left ey).2 hz⟩
    refine Stable.of_nn (mem_lift.1 hz) fun ⟨ζ, hζ, e'⟩ => ?_
    exact (mem_congr_left (ex.trans e')).2 (lift_mem_of_mem (hsub ζ hζ))
  · refine Stable.of_nn (mem_idGraph.1 hp) fun ⟨z, _, e⟩ =>
      Stable.of_nn (mem_idGraph.1 hp') fun ⟨z', _, e'⟩ => ?_
    have ⟨ex, ey⟩ := pair_inj e
    have ⟨ex', ey'⟩ := pair_inj e'
    exact ey.trans ((ex.symm.trans ex').trans ey'.symm)
  · exact nn_intro ⟨ξ, ξ, mem_idGraph.2 (nn_intro ⟨ξ, hξ, Equiv.refl _⟩), self_mem_succ ξ⟩

/-- **Reachability below the seed.** A nonzero ordinal `η ≤ rank b` is reached, for the
seeded budget, from any of its elements. -/
theorem reachable_below {η ζ₀ : PSet.{u}} (hη : IsOrd η) (hle : η ∈ succ (rank b)) (hζ₀ : ζ₀ ∈ η) :
    Reachable (B := seeded b) (cofI M) η :=
  have hs : succ (rank b) ∈ @Budget.D.{u} (seeded b) ζ₀ := seededD_empty_sub (succ_rank_mem_seededD b)
  nn_intro ⟨ζ₀, hζ₀, nn_intro ⟨succ (rank b), succ (rank b), hs, hs,
    unb_cofI M hη (M.N_lift_ord _ (isOrd_rank b).succ)
      (nn_intro ⟨idGraph (lift.{u,v+1} η), M.N_idGraph η hη, cof_idGraph b hle⟩)⟩⟩

/-- **The interval hypothesis** for `b`: no lift.{u,v+1} of a lower ordinal above `rank b` is
inaccessible in `N`. -/
def NoGap : Prop := ∀ η : PSet.{u}, IsOrd η → rank b ∈ η → ¬ InaccIn M.N (lift.{u,v+1} η)

/-- Under the interval hypothesis every lower ordinal is hereditarily good for the seeded
budget. -/
theorem cls_interval (hni : NoGap M b) : ∀ η : PSet.{u}, IsOrd η → Cls (B := seeded b) (cofI M) η := by
  intro η hη
  refine ⟨hη, fun μ hμ ζ hζ => ?_⟩
  have hμo : IsOrd μ := hη.succ.mem hμ
  refine Stable.of_nn (hμo.trichotomy (isOrd_rank b)) fun
    | .inl h => reachable_below M b hμo (mem_succ_of_mem h) hζ
    | .inr (.inl e) => reachable_below M b hμo (mem_succ_of_equiv e) hζ
    | .inr (.inr h) => reachable_cofI (B := seeded b) M hμo ⟨ζ, hζ⟩ (hni μ hμo h)

/-- **The interval bound.** -/
theorem ordBound_interval (hni : NoGap M b) (em : ∀ p : Prop, p ∨ ¬p) (s : PSet.{u})
    (φ : PSet.{u} → PSet.{u} → Prop)
    (φ_resp : ∀ {x x' y y' : PSet.{u}}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (φ_func : ∀ {x y y' : PSet.{u}}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (φ_ord : ∀ {x y : PSet.{u}}, x ∈ s → φ x y → IsOrd y) :
    ∃ κ : PSet.{u}, IsOrd κ ∧ ∀ x η, x ∈ s → φ x η → η ∈ κ :=
  ⟨ordBound (B := seeded b) (cofI_resp M) (cls_interval M b hni) em s φ φ_resp φ_func φ_ord,
   isOrd_ordBound (B := seeded b) (cofI_resp M) (cls_interval M b hni) em s φ φ_resp φ_func φ_ord,
   fun _ _ hx h => mem_ordBound_of (B := seeded b) (cofI_resp M) (cls_interval M b hni) em s φ
     φ_resp φ_func φ_ord hx h⟩

/-! ### Explicit consequences -/

theorem K_initialAt (em : ∀ p : Prop, p ∨ ¬p) : InitialAt K.{u,v+1} := fun _ _ hδ hf => K_initial em hδ hf

theorem omega_mem_K : lift.{u,v+1} omega.{u} ∈ K.{u,v+1} := lift_mem_K isOrd_omega

/-- **`K` is a strong limit** against relational injections into subsets of powersets of its
members. -/
theorem K_strongLimit (em : ∀ p : Prop, p ∨ ¬p) : StrongLimitAt K.{u,v+1} := by
  intro lam θ P f hlam hθ hP hf
  refine Stable.of_nn (mem_K.1 hlam) fun ⟨l, hl, e⟩ => ?_
  have hsub : ∀ w, w ∈ P → w ∈ lift.{u,v+1} (powerset l) := fun w hw =>
    (mem_congr_right ((powerset_congr e).trans (lift_powerset l).symm)).1 (hP w hw)
  have h := mem_lift_wfBound em hθ (hf.mono hsub)
  exact isOrd_K.trans _ (lift_mem_K (isOrd_wfBound _)) θ h

/-- **`K` is regular** against all upper set-coded functions, under the interval hypothesis and
excluded middle: the function is pulled back to a lower ordinal relation on the lower
representative of its domain and bounded natively. -/
theorem K_regular_of_interval (hni : NoGap M b) (em : ∀ p : Prop, p ∨ ¬p) : RegularAt K.{u,v+1} := by
  intro δ f hδ hf
  refine Stable.of_nn (mem_K.1 hδ) fun ⟨d, hd, ed⟩ => ?_
  -- the pulled-back relation on the lower representative of the domain
  let φ : PSet.{u} → PSet.{u} → Prop := fun x η => IsOrd η ∧ ¬¬∃ y, pair (lift.{u,v+1} x) y ∈ f ∧ y ≈ lift.{u,v+1} η
  have ⟨κ, hκ, hb⟩ := ordBound_interval M b hni em d φ
    (fun ex eη ⟨ho, h⟩ => ⟨ho.resp eη, nn_map (fun ⟨y, hp, ey⟩ =>
      ⟨y, (mem_congr_left (pair_congr (lift_congr ex) (Equiv.refl _))).1 hp, ey.trans (lift_congr eη)⟩) h⟩)
    (fun _ ⟨_, h⟩ ⟨_, h'⟩ => Stable.of_nn h fun ⟨y, hp, ey⟩ => Stable.of_nn h' fun ⟨y', hp', ey'⟩ =>
      lift_equiv.1 ((ey.symm.trans (hf.2.1 _ _ _ hp hp')).trans ey'))
    (fun _ h => h.1)
  refine nn_intro ⟨lift.{u,v+1} κ, lift_mem_K hκ, fun x y hp => ?_⟩
  have ⟨hx, hy⟩ := hf.1 x y hp
  refine Stable.of_nn (mem_lift.1 ((mem_congr_right ed).1 hx)) fun ⟨x₀, hx₀, ex⟩ => ?_
  refine Stable.of_nn (mem_K.1 hy) fun ⟨η, hη, ey⟩ => ?_
  have hφ : φ x₀ η := ⟨hη, nn_intro ⟨y,
    (mem_congr_left (pair_congr ex (Equiv.refl _))).1 hp, ey⟩⟩
  exact (mem_congr_left ey).2 (lift_mem_of_mem (hb x₀ η hx₀ hφ))

/-- **Inaccessibility of `K`** against upper set-coded functions and injections, under the
interval hypothesis and excluded middle. -/
theorem K_inacc_of_interval (hni : NoGap M b) (em : ∀ p : Prop, p ∨ ¬p) :
    lift.{u,v+1} omega.{u} ∈ K.{u,v+1} ∧ InitialAt K.{u,v+1} ∧ RegularAt K.{u,v+1} ∧ StrongLimitAt K.{u,v+1} :=
  ⟨omega_mem_K, K_initialAt em, K_regular_of_interval M b hni em, K_strongLimit em⟩

/-- Ambient inaccessibility against all upper functions implies inaccessibility in `N`. -/
theorem inaccIn_of_ambient {N : PSet.{u} → Prop} {κ : PSet.{u}} (hκ : IsOrd κ) (hω : omega ∈ κ)
    (h1 : InitialAt κ) (h2 : RegularAt κ) (h3 : StrongLimitAt κ) : InaccIn N κ :=
  ⟨hκ, hω, fun δ f hδ _ hf => h1 δ f hδ hf, fun δ f hδ _ hf => h2 δ f hδ hf,
   fun lam θ P f hl hθ _ _ hP hf => h3 lam θ P f hl hθ hP hf⟩

/-- **The interval theorem.** Under excluded middle, for every lower set `b`, `N` has an
inaccessible `ρ` with `lift.{u,v+1} (rank b) < ρ ≤ K`: either some lifted lower ordinal above `rank b`
is inaccessible in `N`, or the interval hypothesis holds and `K` itself is. The remaining
premise is the interface `M` (an upper class with the stated laws), to be instantiated by the
constructible interpretation of a seeded model. -/
theorem inacc_interval (em : ∀ p : Prop, p ∨ ¬p) :
    ∃ ρ, M.N ρ ∧ lift.{u,v+1} (rank b) ∈ ρ ∧ (ρ ∈ K.{u,v+1} ∨ ρ ≈ K.{u,v+1}) ∧ InaccIn M.N ρ := by
  rcases em (∃ η : PSet.{u}, IsOrd η ∧ rank b ∈ η ∧ InaccIn M.N (lift.{u,v+1} η)) with ⟨η, hη, hb, hi⟩ | hn
  · exact ⟨lift.{u,v+1} η, M.N_lift_ord η hη, lift_mem_of_mem hb, .inl (lift_mem_K hη), hi⟩
  · have hni : NoGap M b := fun η hη hb hi => hn ⟨η, hη, hb, hi⟩
    have ⟨hω, h1, h2, h3⟩ := K_inacc_of_interval M b hni em
    refine ⟨K, M.N_K, ?_, .inr (Equiv.refl _), inaccIn_of_ambient isOrd_K
      ((mem_congr_left lift_omega).1 hω) h1 h2 h3⟩
    exact lift_mem_K (isOrd_rank b)
/-- The interval theorem in the concrete common class `L t`. The upper seed `t`
remains the same for every lower-universe invocation. -/
theorem inacc_interval_seeded (t : PSet.{max u v + 1})
    (em : ∀ p : Prop, p ∨ ¬p) (ht : IsOrd t) (hK : K.{u,v+1} ∈ succ t)
    (s : PSet.{u}) :
    ∃ ρ, L t ρ ∧ lift.{u,v+1} (rank s) ∈ ρ ∧
      (ρ ∈ K.{u,v+1} ∨ ρ ≈ K.{u,v+1}) ∧ InaccIn (L t) ρ :=
  inacc_interval (upperModel_seeded t em ht hK) s em

/-- A witness at most the previous height precedes a witness strictly above that height. -/
theorem mem_of_interval_separation {ρ K ρ' : PSet.{u}} (hρ' : IsOrd ρ')
    (hρ : ρ ∈ K ∨ ρ ≈ K) (hK : K ∈ ρ') : ρ ∈ ρ' := by
  cases hρ with
  | inl h => exact hρ'.trans K hK ρ h
  | inr e => exact (mem_congr_left e).2 hK

#print axioms inacc_interval
#print axioms inacc_interval_seeded
#print axioms mem_of_interval_separation

end PSet.Multi
