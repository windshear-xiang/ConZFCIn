import Vendor.ConZF.Cofinality
import Vendor.ConZF.Acc
import Vendor.ConZF.Seeded
import Vendor.ConZF.MixedHartogs
/-!
The interval argument (con23) and the explicit consequences at the two-level interface.

**Seeded interval reachability.** With the seeded budget around a lower set `b` and the same
cofinality interpreter, every nonzero ordinal `η ≤ rank b` is reached by the identity graph on
`lift η`, a partial cofinal relation from `lift (succ (rank b))`, whose domain code lies in the
seeded budget at every source (`reachable_below`); above `rank b` the three cases of
`reachable_cofI` apply. Hence, if no lift of a lower ordinal above `rank b` is inaccessible in
`N`, every lower ordinal is hereditarily good for the seeded budget (`cls_interval`), and under
excluded middle every functional ordinal relation on a lower source has a native bound
(`ordBound_interval`).

**Explicit consequences.** Stated with set-theoretic definitions in the upper universe:
`IsFun` (total set-coded functions), `RegularAt κ` (every function from a member of `κ` into
`κ` has range inside a member of `κ`), `StrongLimitAt κ` (every ordinal injecting relationally
into a subset of the powerset of a member of `κ` is a member of `κ`), `InitialAt κ` (no
relational injection into a member). `K` is initial and a strong limit unconditionally under
excluded middle (`K_strongLimit`), with `ω < K`; and it is regular against all upper set-coded
functions under the interval hypothesis (`K_regular_of_interval`), by pulling the function
back to a lower ordinal relation and bounding it natively. Together: `K_inacc_of_interval`.
These are statements about the ambient upper universe; the internal versions in `N` follow
for any transitive class containing the relevant functions.
-/
universe u

namespace PSet

variable (M : UpperModel.{u}) (b : PSet.{u})

/-- The identity graph on a lifted ordinal `η ≤ rank b` is a partial cofinal relation from
`lift (succ (rank b))`. -/
theorem cof_idGraph {η : PSet.{u}} (hle : η ∈ succ (rank b)) :
    Cof (idGraph (lift η)) (lift (succ (rank b))) (lift η) := by
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
      (nn_intro ⟨idGraph (lift η), M.N_idGraph η hη, cof_idGraph b hle⟩)⟩⟩

/-- **The interval hypothesis** for `b`: no lift of a lower ordinal above `rank b` is
inaccessible in `N`. -/
def NoGap : Prop := ∀ η : PSet.{u}, IsOrd η → rank b ∈ η → ¬ InaccIn M.N (lift η)

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

/-- `κ` is regular against set-coded functions: every function from a member of `κ` into `κ`
has its values inside a member of `κ`. -/
def RegularAt (κ : PSet.{u}) : Prop :=
  ∀ δ f, δ ∈ κ → IsFun f δ κ → ¬¬∃ β, β ∈ κ ∧ ∀ x y, pair x y ∈ f → y ∈ β

/-- `κ` is a strong limit against relational injections: every ordinal injecting relationally
into a subset of the powerset of a member of `κ` is a member of `κ`. -/
def StrongLimitAt (κ : PSet.{u}) : Prop :=
  ∀ lam θ P f, lam ∈ κ → IsOrd θ → (∀ w, w ∈ P → w ∈ powerset lam) → IsInjRel θ P f → θ ∈ κ

/-- `κ` is initial: no relational injection into a member. -/
def InitialAt (κ : PSet.{u}) : Prop := ∀ δ f, δ ∈ κ → ¬ IsInjRel κ δ f

theorem K_initialAt (em : ∀ p : Prop, p ∨ ¬p) : InitialAt K.{u} := fun _ _ hδ hf => K_initial em hδ hf

theorem omega_mem_K : lift omega.{u} ∈ K.{u} := lift_mem_K isOrd_omega

/-- **`K` is a strong limit** against relational injections into subsets of powersets of its
members. -/
theorem K_strongLimit (em : ∀ p : Prop, p ∨ ¬p) : StrongLimitAt K.{u} := by
  intro lam θ P f hlam hθ hP hf
  refine Stable.of_nn (mem_K.1 hlam) fun ⟨l, hl, e⟩ => ?_
  have hsub : ∀ w, w ∈ P → w ∈ lift (powerset l) := fun w hw =>
    (mem_congr_right ((powerset_congr e).trans (lift_powerset l).symm)).1 (hP w hw)
  have h := mem_lift_wfBound em hθ (hf.mono hsub)
  exact isOrd_K.trans _ (lift_mem_K (isOrd_wfBound _)) θ h

/-- **`K` is regular** against all upper set-coded functions, under the interval hypothesis and
excluded middle: the function is pulled back to a lower ordinal relation on the lower
representative of its domain and bounded natively. -/
theorem K_regular_of_interval (hni : NoGap M b) (em : ∀ p : Prop, p ∨ ¬p) : RegularAt K.{u} := by
  intro δ f hδ hf
  refine Stable.of_nn (mem_K.1 hδ) fun ⟨d, hd, ed⟩ => ?_
  -- the pulled-back relation on the lower representative of the domain
  let φ : PSet.{u} → PSet.{u} → Prop := fun x η => IsOrd η ∧ ¬¬∃ y, pair (lift x) y ∈ f ∧ y ≈ lift η
  have ⟨κ, hκ, hb⟩ := ordBound_interval M b hni em d φ
    (fun ex eη ⟨ho, h⟩ => ⟨ho.resp eη, nn_map (fun ⟨y, hp, ey⟩ =>
      ⟨y, (mem_congr_left (pair_congr (lift_congr ex) (Equiv.refl _))).1 hp, ey.trans (lift_congr eη)⟩) h⟩)
    (fun _ ⟨_, h⟩ ⟨_, h'⟩ => Stable.of_nn h fun ⟨y, hp, ey⟩ => Stable.of_nn h' fun ⟨y', hp', ey'⟩ =>
      lift_equiv.1 ((ey.symm.trans (hf.2.1 _ _ _ hp hp')).trans ey'))
    (fun _ h => h.1)
  refine nn_intro ⟨lift κ, lift_mem_K hκ, fun x y hp => ?_⟩
  have ⟨hx, hy⟩ := hf.1 x y hp
  refine Stable.of_nn (mem_lift.1 ((mem_congr_right ed).1 hx)) fun ⟨x₀, hx₀, ex⟩ => ?_
  refine Stable.of_nn (mem_K.1 hy) fun ⟨η, hη, ey⟩ => ?_
  have hφ : φ x₀ η := ⟨hη, nn_intro ⟨y,
    (mem_congr_left (pair_congr ex (Equiv.refl _))).1 hp, ey⟩⟩
  exact (mem_congr_left ey).2 (lift_mem_of_mem (hb x₀ η hx₀ hφ))

/-- **Inaccessibility of `K`** against upper set-coded functions and injections, under the
interval hypothesis and excluded middle. -/
theorem K_inacc_of_interval (hni : NoGap M b) (em : ∀ p : Prop, p ∨ ¬p) :
    lift omega.{u} ∈ K.{u} ∧ InitialAt K.{u} ∧ RegularAt K.{u} ∧ StrongLimitAt K.{u} :=
  ⟨omega_mem_K, K_initialAt em, K_regular_of_interval M b hni em, K_strongLimit em⟩

/-- Ambient inaccessibility against all upper functions implies inaccessibility in `N`. -/
theorem inaccIn_of_ambient {N : PSet.{u+1} → Prop} {κ : PSet.{u+1}} (hκ : IsOrd κ) (hω : omega ∈ κ)
    (h1 : InitialAt κ) (h2 : RegularAt κ) (h3 : StrongLimitAt κ) : InaccIn N κ :=
  ⟨hκ, hω, fun δ f hδ _ hf => h1 δ f hδ hf, fun δ f hδ _ hf => h2 δ f hδ hf,
   fun lam θ P f hl hθ _ _ hP hf => h3 lam θ P f hl hθ hP hf⟩

/-- **The interval theorem.** Under excluded middle, for every lower set `b`, `N` has an
inaccessible `ρ` with `lift (rank b) < ρ ≤ K`: either some lifted lower ordinal above `rank b`
is inaccessible in `N`, or the interval hypothesis holds and `K` itself is. The remaining
premise is the interface `M` (an upper class with the stated laws), to be instantiated by the
constructible interpretation of a seeded model. -/
theorem inacc_interval (em : ∀ p : Prop, p ∨ ¬p) :
    ∃ ρ, M.N ρ ∧ lift (rank b) ∈ ρ ∧ (ρ ∈ K.{u} ∨ ρ ≈ K.{u}) ∧ InaccIn M.N ρ := by
  rcases em (∃ η : PSet.{u}, IsOrd η ∧ rank b ∈ η ∧ InaccIn M.N (lift η)) with ⟨η, hη, hb, hi⟩ | hn
  · exact ⟨lift η, M.N_lift_ord η hη, lift_mem_of_mem hb, .inl (lift_mem_K hη), hi⟩
  · have hni : NoGap M b := fun η hη hb hi => hn ⟨η, hη, hb, hi⟩
    have ⟨hω, h1, h2, h3⟩ := K_inacc_of_interval M b hni em
    refine ⟨K, M.N_K, ?_, .inr (Equiv.refl _), inaccIn_of_ambient isOrd_K
      ((mem_congr_left lift_omega).1 hω) h1 h2 h3⟩
    exact lift_mem_K (isOrd_rank b)

/-- info: 'PSet.inacc_interval' does not depend on any axioms -/
#guard_msgs in #print axioms inacc_interval
/-- info: 'PSet.cls_interval' does not depend on any axioms -/
#guard_msgs in #print axioms cls_interval
/-- info: 'PSet.K_inacc_of_interval' does not depend on any axioms -/
#guard_msgs in #print axioms K_inacc_of_interval

/-! ### The interval theorem from negative accessibility of `K` (con33 §3) -/

/-- **The interval bound from lower accessibility**: the exact image supplied by the
definability rule's Replacement, with its rank as the bound. -/
theorem ordBound_interval_nn (hni : NoGap M b) (hacc : AccHyp.{u}) (s : PSet.{u})
    (φ : PSet.{u} → PSet.{u} → Prop)
    (φ_resp : ∀ {x x' y y' : PSet.{u}}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (φ_func : ∀ {x y y' : PSet.{u}}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (φ_ord : ∀ {x y : PSet.{u}}, x ∈ s → φ x y → IsOrd y) :
    ¬¬∃ κ : PSet.{u}, IsOrd κ ∧ ∀ x η, x ∈ s → φ x η → η ∈ κ := by
  have hrepl := (reach_rule (B := seeded b) (cofI_resp M) s).replacement s rfl φ φ_resp φ_func
    (fun hx h => cls_interval M b hni _ (φ_ord hx h)) (hacc _)
  refine nn_map (fun ⟨R, hR⟩ => ⟨rank R, isOrd_rank R, fun x η hx h => ?_⟩) hrepl
  exact (mem_congr_left (φ_ord hx h).rank_equiv).1 (rank_mem ((hR η).2 (nn_intro ⟨x, hx, h⟩)))

/-- **`K` is regular** against all upper set-coded functions, under the interval hypothesis and
lower accessibility. -/
theorem K_regular_of_interval_acc (hni : NoGap M b) (hacc : AccHyp.{u}) : RegularAt K.{u} := by
  intro δ f hδ hf
  refine Stable.of_nn (mem_K.1 hδ) fun ⟨d, hd, ed⟩ => ?_
  let φ : PSet.{u} → PSet.{u} → Prop := fun x η => IsOrd η ∧ ¬¬∃ y, pair (lift x) y ∈ f ∧ y ≈ lift η
  refine Stable.of_nn (ordBound_interval_nn M b hni hacc d φ
    (fun ex eη ⟨ho, h⟩ => ⟨ho.resp eη, nn_map (fun ⟨y, hp, ey⟩ =>
      ⟨y, (mem_congr_left (pair_congr (lift_congr ex) (Equiv.refl _))).1 hp, ey.trans (lift_congr eη)⟩) h⟩)
    (fun _ ⟨_, h⟩ ⟨_, h'⟩ => Stable.of_nn h fun ⟨y, hp, ey⟩ => Stable.of_nn h' fun ⟨y', hp', ey'⟩ =>
      lift_equiv.1 ((ey.symm.trans (hf.2.1 _ _ _ hp hp')).trans ey'))
    (fun _ h => h.1)) fun ⟨κ, hκ, hb⟩ => ?_
  refine nn_intro ⟨lift κ, lift_mem_K hκ, fun x y hp => ?_⟩
  have ⟨hx, hy⟩ := hf.1 x y hp
  refine Stable.of_nn (mem_lift.1 ((mem_congr_right ed).1 hx)) fun ⟨x₀, hx₀, ex⟩ => ?_
  refine Stable.of_nn (mem_K.1 hy) fun ⟨η, hη, ey⟩ => ?_
  have hφ : φ x₀ η := ⟨hη, nn_intro ⟨y,
    (mem_congr_left (pair_congr ex (Equiv.refl _))).1 hp, ey⟩⟩
  exact (mem_congr_left ey).2 (lift_mem_of_mem (hb x₀ η hx₀ hφ))

theorem K_initialAt_of_nnacc (hK : NNAccK.{u}) : InitialAt K.{u} := fun _ _ hδ hf => K_initial_of_nnacc hK hδ hf

/-- **`K` is a strong limit** from negative accessibility of `K`: an injecting ordinal is below
`K` by comparison and restriction. -/
theorem K_strongLimit_of_nnacc (hK : NNAccK.{u}) : StrongLimitAt K.{u} := by
  intro lam θ P f hlam hθ hP hf
  refine Stable.of_nn (mem_K.1 hlam) fun ⟨l, hl, e⟩ => ?_
  have hsub : ∀ w, w ∈ P → w ∈ lift (powerset l) := fun w hw =>
    (mem_congr_right ((powerset_congr e).trans (lift_powerset l).symm)).1 (hP w hw)
  exact mem_K_of_injRel hK hθ (hf.mono hsub)

/-- Lower membership accessibility from actual accessibility of `K`, through the rank map. -/
theorem lower_acc_of_acc_K (hK : Acc (fun a b : PSet.{u+1} => a ∈ b) K.{u}) : ∀ x : PSet.{u}, Acc (· ∈ ·) x := by
  have pull : ∀ y : PSet.{u+1}, Acc (· ∈ ·) y → ∀ x : PSet.{u}, lift x ≈ y → Acc (· ∈ ·) x := by
    intro y hy
    induction hy with
    | intro y _ ih =>
      intro x e
      exact ⟨x, fun z hz => ih (lift z) ((mem_congr_right e).1 (lift_mem_of_mem hz)) z (Equiv.refl _)⟩
  exact fun x => acc_of_rank (pull _ (hK.inv (lift_mem_K (isOrd_rank x))) _ (Equiv.refl _))

/-- Lower `AccHyp` from negative accessibility of `K`. -/
theorem accHyp_of_nnAccK (hK : NNAccK.{u}) : AccHyp.{u} :=
  accHyp_of_mem_wf (nn_map lower_acc_of_acc_K hK)

/-- **The interval theorem from negative accessibility of `K`**, without excluded middle: the
conclusion is negatively existential, so the split on the existence of a lifted inaccessible
above `rank b` is by stability. -/
theorem inacc_interval_nnacc (hK : NNAccK.{u}) :
    ¬¬∃ ρ, M.N ρ ∧ lift (rank b) ∈ ρ ∧ (ρ ∈ K.{u} ∨ ρ ≈ K.{u}) ∧ InaccIn M.N ρ := by
  refine Stable.by_cases (∃ η : PSet.{u}, IsOrd η ∧ rank b ∈ η ∧ InaccIn M.N (lift η))
    (fun ⟨η, hη, hb, hi⟩ => nn_intro ⟨lift η, M.N_lift_ord η hη, lift_mem_of_mem hb, .inl (lift_mem_K hη), hi⟩) fun hn => ?_
  have hni : NoGap M b := fun η hη hb hi => hn ⟨η, hη, hb, hi⟩
  refine nn_intro ⟨K, M.N_K, lift_mem_K (isOrd_rank b), .inr (Equiv.refl _), inaccIn_of_ambient isOrd_K
    ((mem_congr_left lift_omega).1 omega_mem_K) (K_initialAt_of_nnacc hK) (K_regular_of_interval_acc M b hni (accHyp_of_nnAccK hK))
    (K_strongLimit_of_nnacc hK)⟩

/-- info: 'PSet.inacc_interval_nnacc' does not depend on any axioms -/
#guard_msgs in #print axioms inacc_interval_nnacc
/-- info: 'PSet.K_regular_of_interval_acc' does not depend on any axioms -/
#guard_msgs in #print axioms K_regular_of_interval_acc

end PSet
