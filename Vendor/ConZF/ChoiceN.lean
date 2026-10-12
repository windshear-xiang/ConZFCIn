import Vendor.ConZF.Programs
/-!
Choice and the least cofinal graph from the program minimum (conzf20, con32 §3–5). The
constructible class is its own constructible universe (`constr_constr`), so every member of
`N := Constr M` is the denotation of a program of `N`. The shortlex minimum of the successful
programs for a fixed native condition is a first-order definable selector: for the choice
axiom the condition is "denotes a member of `u`" (`Pick`), and the choice graph is one
Separation of the internal product `a × ⋃ a` (`valid_ac`); for the cofinality interface the
condition is "denotes a cofinal graph from `Q` to `ζ`" (`LeastCofN`), which satisfies the four
laws of `UpperModel`. With the classification fields already discharged, the constructible
upper class is an `UpperModel` with no further input (`upperModel_NL`), and
`con_ZFCI_of_em` states the conditional consistency of `ZFC + ∃ inaccessible` from excluded
middle alone.
-/
universe u

namespace PSet
open Fml CardF LF AssignF

/-- **The constructible class is its own constructible universe.** -/
theorem SynZF.constr_constr {M : PSet.{u} → Prop} (hM : SynZF M) (hN : SynZF (Constr M)) (x : PSet.{u}) :
    Constr (Constr M) x ↔ Constr M x :=
  ⟨fun h => SynZF.Constr.mem_class hN h, fun h => nn_map (fun ⟨α, A, hα, hA, hx⟩ =>
    ⟨α, A, hα, level_absolute hN hα (hM.constr_of_ord hα (hM.level_mem_class hA).1) hA, hx⟩) h⟩

/-- The denotation of a program of the class is in the class. -/
theorem SynZF.Den.mem_class {M : PSet.{u} → Prop} (hM : SynZF M) {c n y : PSet.{u}} (h : Den M c n y) : M y := by
  have := hM.stable y
  refine Stable.of_nn h fun ⟨S, hr, ht⟩ => ?_
  have := hM.stable S
  have hS : M S := Stable.of_nn hr fun ⟨g, hg, _, _, _, hn⟩ => (hM.toTransClass.of_pair_mem hg hn).2
  exact Stable.of_nn ht fun ⟨m, hm, _⟩ => (hM.toTransClass.of_pair_mem hS hm).2

instance {g Q ζ : PSet.{u+1}} : Stable (Cof g Q ζ) := inferInstanceAs (Stable (_ ∧ _ ∧ _))

theorem Cof.congr_cod {g Q ζ ζ' : PSet.{u+1}} (e : ζ ≈ ζ') (h : Cof g Q ζ) : Cof g Q ζ' :=
  ⟨fun x y hp => ⟨(h.1 x y hp).1, (mem_congr_right e).1 (h.1 x y hp).2⟩, h.2.1,
   fun ξ hξ => h.2.2 ξ ((mem_congr_right e).2 hξ)⟩

/-! ### The least cofinal graph -/

/-- `c` (of length `n`) denotes a cofinal graph from `Q` to `ζ`. -/
def CofHit (N : PSet.{u+1} → Prop) (c n Q ζ : PSet.{u+1}) : Prop := ¬¬∃ g, Den N c n g ∧ Cof g Q ζ

instance {N : PSet.{u+1} → Prop} {c n Q ζ : PSet.{u+1}} : Stable (CofHit N c n Q ζ) := inferInstanceAs (Stable (¬_))

theorem CofHit.congr {N : PSet.{u+1} → Prop} {c c' n n' Q ζ : PSet.{u+1}} (ec : c ≈ c') (en : n ≈ n') (h : CofHit N c n Q ζ) :
    CofHit N c' n' Q ζ :=
  nn_map (fun ⟨g, hd, hc⟩ => ⟨g, hd.congr ec en (Equiv.refl _), hc⟩) h

/-- **The least cofinal graph**: the denotation of the shortlex-least program denoting a cofinal
graph. -/
def LeastCofN (N : PSet.{u+1} → Prop) (f Q ζ : PSet.{u+1}) : Prop :=
  ¬¬∃ c n, N c ∧ IsOWord c n ∧ Den N c n f ∧ Cof f Q ζ ∧ ∀ d m, N d → IsOWord d m → WLt d m c n → ¬ CofHit N d m Q ζ

/-- Two programs equal up to bisimulation with equal-length words denote the same value. -/
theorem SynZF.den_unique_of_equiv {N : PSet.{u} → Prop} (hN : SynZF N) {c c' n n' y y' : PSet.{u}} (ec : c ≈ c')
    (ho : IsOWord c n) (ho' : IsOWord c' n') (h : Den N c n y) (h' : Den N c' n' y') : y ≈ y' := by
  have en : n ≈ n' := ho.2.1.dom_unique (ho'.2.1.congr ec.symm)
  refine Stable.of_nn (mem_omega.1 ho.1) fun ⟨K, eK⟩ => ?_
  exact SynZF.Den.unique hN ((ho.2.1).congr_dom eK) (h.congr (Equiv.refl _) eK (Equiv.refl _))
    (h'.congr ec.symm (en.symm.trans eK) (Equiv.refl _))

namespace SynZF
variable {N : PSet.{u+1} → Prop} (hN : SynZF N) (hself : ∀ x, N x → Constr N x)
include hN hself

theorem leastCofN_exists {Q ζ : PSet.{u+1}} (_hQ : N Q) (_hζ : N ζ) (_hζo : IsOrd ζ) (h : ¬¬∃ g, N g ∧ Cof g Q ζ) :
    ¬¬∃ f, N f ∧ LeastCofN N f Q ζ := by
  refine Stable.of_nn h fun ⟨g, hg, hc⟩ => ?_
  have h0 : ¬¬∃ c n, N c ∧ IsOWord c n ∧ CofHit N c n Q ζ :=
    nn_map (fun ⟨n, e, hp, ho, hd⟩ => ⟨pack n e, ofNat n, hp, ho, nn_intro ⟨g, hd, hc⟩⟩) (hN.program_of_constr (hself g hg))
  refine nn_bind (minWord (N := N) (fun c n => CofHit N c n Q ζ) (fun ec en k => k.congr ec en) h0)
    fun ⟨c, n, hcN, ho, hhit, hmin⟩ => ?_
  exact nn_map (fun ⟨f, hd, hcf⟩ => ⟨f, SynZF.Den.mem_class hN hd, nn_intro ⟨c, n, hcN, ho, hd, hcf, hmin⟩⟩) hhit

omit hself in
theorem leastCofN_unique {f f' Q ζ : PSet.{u+1}} (h : LeastCofN N f Q ζ) (h' : LeastCofN N f' Q ζ) : f ≈ f' := by
  refine Stable.of_nn h fun ⟨c, n, hc, ho, hd, hcf, hmin⟩ => Stable.of_nn h' fun ⟨c', n', hc', ho', hd', hcf', hmin'⟩ => ?_
  have ec : c ≈ c' := minWord_unique (χ := fun c n => CofHit N c n Q ζ) hc ho (nn_intro ⟨f, hd, hcf⟩) hmin hc' ho'
    (nn_intro ⟨f', hd', hcf'⟩) hmin'
  exact hN.den_unique_of_equiv ec ho ho' hd hd'

omit hN hself in
theorem leastCofN_resp {f Q Q' ζ ζ' : PSet.{u+1}} (eQ : Q ≈ Q') (eζ : ζ ≈ ζ') (h : LeastCofN N f Q ζ) : LeastCofN N f Q' ζ' :=
  nn_map (fun ⟨c, n, hc, ho, hd, hcf, hmin⟩ => ⟨c, n, hc, ho, hd, (hcf.congr_dom eQ).congr_cod eζ,
    fun d m hd' ho' hlt k => hmin d m hd' ho' hlt (nn_map (fun ⟨g, hg, hgc⟩ => ⟨g, hg, (hgc.congr_dom eQ.symm).congr_cod eζ.symm⟩) k)⟩) h

omit hN hself in
theorem leastCofN_cof {f Q ζ : PSet.{u+1}} (h : LeastCofN N f Q ζ) : Cof f Q ζ :=
  Stable.of_nn h fun ⟨_, _, _, _, _, hcf, _⟩ => hcf

end SynZF

/-! ### Choice -/

/-- `c` (of length `n`) denotes a member of `u`. -/
def Hit (N : PSet.{u} → Prop) (c n u : PSet.{u}) : Prop := ¬¬∃ y, Den N c n y ∧ y ∈ u

instance {N : PSet.{u} → Prop} {c n u : PSet.{u}} : Stable (Hit N c n u) := inferInstanceAs (Stable (¬_))

theorem Hit.congr_u {N : PSet.{u} → Prop} {c n u u' : PSet.{u}} (e : u ≈ u') (h : Hit N c n u) : Hit N c n u' :=
  nn_map (fun ⟨y, hd, hy⟩ => ⟨y, hd, (mem_congr_right e).1 hy⟩) h

theorem Hit.congr {N : PSet.{u} → Prop} {c c' n n' u : PSet.{u}} (ec : c ≈ c') (en : n ≈ n') (h : Hit N c n u) : Hit N c' n' u :=
  nn_map (fun ⟨y, hd, hy⟩ => ⟨y, hd.congr ec en (Equiv.refl _), hy⟩) h

/-- **The selector**: `y ∈ u` is denoted by the least program denoting a member of `u`. -/
def Pick (N : PSet.{u} → Prop) (u y : PSet.{u}) : Prop :=
  y ∈ u ∧ ¬¬∃ c n, N c ∧ IsOWord c n ∧ Den N c n y ∧ Hit N c n u ∧ ∀ d m, N d → IsOWord d m → WLt d m c n → ¬ Hit N d m u

namespace LF

/-- `∃ y, den c n y ∧ y ∈ u`. Variables `c n u w`. -/
def hitF (c n u w : Nat) : Fml := ex (and (denF (c+1) (n+1) 0 (w+1)) (mem 0 (u+1)))

/-- The selector formula. Variables `u y w`. Under the two existentials the environment is
`[n, c, u, y, w, …]`; under the two universals `[m, d, n, c, u, y, w, …]`. -/
def pickF (u y w : Nat) : Fml :=
  and (mem y u) (ex (ex (and (owordF 1 0 (w+2)) (and (denF 1 0 (y+2) (w+2)) (and (hitF 1 0 (u+2) (w+2))
    (all (all (imp (owordF 1 0 (w+4)) (imp (wltF 1 0 3 2) (neg (hitF 1 0 (u+4) (w+4))))))))))))

/-- The choice-graph Separation matrix: `z = ⟨u, y⟩ ∧ pick u y`, under `[y, u, z, P, a, b, w]`
after two existentials from `[z, P, a, b, w]`. -/
def choiceSepF : Fml := ex (ex (and (pairF 2 1 0) (pickF 1 0 6)))

end LF

namespace SynZF
variable {N : PSet.{u} → Prop} (hN : SynZF N) {E : Nat → PSet.{u}} (hE : ∀ i, N (E i))
include hN hE

theorem sat_hitF (c n u w : Nat) (hw : E w ≈ PSet.omega) : Sat N (hitF c n u w) E ↔ Hit N (E c) (E n) (E u) := by
  refine sat_ex.trans (nn_congr ⟨fun ⟨y, hy, hs⟩ => ?_, fun ⟨y, hd, hy⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨y, (hN.sat_denF (Env.cons_mem hy hE) (c+1) (n+1) 0 (w+1) hw).1 h1, h2⟩
  · have hyN := hN.trans (hE u) hy
    exact ⟨y, hyN, sat_and.2 ⟨(hN.sat_denF (Env.cons_mem hyN hE) (c+1) (n+1) 0 (w+1) hw).2 hd, hy⟩⟩

/-- **The selector bridge.** -/
theorem sat_pickF (u y w : Nat) (hw : E w ≈ PSet.omega) : Sat N (pickF u y w) E ↔ Pick N (E u) (E y) := by
  have hT := hN.toTransClass
  refine sat_and.trans (and_congr Iff.rfl (sat_ex.trans ⟨fun k => nn_bind k fun ⟨c, hc, k⟩ => nn_map (fun ⟨n, hn, hs⟩ => ?_) (sat_ex.1 k),
    fun k => nn_map (fun ⟨c, n, hc, ho, hd, hh, hmin⟩ => ?_) k⟩))
  · have hE2 := Env.cons_mem hn (Env.cons_mem hc hE)
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h3, h4⟩ := sat_and.1 h2
    have ⟨h5, h6⟩ := sat_and.1 h4
    refine ⟨c, n, hc, (hT.sat_owordF hE2 1 0 (w+2) hw).1 h1, (hN.sat_denF hE2 1 0 (y+2) (w+2) hw).1 h3,
      (hN.sat_hitF hE2 1 0 (u+2) (w+2) hw).1 h5, fun d m hd ho hlt k => ?_⟩
    have hmN : N m := hN.trans hN.omega ho.1
    have hE4 := Env.cons_mem hmN (Env.cons_mem hd hE2)
    exact h6 d hd m hmN ((hT.sat_owordF hE4 1 0 (w+4) hw).2 ho) ((hT.sat_wltF hE4 1 0 3 2).2 hlt) ((hN.sat_hitF hE4 1 0 (u+4) (w+4) hw).2 k)
  · have hnN : N n := hN.trans hN.omega ho.1
    have hE2 := Env.cons_mem hnN (Env.cons_mem hc hE)
    refine ⟨c, hc, sat_ex.2 (nn_intro ⟨n, hnN, sat_and.2 ⟨(hT.sat_owordF hE2 1 0 (w+2) hw).2 ho, sat_and.2
      ⟨(hN.sat_denF hE2 1 0 (y+2) (w+2) hw).2 hd, sat_and.2 ⟨(hN.sat_hitF hE2 1 0 (u+2) (w+2) hw).2 hh, fun d hd m hmN h1 h2 k => ?_⟩⟩⟩⟩)⟩
    have hE4 := Env.cons_mem hmN (Env.cons_mem hd hE2)
    exact hmin d m hd ((hT.sat_owordF hE4 1 0 (w+4) hw).1 h1) ((hT.sat_wltF hE4 1 0 3 2).1 h2) ((hN.sat_hitF hE4 1 0 (u+4) (w+4) hw).1 k)

end SynZF

namespace SynZF
variable {N : PSet.{u} → Prop} (hN : SynZF N) (hself : ∀ x, N x → Constr N x)
include hN hself

/-- Every inhabited member of the class has a selected member. -/
theorem pick_exists {u : PSet.{u}} (hu : N u) (h : ¬¬∃ y, N y ∧ y ∈ u) : ¬¬∃ y, N y ∧ Pick N u y := by
  refine Stable.of_nn h fun ⟨y, hy, hyu⟩ => ?_
  have h0 : ¬¬∃ c n, N c ∧ IsOWord c n ∧ Hit N c n u :=
    nn_map (fun ⟨n, e, hp, ho, hd⟩ => ⟨pack n e, ofNat n, hp, ho, nn_intro ⟨y, hd, hyu⟩⟩) (hN.program_of_constr (hself y hy))
  refine nn_bind (minWord (N := N) (fun c n => Hit N c n u) (fun ec en k => k.congr ec en) h0)
    fun ⟨c, n, hcN, ho, hhit, hmin⟩ => ?_
  exact nn_map (fun ⟨y', hd, hy'⟩ => ⟨y', hN.trans hu hy', hy', nn_intro ⟨c, n, hcN, ho, hd, hhit, hmin⟩⟩) hhit

omit hself in
theorem pick_unique {u y y' : PSet.{u}} (h : Pick N u y) (h' : Pick N u y') : y ≈ y' := by
  refine Stable.of_nn h.2 fun ⟨c, n, hc, ho, hd, hh, hmin⟩ => Stable.of_nn h'.2 fun ⟨c', n', hc', ho', hd', hh', hmin'⟩ => ?_
  have ec : c ≈ c' := minWord_unique (χ := fun c n => Hit N c n u) hc ho hh hmin hc' ho' hh' hmin'
  exact hN.den_unique_of_equiv ec ho ho' hd hd'

/-- **Choice is valid in a self-constructible class.** -/
theorem valid_ac : Valid N ac := by
  intro e he a ha hinh
  have hT := hN.toTransClass
  let b := PSet.sUnion a
  have hb : N b := hN.sUnion ha
  refine Stable.of_nn (hN.prodM ha hb) fun ⟨P, hP, hPm⟩ => ?_
  let E := Env.cons P (Env.cons a (Env.cons b envω))
  have hE : ∀ i, N (E i) := Env.cons_mem hP (Env.cons_mem ha (Env.cons_mem hb hN.envω_mem))
  let f := PSet.sep (fun z => Sat N choiceSepF (Env.cons z E)) P
  have hf : N f := hN.sepM choiceSepF hE
  have hfm : ∀ z, z ∈ f ↔ z ∈ P ∧ Sat N choiceSepF (Env.cons z E) := fun z =>
    mem_sep fun _ _ e' k => Sat.resp _ (Env.cons_resp e' fun _ => Equiv.refl _) k
  have read : ∀ z, N z → (Sat N choiceSepF (Env.cons z E) ↔ ¬¬∃ u y, N u ∧ N y ∧ z ≈ PSet.pair u y ∧ Pick N u y) := by
    intro z hz
    have hE1 := Env.cons_mem hz hE
    refine sat_ex.trans ⟨fun k => nn_bind k fun ⟨u, hu, k⟩ => nn_map (fun ⟨y, hy, hs⟩ => ?_) (sat_ex.1 k),
      fun k => nn_map (fun ⟨u, y, hu, hy, ez, hp⟩ => ?_) k⟩
    · have hE3 := Env.cons_mem hy (Env.cons_mem hu hE1)
      have ⟨h1, h2⟩ := sat_and.1 hs
      exact ⟨u, y, hu, hy, (hT.sat_pairF hE3 2 1 0).1 h1, (hN.sat_pickF hE3 1 0 6 (Equiv.refl _)).1 h2⟩
    · have hE3 := Env.cons_mem hy (Env.cons_mem hu hE1)
      exact ⟨u, hu, sat_ex.2 (nn_intro ⟨y, hy, sat_and.2 ⟨(hT.sat_pairF hE3 2 1 0).2 ez, (hN.sat_pickF hE3 1 0 6 (Equiv.refl _)).2 hp⟩⟩)⟩
  refine sat_ex.2 (nn_intro ⟨f, hf, sat_and.2 ⟨fun u hu hua => ?_, fun u hu y hy z hz h1 h2 => ?_⟩⟩)
  · -- totality
    have hinh' : ¬¬∃ y, N y ∧ y ∈ u := nn_map (fun ⟨y, hy, hyu⟩ => ⟨y, hy, hyu⟩) (sat_ex.1 (hinh u hu hua))
    refine sat_ex.2 (nn_map (fun ⟨y, hy, hp⟩ => ?_) (hN.pick_exists hself hu hinh'))
    have hyb : y ∈ b := mem_sUnion.2 (nn_intro ⟨u, hua, hp.1⟩)
    have hzN : N (PSet.pair u y) := hN.pair hu hy
    have hzf : PSet.pair u y ∈ f := (hfm _).2 ⟨(hPm _).2 (nn_intro ⟨u, y, hua, hyb, Equiv.refl _⟩),
      (read _ hzN).2 (nn_intro ⟨u, y, hu, hy, Equiv.refl _, hp⟩)⟩
    exact ⟨y, hy, sat_and.2 ⟨(hT.sat_pairMemF (Env.cons_mem hy (Env.cons_mem hu (Env.cons_mem hf he))) 2 1 0).2 hzf, hp.1⟩⟩
  · -- functionality
    have hE3 := Env.cons_mem hz (Env.cons_mem hy (Env.cons_mem hu (Env.cons_mem hf he)))
    have k1 := (hT.sat_pairMemF hE3 3 2 1).1 h1
    have k2 := (hT.sat_pairMemF hE3 3 2 0).1 h2
    have hzN₁ : N (PSet.pair u y) := hN.trans hP ((hfm _).1 k1).1
    have hzN₂ : N (PSet.pair u z) := hN.trans hP ((hfm _).1 k2).1
    refine Stable.of_nn ((read _ hzN₁).1 ((hfm _).1 k1).2) fun ⟨u₁, y₁, _, _, e₁, p₁⟩ =>
      Stable.of_nn ((read _ hzN₂).1 ((hfm _).1 k2).2) fun ⟨u₂, y₂, _, _, e₂, p₂⟩ => ?_
    have ⟨eu₁, ey₁⟩ := pair_inj e₁
    have ⟨eu₂, ey₂⟩ := pair_inj e₂
    have p₂' : Pick N u₁ y₂ := ⟨(mem_congr_right (eu₂.symm.trans eu₁)).1 p₂.1,
      nn_map (fun ⟨c, n, hc, ho, hd, hh, hmin⟩ => ⟨c, n, hc, ho, hd, Hit.congr_u (eu₂.symm.trans eu₁) hh, fun d m hd ho hlt k =>
        hmin d m hd ho hlt (Hit.congr_u (eu₁.symm.trans eu₂) k)⟩) p₂.2⟩
    exact ey₁.trans ((hN.pick_unique p₁ p₂').trans ey₂.symm)

end SynZF

/-! ### The assembly -/

/-- The constructible upper class is self-constructible. -/
theorem NL_self (hMU : SynZF MU.{u}) : ∀ x, NL.{u} x → Constr NL.{u} x :=
  fun x hx => (hMU.constr_constr (synZF_NL hMU) x).2 hx

/-- **The upper model**, with no further input: the least cofinal graph is the program minimum. -/
def upperModel_NL (hMU : SynZF MU.{u}) : UpperModel.{u} :=
  upperModel_of_leastCof hMU (LeastCofN NL.{u}) (fun eQ eζ h => SynZF.leastCofN_resp eQ eζ h)
    (fun h h' => SynZF.leastCofN_unique (synZF_NL hMU) h h') (fun h => SynZF.leastCofN_cof h)
    (fun hQ hζ hζo h => SynZF.leastCofN_exists (synZF_NL hMU) (NL_self hMU) hQ hζ hζo h)

/-- **Choice holds in the constructible upper class.** -/
theorem valid_ac_NL (hMU : SynZF MU.{u}) : Valid NL.{u} ac := (synZF_NL hMU).valid_ac (NL_self hMU)

/-- **Consistency of `ZFC + ∃ inaccessible` from excluded middle alone.** Excluded middle yields
the accessibility hypothesis of the upper universe, hence the seeded syntactic class `MU`; its
constructible class `NL` is a syntactic `ZFC` class that is an `UpperModel`, and the interval
theorem supplies the inaccessible. -/
theorem con_ZFCI_of_em (em : ∀ p : Prop, p ∨ ¬p) : Con ZFCI :=
  have hMU : SynZF MU.{0} := synZF_MU_of_acc (accHyp_of_not_not_em fun k => k em)
  con_ZFCI em (upperModel_NL hMU) (synZF_NL hMU).toTransClass (synZF_NL hMU).valid (valid_ac_NL hMU)

/-- info: 'PSet.SynZF.valid_ac' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.valid_ac
/-- info: 'PSet.SynZF.leastCofN_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.leastCofN_exists
/-- info: 'PSet.upperModel_NL' does not depend on any axioms -/
#guard_msgs in #print axioms upperModel_NL
/-- info: 'PSet.con_ZFCI_of_em' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_em

end PSet
