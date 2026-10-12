import Vendor.ConZF.Step
/-!
The validity/truth history (gate 2, checkpoint 3). The step of `Step.lean` is functional and
total on a `SynZF` class, so the ω-recursion of `OmegaRec.lean` from the start `⟨∅, ∅⟩` gives
the history `H` (the sequence specified by `seqF stepF`), whose row at `d` is the state
`⟨V_d, T_d⟩`. Native height `ht` counts nested constructors. The invariants, by induction on
`d` along the recursion equations: a row `⟨enc φ, ofNat n⟩` is in `V_d` exactly when
`ht φ ≤ d` and `Bound n φ` (`valid_iff`); every row of `V_d` negatively decodes to a native
formula and a numeral (`valid_decode`); and a row `⟨enc φ, pack n e⟩` with entries in `A` is in
`T_d` exactly when `ht φ ≤ d`, `Bound n φ`, and `φ` holds in the set structure `A` at `e`
(`truth_iff`).
-/
universe u

namespace PSet
open Fml CardF RecF CodeF AssignF StepF

/-- Native height. -/
def Fml.ht : Fml → Nat
  | .mem _ _ | .eq _ _ | .fls => 1
  | .imp p q => nmax (ht p) (ht q) + 1
  | .all p => ht p + 1

theorem Fml.ht_pos : ∀ φ : Fml, 0 < ht φ
  | .mem _ _ | .eq _ _ | .fls => Nat.one_pos
  | .imp _ _ => Nat.succ_pos _
  | .all _ => Nat.succ_pos _

/-- Uniqueness of the domain of an assignment. -/
theorem IsAssign.dom_unique {A e n n' : PSet.{u}} (h : IsAssign A e n) (h' : IsAssign A e n') : n ≈ n' :=
  ext fun i => ⟨fun hi => Stable.of_nn (h.2.2.1 i hi) fun ⟨_, hv⟩ => Stable.of_nn (h'.2.1 _ hv)
      fun ⟨_, _, hi', _, e'⟩ => (mem_congr_left (pair_inj e').1).2 hi',
    fun hi => Stable.of_nn (h'.2.2.1 i hi) fun ⟨_, hv⟩ => Stable.of_nn (h.2.1 _ hv)
      fun ⟨_, _, hi', _, e'⟩ => (mem_congr_left (pair_inj e').1).2 hi'⟩

/-- Uniqueness of the cons. -/
theorem IsCons.unique {u u' x e : PSet.{u}} (h : IsCons u x e) (h' : IsCons u' x e) : u ≈ u' := by
  refine ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · refine Stable.of_nn (h.2.2.2 q hq) fun
      | .inl e1 => (mem_congr_left e1).2 h'.1
      | .inr h2 => Stable.of_nn h2 fun ⟨i, v, hiv, e2⟩ => (mem_congr_left e2).2 (h'.2.1 i v hiv)
  · refine Stable.of_nn (h'.2.2.2 q hq) fun
      | .inl e1 => (mem_congr_left e1).2 h.1
      | .inr h2 => Stable.of_nn h2 fun ⟨i, v, hiv, e2⟩ => (mem_congr_left e2).2 (h.2.1 i v hiv)

/-! ### Tag arithmetic on codes -/

/-- The tag of a code determines the constructor: the payload of a `mem` code. -/
theorem enc_mem_eq {i j : Nat} {t : Nat} {p : PSet.{u}} (h : enc (.mem i j) ≈ pair (ofNat t) p) :
    t = 0 ∧ p ≈ pair (ofNat i) (ofNat j) :=
  have ⟨e1, e2⟩ := pair_inj h
  ⟨(ofNat_inj e1).symm, e2.symm⟩

theorem enc_eq_eq {i j : Nat} {t : Nat} {p : PSet.{u}} (h : enc (.eq i j) ≈ pair (ofNat t) p) :
    t = 1 ∧ p ≈ pair (ofNat i) (ofNat j) :=
  have ⟨e1, e2⟩ := pair_inj h
  ⟨(ofNat_inj e1).symm, e2.symm⟩

theorem enc_fls_eq {t : Nat} {p : PSet.{u}} (h : enc .fls ≈ pair (ofNat t) p) : t = 2 ∧ p ≈ empty :=
  have ⟨e1, e2⟩ := pair_inj h
  ⟨(ofNat_inj e1).symm, e2.symm⟩

theorem enc_imp_eq {φ ψ : Fml} {t : Nat} {p : PSet.{u}} (h : enc (.imp φ ψ) ≈ pair (ofNat t) p) :
    t = 3 ∧ p ≈ pair (enc φ) (enc ψ) :=
  have ⟨e1, e2⟩ := pair_inj h
  ⟨(ofNat_inj e1).symm, e2.symm⟩

theorem enc_all_eq {φ : Fml} {t : Nat} {p : PSet.{u}} (h : enc (.all φ) ≈ pair (ofNat t) p) :
    t = 4 ∧ p ≈ enc φ :=
  have ⟨e1, e2⟩ := pair_inj h
  ⟨(ofNat_inj e1).symm, e2.symm⟩

instance stable_of_decidable {p : Prop} [Decidable p] : Stable p :=
  ⟨fun h => match (inferInstance : Decidable p) with
    | .isTrue hp => hp
    | .isFalse hn => (h hn).elim⟩

theorem bound_stable' : ∀ (k : Nat) (φ : Fml), Stable (Bound k φ)
  | _, .mem _ _ => inferInstanceAs (Stable (_ ∧ _))
  | _, .eq _ _ => inferInstanceAs (Stable (_ ∧ _))
  | _, .fls => inferInstanceAs (Stable True)
  | k, .imp φ ψ =>
    have := bound_stable' k φ
    have := bound_stable' k ψ
    inferInstanceAs (Stable (Bound k φ ∧ Bound k ψ))
  | k, .all φ => bound_stable' (k+1) φ

instance {k : Nat} {φ : Fml} : Stable (Bound k φ) := bound_stable' k φ

theorem nmax_le {a b c : Nat} : nmax a b ≤ c ↔ a ≤ c ∧ b ≤ c := by
  induction a generalizing b c with
  | zero => exact ⟨fun h => ⟨Nat.zero_le _, h⟩, fun h => h.2⟩
  | succ a ih =>
    cases b with
    | zero => exact ⟨fun h => ⟨h, Nat.zero_le _⟩, fun h => h.1⟩
    | succ b =>
      cases c with
      | zero => exact ⟨fun h => (Nat.not_succ_le_zero _ h).elim, fun h => (Nat.not_succ_le_zero _ h.1).elim⟩
      | succ c => exact ⟨fun h => have ⟨h1, h2⟩ := ih.1 (Nat.le_of_succ_le_succ h)
          ⟨Nat.succ_le_succ h1, Nat.succ_le_succ h2⟩,
        fun ⟨h1, h2⟩ => Nat.succ_le_succ (ih.2 ⟨Nat.le_of_succ_le_succ h1, Nat.le_of_succ_le_succ h2⟩)⟩

theorem mem_ofNat_iff {i n : Nat} : ofNat.{u} i ∈ ofNat n ↔ i < n :=
  ⟨fun h => Stable.of_nn (mem_ofNat.1 h) fun ⟨_, hm, e⟩ => ofNat_inj e ▸ hm,
   fun h => mem_ofNat.2 (nn_intro ⟨i, h, Equiv.refl _⟩)⟩

/-! ### The scope invariant -/

/-- The scope invariant at stage `d`: exact rows at native codes, and decoding of every row. -/
def InvV (d : Nat) (V : PSet.{u}) : Prop :=
  (∀ (φ : Fml) (n : Nat), pair (enc φ) (ofNat n) ∈ V ↔ φ.ht ≤ d ∧ Bound n φ) ∧
  (∀ r, r ∈ V → ¬¬∃ (φ : Fml) (n : Nat), r ≈ pair (enc φ) (ofNat n))

theorem invV_zero : InvV 0 empty :=
  ⟨fun φ _ => ⟨fun h => (not_mem_empty _ h).elim, fun ⟨h, _⟩ => (Nat.not_succ_le_zero _ (Nat.lt_of_lt_of_le (ht_pos φ) h)).elim⟩,
   fun r hr => (not_mem_empty r hr).elim⟩

/-- The tag of a native formula's code. -/
def Fml.tag : Fml → Nat
  | .mem _ _ => 0
  | .eq _ _ => 1
  | .fls => 2
  | .imp _ _ => 3
  | .all _ => 4

theorem enc_tag {φ : Fml} {t : Nat} {p : PSet.{u}} (h : enc φ ≈ pair (ofNat t) p) : t = φ.tag := by
  cases φ with
  | mem _ _ => exact (enc_mem_eq h).1
  | eq _ _ => exact (enc_eq_eq h).1
  | fls => exact (enc_fls_eq h).1
  | imp _ _ => exact (enc_imp_eq h).1
  | all _ => exact (enc_all_eq h).1

/-- **The scope body at a native code**, given the invariant for the old table. -/
theorem vbody_enc {d : Nat} {V : PSet.{u}} (hV : InvV d V) (φ : Fml) (n : Nat) :
    VBody V (enc φ) (ofNat n) ↔ φ.ht ≤ d + 1 ∧ Bound n φ := by
  constructor
  · rintro ⟨_, h⟩
    refine Stable.of_nn h fun
      | .inl h => Stable.of_nn h fun ⟨i, j, hi, hj, hc⟩ => Stable.of_nn hc fun
        | .inl e => atom0 e hi hj
        | .inr e => atom1 e hi hj
      | .inr h => Stable.of_nn h fun
        | .inl e => bot e
        | .inr h => Stable.of_nn h fun
          | .inl h => Stable.of_nn h fun ⟨p, r, e, hp, hr⟩ => impc e hp hr
          | .inr h => Stable.of_nn h fun ⟨p, e, hp⟩ => allc e hp
  · rintro ⟨hh, hb⟩
    refine ⟨ofNat_mem_omega n, ?_⟩
    cases φ with
    | mem i j => exact nn_intro (.inl (nn_intro ⟨ofNat i, ofNat j, mem_ofNat_iff.2 hb.1, mem_ofNat_iff.2 hb.2,
        nn_intro (.inl (Equiv.refl _))⟩))
    | eq i j => exact nn_intro (.inl (nn_intro ⟨ofNat i, ofNat j, mem_ofNat_iff.2 hb.1, mem_ofNat_iff.2 hb.2,
        nn_intro (.inr (Equiv.refl _))⟩))
    | fls => exact nn_intro (.inr (nn_intro (.inl (Equiv.refl _))))
    | imp φ ψ =>
      have ⟨h1, h2⟩ := nmax_le.1 (Nat.le_of_succ_le_succ hh)
      exact nn_intro (.inr (nn_intro (.inr (nn_intro (.inl (nn_intro ⟨enc φ, enc ψ, Equiv.refl _,
        (hV.1 φ n).2 ⟨h1, hb.1⟩, (hV.1 ψ n).2 ⟨h2, hb.2⟩⟩))))))
    | all φ =>
      exact nn_intro (.inr (nn_intro (.inr (nn_intro (.inr (nn_intro ⟨enc φ, Equiv.refl _,
        (hV.1 φ (n+1)).2 ⟨Nat.le_of_succ_le_succ hh, hb⟩⟩))))))
where
  atom0 {i j : PSet.{u}} (e : enc φ ≈ pair (ofNat 0) (pair i j)) (hi : i ∈ ofNat n) (hj : j ∈ ofNat n) :
      φ.ht ≤ d + 1 ∧ Bound n φ := by
    have ht := enc_tag e
    cases φ with
    | mem i₀ j₀ =>
      have ⟨ei, ej⟩ := pair_inj (enc_mem_eq e).2
      exact ⟨Nat.succ_le_succ (Nat.zero_le d), mem_ofNat_iff.1 ((mem_congr_left ei).1 hi),
        mem_ofNat_iff.1 ((mem_congr_left ej).1 hj)⟩
    | eq _ _ => exact absurd ht (show (0 : Nat) ≠ 1 by decide)
    | fls => exact absurd ht (show (0 : Nat) ≠ 2 by decide)
    | imp _ _ => exact absurd ht (show (0 : Nat) ≠ 3 by decide)
    | all _ => exact absurd ht (show (0 : Nat) ≠ 4 by decide)
  atom1 {i j : PSet.{u}} (e : enc φ ≈ pair (ofNat 1) (pair i j)) (hi : i ∈ ofNat n) (hj : j ∈ ofNat n) :
      φ.ht ≤ d + 1 ∧ Bound n φ := by
    have ht := enc_tag e
    cases φ with
    | eq i₀ j₀ =>
      have ⟨ei, ej⟩ := pair_inj (enc_eq_eq e).2
      exact ⟨Nat.succ_le_succ (Nat.zero_le d), mem_ofNat_iff.1 ((mem_congr_left ei).1 hi),
        mem_ofNat_iff.1 ((mem_congr_left ej).1 hj)⟩
    | mem _ _ => exact absurd ht (show (1 : Nat) ≠ 0 by decide)
    | fls => exact absurd ht (show (1 : Nat) ≠ 2 by decide)
    | imp _ _ => exact absurd ht (show (1 : Nat) ≠ 3 by decide)
    | all _ => exact absurd ht (show (1 : Nat) ≠ 4 by decide)
  bot (e : enc φ ≈ pair (ofNat 2) empty) : φ.ht ≤ d + 1 ∧ Bound n φ := by
    have ht := enc_tag e
    cases φ with
    | fls => exact ⟨Nat.succ_le_succ (Nat.zero_le d), trivial⟩
    | mem _ _ => exact absurd ht (show (2 : Nat) ≠ 0 by decide)
    | eq _ _ => exact absurd ht (show (2 : Nat) ≠ 1 by decide)
    | imp _ _ => exact absurd ht (show (2 : Nat) ≠ 3 by decide)
    | all _ => exact absurd ht (show (2 : Nat) ≠ 4 by decide)
  impc {p r : PSet.{u}} (e : enc φ ≈ pair (ofNat 3) (pair p r)) (hp : pair p (ofNat n) ∈ V) (hr : pair r (ofNat n) ∈ V) :
      φ.ht ≤ d + 1 ∧ Bound n φ := by
    have ht := enc_tag e
    cases φ with
    | imp φ ψ =>
      have ⟨ep, er⟩ := pair_inj (enc_imp_eq e).2
      have hp' : pair (enc φ) (ofNat n) ∈ V := (mem_congr_left (pair_congr ep (Equiv.refl _))).1 hp
      have hr' : pair (enc ψ) (ofNat n) ∈ V := (mem_congr_left (pair_congr er (Equiv.refl _))).1 hr
      have h1 := (hV.1 φ n).1 hp'
      have h2 := (hV.1 ψ n).1 hr'
      exact ⟨Nat.succ_le_succ (nmax_le.2 ⟨h1.1, h2.1⟩), h1.2, h2.2⟩
    | mem _ _ => exact absurd ht (show (3 : Nat) ≠ 0 by decide)
    | eq _ _ => exact absurd ht (show (3 : Nat) ≠ 1 by decide)
    | fls => exact absurd ht (show (3 : Nat) ≠ 2 by decide)
    | all _ => exact absurd ht (show (3 : Nat) ≠ 4 by decide)
  allc {p : PSet.{u}} (e : enc φ ≈ pair (ofNat 4) p) (hp : pair p (succ (ofNat n)) ∈ V) :
      φ.ht ≤ d + 1 ∧ Bound n φ := by
    have ht := enc_tag e
    cases φ with
    | all φ =>
      have ep : p ≈ enc φ := (enc_all_eq e).2
      have hp' : pair (enc φ) (ofNat (n+1)) ∈ V := (mem_congr_left (pair_congr ep (Equiv.refl _))).1 hp
      have h1 := (hV.1 φ (n+1)).1 hp'
      exact ⟨Nat.succ_le_succ h1.1, h1.2⟩
    | mem _ _ => exact absurd ht (show (4 : Nat) ≠ 0 by decide)
    | eq _ _ => exact absurd ht (show (4 : Nat) ≠ 1 by decide)
    | fls => exact absurd ht (show (4 : Nat) ≠ 2 by decide)
    | imp _ _ => exact absurd ht (show (4 : Nat) ≠ 3 by decide)

/-- **Decoding**: every row admitted by the scope body decodes to a native code and numeral. -/
theorem vbody_decode {d : Nat} {V : PSet.{u}} (hV : InvV d V) {q n : PSet.{u}} (hb : VBody V q n) :
    ¬¬∃ (φ : Fml) (m : Nat), q ≈ enc φ ∧ n ≈ ofNat m := by
  refine nn_bind (mem_omega.1 hb.1) fun ⟨m, em⟩ => ?_
  refine nn_bind hb.2 fun
    | .inl h => nn_bind h fun ⟨i, j, hi, hj, hc⟩ => nn_bind (mem_omega.1 (isOrd_omega.trans _ hb.1 i hi)) fun ⟨i₀, ei⟩ =>
        nn_bind (mem_omega.1 (isOrd_omega.trans _ hb.1 j hj)) fun ⟨j₀, ej⟩ => nn_map (fun
          | .inl e => ⟨.mem i₀ j₀, m, e.trans (pair_congr (Equiv.refl _) (pair_congr ei ej)), em⟩
          | .inr e => ⟨.eq i₀ j₀, m, e.trans (pair_congr (Equiv.refl _) (pair_congr ei ej)), em⟩) hc
    | .inr h => nn_bind h fun
      | .inl e => nn_intro ⟨.fls, m, e, em⟩
      | .inr h => nn_bind h fun
        | .inl h => nn_bind h fun ⟨p, r, e, hp, hr⟩ =>
            nn_bind (hV.2 _ hp) fun ⟨φ, _, e₁⟩ => nn_map (fun ⟨ψ, _, e₂⟩ =>
              ⟨.imp φ ψ, m, e.trans (pair_congr (Equiv.refl _) (pair_congr (pair_inj e₁).1 (pair_inj e₂).1)), em⟩) (hV.2 _ hr)
        | .inr h => nn_bind h fun ⟨p, e, hp⟩ => nn_map (fun ⟨φ, _, e₁⟩ =>
            ⟨.all φ, m, e.trans (pair_congr (Equiv.refl _) (pair_inj e₁).1), em⟩) (hV.2 _ hp)

/-- The scope invariant advances along the step. -/
theorem invV_step {d : Nat} {A E V T V' T' : PSet.{u}} (hV : InvV d V) (st : IsStep A E V T V' T') :
    InvV (d+1) V' :=
  ⟨fun φ n => (st.2.1 _ _).trans (vbody_enc hV φ n),
   fun r hr => nn_bind (st.1 r hr) fun ⟨q, n, _, e⟩ =>
     nn_map (fun ⟨φ, m, eqq, en⟩ => ⟨φ, m, e.trans (pair_congr eqq en)⟩)
       (vbody_decode hV ((st.2.1 q n).1 ((mem_congr_left e).1 hr)))⟩

/-! ### The totalized step and the history -/

namespace StepF
/-- `s` is a pair. -/
def isPairF (s : Nat) : Fml := ex (ex (pairF (s+2) 1 0))
/-- The totalized step: on pairs the step, elsewhere the output is `∅`. -/
def totStepF : Fml := or (and (isPairF 0) stepF) (and (neg (isPairF 0)) (emptyF 1))
end StepF

theorem IsStep.congr_out {A E V T V' V₂' T' T₂' : PSet.{u}} (ev : V' ≈ V₂') (et : T' ≈ T₂')
    (h : IsStep A E V T V' T') : IsStep A E V T V₂' T₂' :=
  ⟨fun r hr => h.1 r ((mem_congr_right ev).2 hr), fun q n => (mem_congr_right ev).symm.trans (h.2.1 q n),
   fun r hr => h.2.2.1 r ((mem_congr_right et).2 hr),
   fun q e he => (mem_congr_right et).symm.trans ((h.2.2.2 q e he).trans ⟨TBody.congr_table ev, TBody.congr_table ev.symm⟩)⟩

theorem IsStep.congr_in {A E V V₂ T T₂ V' T' : PSet.{u}} (ev : V ≈ V₂) (et : T ≈ T₂)
    (h : IsStep A E V T V' T') : IsStep A E V₂ T₂ V' T' :=
  ⟨h.1, fun q n => (h.2.1 q n).trans ⟨fun hb => ⟨hb.1, nn_map (fun
      | .inl h => .inl h
      | .inr h => .inr (nn_map (fun
        | .inl e => .inl e
        | .inr h => .inr (nn_map (fun
          | .inl h => .inl (nn_map (fun ⟨p, r, e, hp, hr⟩ => ⟨p, r, e, (mem_congr_right ev).1 hp, (mem_congr_right ev).1 hr⟩) h)
          | .inr h => .inr (nn_map (fun ⟨p, e, hp⟩ => ⟨p, e, (mem_congr_right ev).1 hp⟩) h)) h)) h)) hb.2⟩,
     fun hb => ⟨hb.1, nn_map (fun
      | .inl h => .inl h
      | .inr h => .inr (nn_map (fun
        | .inl e => .inl e
        | .inr h => .inr (nn_map (fun
          | .inl h => .inl (nn_map (fun ⟨p, r, e, hp, hr⟩ => ⟨p, r, e, (mem_congr_right ev).2 hp, (mem_congr_right ev).2 hr⟩) h)
          | .inr h => .inr (nn_map (fun ⟨p, e, hp⟩ => ⟨p, e, (mem_congr_right ev).2 hp⟩) h)) h)) h)) hb.2⟩⟩,
   h.2.2.1, fun q e he => (h.2.2.2 q e he).trans ⟨tbody_congr et, tbody_congr et.symm⟩⟩
where
  tbody_congr {A E V' T T₂ q e : PSet.{u}} (et : T ≈ T₂) (h : TBody A E V' T q e) : TBody A E V' T₂ q e :=
    nn_map (fun ⟨n, ha, hv, hb⟩ => ⟨n, ha, hv, nn_map (fun
      | .inl h => .inl h
      | .inr h => .inr (nn_map (fun
        | .inl h => .inl h
        | .inr h => .inr (nn_map (fun
          | .inl h => .inl (nn_map (fun ⟨p, r, e', hpr⟩ => ⟨p, r, e', fun hp =>
              (mem_congr_right et).1 (hpr ((mem_congr_right et).2 hp))⟩) h)
          | .inr h => .inr (nn_map (fun ⟨p, e', hall⟩ => ⟨p, e', fun x hx =>
              nn_map (fun ⟨u, hu, hc, hpu⟩ => ⟨u, hu, hc, (mem_congr_right et).1 hpu⟩) (hall x hx)⟩) h)) h)) h)) hb⟩) h

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M) {A Ea : PSet.{u}} (hA : M A) (hEa : M Ea)
include hM

/-- The parameter environment of the step: `A`, the assignment set, `ω`. -/
def stepEnv (A Ea : PSet.{u}) : Nat → PSet.{u} := Env.cons A (Env.cons Ea (Env.cons PSet.omega envω))

include hA hEa in
theorem stepEnv_mem : ∀ i, M (stepEnv A Ea i) := Env.cons_mem hA (Env.cons_mem hEa (Env.cons_mem hM.omega hM.envω_mem))

include hA hEa in
/-- The totalized step, read at a member `x` and a member `y`. -/
theorem sat_totStepF {x y : PSet.{u}} (hx : M x) (hy : M y) :
    Sat M totStepF (Env.cons x (Env.cons y (stepEnv A Ea))) ↔
      ¬¬((¬¬∃ V T, M V ∧ M T ∧ x ≈ PSet.pair V T) ∧ Sat M stepF (Env.cons x (Env.cons y (stepEnv A Ea))) ∨
        (¬ ¬¬∃ V T, M V ∧ M T ∧ x ≈ PSet.pair V T) ∧ y ≈ PSet.empty) := by
  have hT := hM.toTransClass
  have hE : ∀ i, M (Env.cons x (Env.cons y (stepEnv A Ea)) i) := Env.cons_mem hx (Env.cons_mem hy (hM.stepEnv_mem hA hEa))
  have hp : Sat M (isPairF 0) (Env.cons x (Env.cons y (stepEnv A Ea))) ↔ ¬¬∃ V T, M V ∧ M T ∧ x ≈ PSet.pair V T := by
    refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨V, hV, h⟩ => nn_map (fun ⟨T, hT', h⟩ => ?_) (sat_ex.1 h),
      fun h => nn_bind h fun ⟨V, T, hV, hT', e⟩ => ?_⟩
    · exact ⟨V, T, hV, hT', (hT.sat_pairF (Env.cons_mem hT' (Env.cons_mem hV hE)) 2 1 0).1 h⟩
    · exact nn_intro ⟨V, hV, sat_ex.2 (nn_intro ⟨T, hT', (hT.sat_pairF (Env.cons_mem hT' (Env.cons_mem hV hE)) 2 1 0).2 e⟩)⟩
  refine sat_or.trans (nn_congr (or_congr (sat_and.trans (and_congr hp Iff.rfl))
    (sat_and.trans (and_congr (sat_neg.trans (not_congr hp)) (hT.sat_emptyF hE 1)))))

include hA hEa in
/-- **Functionality of the totalized step.** -/
theorem totStep_fun : ∀ x y y', M x → M y → M y' →
    Sat M totStepF (Env.cons x (Env.cons y (stepEnv A Ea))) →
    Sat M totStepF (Env.cons x (Env.cons y' (stepEnv A Ea))) → y ≈ y' := by
  intro x y y' hx hy hy' h1 h2
  have hT := hM.toTransClass
  refine Stable.of_nn ((hM.sat_totStepF hA hEa hx hy).1 h1) fun
    | .inl ⟨_, hs⟩ => Stable.of_nn ((hM.sat_totStepF hA hEa hx hy').1 h2) fun
      | .inl ⟨_, hs'⟩ => ?_
      | .inr ⟨hn, _⟩ => (hn (Stable.of_nn ((hT.sat_stepFormula hM.empty hM.succ_mem hx hy hA hEa hM.omega hM.envω_mem).1 hs)
          fun ⟨V, T, _, _, hV, hT', _, _, e, _, _⟩ => nn_intro ⟨V, T, hV, hT', e⟩)).elim
    | .inr ⟨hn, e⟩ => Stable.of_nn ((hM.sat_totStepF hA hEa hx hy').1 h2) fun
      | .inl ⟨hp, _⟩ => (hn hp).elim
      | .inr ⟨_, e'⟩ => e.trans e'.symm
  refine Stable.of_nn ((hT.sat_stepFormula hM.empty hM.succ_mem hx hy hA hEa hM.omega hM.envω_mem).1 hs)
    fun ⟨V, T, V', T', _, _, _, _, ex, ey, st⟩ =>
    Stable.of_nn ((hT.sat_stepFormula hM.empty hM.succ_mem hx hy' hA hEa hM.omega hM.envω_mem).1 hs')
    fun ⟨V₂, T₂, V₂', T₂', _, _, _, _, ex₂, ey₂, st₂⟩ => ?_
  have ⟨ev, et⟩ := pair_inj (ex.symm.trans ex₂)
  have ⟨ev', et'⟩ := (st.congr_in ev et).unique st₂
  exact ey.trans ((pair_congr ev' et').trans ey₂.symm)

include hA hEa in
/-- **Totality of the totalized step.** -/
theorem totStep_tot : ∀ x, M x → ¬¬∃ y, M y ∧ Sat M totStepF (Env.cons x (Env.cons y (stepEnv A Ea))) := by
  intro x hx
  have hT := hM.toTransClass
  refine Stable.by_cases (¬¬∃ V T, M V ∧ M T ∧ x ≈ PSet.pair V T) (fun hp => ?_) fun hn => ?_
  · refine nn_bind hp fun ⟨V, T, hV, hT', e⟩ => nn_map (fun ⟨V', T', hV', hT'', st⟩ => ?_) (hM.step_exists hA hEa hV hT')
    have hy : M (PSet.pair V' T') := hM.pair hV' hT''
    refine ⟨PSet.pair V' T', hy, (hM.sat_totStepF hA hEa hx hy).2 (nn_intro (.inl ⟨hp, ?_⟩))⟩
    exact (hT.sat_stepFormula hM.empty hM.succ_mem hx hy hA hEa hM.omega hM.envω_mem).2
      (nn_intro ⟨V, T, V', T', hV, hT', hV', hT'', e, Equiv.refl _, st⟩)
  · exact nn_intro ⟨PSet.empty, hM.empty, (hM.sat_totStepF hA hEa hx hM.empty).2 (nn_intro (.inr ⟨hn, Equiv.refl _⟩))⟩

/-- The start state. -/
def startState : PSet.{u} := PSet.pair PSet.empty PSet.empty

include hA hEa in
/-- **The history exists** in the class. -/
theorem history_exists : ¬¬∃ H, M H ∧ Sat M (seqF totStepF) (Env.cons H (Env.cons startState (Env.cons PSet.omega (stepEnv A Ea)))) :=
  hM.seq_exists totStepF (hM.stepEnv_mem hA hEa) (hM.totStep_fun hA hEa) (hM.pair hM.empty hM.empty)

/-! ### Rows of the history -/

/-- The row of the history at the numeral `d`. -/
def Row (H : PSet.{u}) (d : Nat) (V T : PSet.{u}) : Prop := PSet.pair (ofNat d) (PSet.pair V T) ∈ H

variable {H : PSet.{u}} (hH : M H)
  (hsat : Sat M (seqF totStepF) (Env.cons H (Env.cons startState (Env.cons PSet.omega (stepEnv A Ea)))))
include hA hEa hH hsat

theorem history_spec :
    (∀ q, q ∈ H → ¬¬∃ n v, n ∈ PSet.omega ∧ q ≈ PSet.pair n v) ∧
    PSet.pair PSet.empty startState ∈ H ∧
    (∀ n v v', PSet.pair n v ∈ H → PSet.pair n v' ∈ H → v ≈ v') ∧
    (∀ n, n ∈ PSet.omega → ¬¬∃ v, PSet.pair n v ∈ H) ∧
    (∀ n v w, PSet.pair n v ∈ H → PSet.pair (succ n) w ∈ H →
      Sat M totStepF (Env.cons v (Env.cons w (stepEnv A Ea)))) :=
  hM.seq_spec totStepF (hM.stepEnv_mem hA hEa) (hM.totStep_fun hA hEa) (hM.totStep_tot hA hEa)
    (hM.pair hM.empty hM.empty) hH hsat

theorem row_unique {d : Nat} {V T V' T' : PSet.{u}} (h : Row H d V T) (h' : Row H d V' T') : V ≈ V' ∧ T ≈ T' :=
  pair_inj ((hM.history_spec hA hEa hH hsat).2.2.1 _ _ _ h h')

/-- Consecutive rows are related by the step. -/
theorem row_step {d : Nat} {V T V' T' : PSet.{u}} (hV : M V) (hT : M T) (hV' : M V') (hT' : M T')
    (h : Row H d V T) (h' : Row H (d+1) V' T') : IsStep A Ea V T V' T' := by
  have hTr := hM.toTransClass
  have hs := (hM.history_spec hA hEa hH hsat).2.2.2.2 _ _ _ h h'
  have hx : M (PSet.pair V T) := hM.pair hV hT
  have hy : M (PSet.pair V' T') := hM.pair hV' hT'
  refine Stable.of_nn ((hM.sat_totStepF hA hEa hx hy).1 hs) fun
    | .inl ⟨_, hs⟩ => ?_
    | .inr ⟨hn, _⟩ => (hn (nn_intro ⟨V, T, hV, hT, Equiv.refl _⟩)).elim
  refine Stable.of_nn ((hTr.sat_stepFormula hM.empty hM.succ_mem hx hy hA hEa hM.omega hM.envω_mem).1 hs)
    fun ⟨V₀, T₀, V₀', T₀', _, _, _, _, ex, ey, st⟩ => ?_
  have ⟨ev, et⟩ := pair_inj ex
  have ⟨ev', et'⟩ := pair_inj ey
  exact (st.congr_in ev.symm et.symm).congr_out ev'.symm et'.symm

/-- Every stage has a row, whose tables are in the class. -/
theorem row_exists : ∀ d : Nat, ¬¬∃ V T, M V ∧ M T ∧ Row H d V T
  | 0 => nn_intro ⟨PSet.empty, PSet.empty, hM.empty, hM.empty, (hM.history_spec hA hEa hH hsat).2.1⟩
  | d+1 => by
    have spec := hM.history_spec hA hEa hH hsat
    refine nn_bind (row_exists d) fun ⟨V, T, hV, hT, hr⟩ => ?_
    refine nn_bind (spec.2.2.2.1 (ofNat (d+1)) (ofNat_mem_omega _)) fun ⟨w, hw⟩ => ?_
    have hs := spec.2.2.2.2 _ _ _ hr hw
    have hx : M (PSet.pair V T) := hM.pair hV hT
    have hwM : M w := (hM.toTransClass.of_pair_mem hH hw).2
    refine Stable.of_nn ((hM.sat_totStepF hA hEa hx hwM).1 hs) fun
      | .inl ⟨_, hs⟩ => ?_
      | .inr ⟨hn, _⟩ => (hn (nn_intro ⟨V, T, hV, hT, Equiv.refl _⟩)).elim
    refine nn_map (fun ⟨_, _, V', T', _, _, hV', hT', _, ey, _⟩ => ⟨V', T', hV', hT', ?_⟩)
      ((hM.toTransClass.sat_stepFormula hM.empty hM.succ_mem hx hwM hA hEa hM.omega hM.envω_mem).1 hs)
    exact (mem_congr_left (pair_congr (Equiv.refl _) ey)).1 hw

/-! ### The truth invariant -/

/-- The truth invariant at stage `d` over the domain `A`: exact rows at native codes and
packaged environments with entries in `A`. -/
def InvT (A : PSet.{u}) (d : Nat) (T : PSet.{u}) : Prop :=
  ∀ (φ : Fml) (n : Nat) (e : Nat → PSet.{u}), (∀ i, i < n → e i ∈ A) →
    (PSet.pair (enc φ) (pack n e) ∈ T ↔ φ.ht ≤ d ∧ Bound n φ ∧ Sat (fun z => z ∈ A) φ e)

omit hM hA hEa hH hsat in
theorem invT_zero : InvT A 0 PSet.empty := fun φ _ _ _ =>
  ⟨fun h => (not_mem_empty _ h).elim, fun ⟨h, _⟩ => (Nat.not_succ_le_zero _ (Nat.lt_of_lt_of_le (ht_pos φ) h)).elim⟩

variable (hEam : ∀ e', e' ∈ Ea ↔ (M e' ∧ ¬¬∃ n, IsAssign A e' n))

omit hEa hH hsat in
include hEam in
/-- Packages with entries in `A` lie in the assignment set. -/
theorem pack_mem_Ea {n : Nat} {e : Nat → PSet.{u}} (he : ∀ i, i < n → e i ∈ A) : pack n e ∈ Ea :=
  (hEam _).2 ⟨hM.pack_mem n fun i hi => hM.trans hA (he i hi), nn_intro ⟨ofNat n, isAssign_pack n he⟩⟩

omit hEa hH hsat in
include hEam in
/-- **The truth body at a native code and a packaged environment.** -/
theorem tbody_enc {d : Nat} {V' T : PSet.{u}} (hV' : InvV (d+1) V') (hT : InvT A d T)
    (φ : Fml) (n : Nat) (e : Nat → PSet.{u}) (he : ∀ i, i < n → e i ∈ A) :
    TBody A Ea V' T (enc φ) (pack n e) ↔ φ.ht ≤ d + 1 ∧ Bound n φ ∧ Sat (fun z => z ∈ A) φ e := by
  constructor
  · intro h
    refine Stable.of_nn h fun ⟨n', ha, hv, hb⟩ => ?_
    have en : n' ≈ ofNat n := ha.dom_unique (isAssign_pack n he)
    have hv' : PSet.pair (enc φ) (ofNat n) ∈ V' := (mem_congr_left (pair_congr (Equiv.refl _) en)).1 hv
    have ⟨hh, hbd⟩ := (hV'.1 φ n).1 hv'
    refine ⟨hh, hbd, ?_⟩
    refine Stable.of_nn hb fun
      | .inl h => Stable.of_nn h fun ⟨i, j, x, y, ec, hix, hjy, hxy⟩ => ?_
      | .inr h => Stable.of_nn h fun
        | .inl h => Stable.of_nn h fun ⟨i, j, x, y, ec, hix, hjy, hxy⟩ => ?_
        | .inr h => Stable.of_nn h fun
          | .inl h => Stable.of_nn h fun ⟨p, r, ec, hpr⟩ => ?_
          | .inr h => Stable.of_nn h fun ⟨p, ec, hall⟩ => ?_
    · have ht := enc_tag ec
      cases φ with
      | mem i₀ j₀ =>
        have ⟨ei, ej⟩ := pair_inj (enc_mem_eq ec).2
        have hx : x ≈ e i₀ := (reads_pack hbd.1).1 ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 hix)
        have hy : y ≈ e j₀ := (reads_pack hbd.2).1 ((mem_congr_left (pair_congr ej (Equiv.refl _))).1 hjy)
        exact (mem_congr_right hy).1 ((mem_congr_left hx).1 hxy)
      | eq _ _ => exact absurd ht (show (0 : Nat) ≠ 1 by decide)
      | fls => exact absurd ht (show (0 : Nat) ≠ 2 by decide)
      | imp _ _ => exact absurd ht (show (0 : Nat) ≠ 3 by decide)
      | all _ => exact absurd ht (show (0 : Nat) ≠ 4 by decide)
    · have ht := enc_tag ec
      cases φ with
      | eq i₀ j₀ =>
        have ⟨ei, ej⟩ := pair_inj (enc_eq_eq ec).2
        have hx : x ≈ e i₀ := (reads_pack hbd.1).1 ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 hix)
        have hy : y ≈ e j₀ := (reads_pack hbd.2).1 ((mem_congr_left (pair_congr ej (Equiv.refl _))).1 hjy)
        exact hx.symm.trans (hxy.trans hy)
      | mem _ _ => exact absurd ht (show (1 : Nat) ≠ 0 by decide)
      | fls => exact absurd ht (show (1 : Nat) ≠ 2 by decide)
      | imp _ _ => exact absurd ht (show (1 : Nat) ≠ 3 by decide)
      | all _ => exact absurd ht (show (1 : Nat) ≠ 4 by decide)
    · have ht := enc_tag ec
      cases φ with
      | imp φ₁ φ₂ =>
        have ⟨ep, er⟩ := pair_inj (enc_imp_eq ec).2
        have ⟨h1, h2⟩ := nmax_le.1 (Nat.le_of_succ_le_succ hh)
        intro hs
        have hin : PSet.pair p (pack n e) ∈ T := (mem_congr_left (pair_congr ep.symm (Equiv.refl _))).1
          ((hT φ₁ n e he).2 ⟨h1, hbd.1, hs⟩)
        exact ((hT φ₂ n e he).1 ((mem_congr_left (pair_congr er (Equiv.refl _))).1 (hpr hin))).2.2
      | mem _ _ => exact absurd ht (show (3 : Nat) ≠ 0 by decide)
      | eq _ _ => exact absurd ht (show (3 : Nat) ≠ 1 by decide)
      | fls => exact absurd ht (show (3 : Nat) ≠ 2 by decide)
      | all _ => exact absurd ht (show (3 : Nat) ≠ 4 by decide)
    · have ht := enc_tag ec
      cases φ with
      | all φ₁ =>
        have ep : p ≈ enc φ₁ := (enc_all_eq ec).2
        intro x hx
        refine Stable.of_nn (hall x hx) fun ⟨u, _, hc, hpu⟩ => ?_
        have eu : u ≈ pack (n+1) (Env.cons x e) := hc.unique (isCons_pack n)
        have he' : ∀ i, i < n + 1 → Env.cons x e i ∈ A := fun i hi => by
          cases i with
          | zero => exact hx
          | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
        exact ((hT φ₁ (n+1) (Env.cons x e) he').1 ((mem_congr_left (pair_congr ep eu)).1 hpu)).2.2
      | mem _ _ => exact absurd ht (show (4 : Nat) ≠ 0 by decide)
      | eq _ _ => exact absurd ht (show (4 : Nat) ≠ 1 by decide)
      | fls => exact absurd ht (show (4 : Nat) ≠ 2 by decide)
      | imp _ _ => exact absurd ht (show (4 : Nat) ≠ 3 by decide)
  · rintro ⟨hh, hbd, hs⟩
    refine nn_intro ⟨ofNat n, isAssign_pack n he, (hV'.1 φ n).2 ⟨hh, hbd⟩, ?_⟩
    cases φ with
    | mem i₀ j₀ =>
      exact nn_intro (.inl (nn_intro ⟨ofNat i₀, ofNat j₀, e i₀, e j₀, Equiv.refl _,
        (reads_pack hbd.1).2 (Equiv.refl _), (reads_pack hbd.2).2 (Equiv.refl _), hs⟩))
    | eq i₀ j₀ =>
      exact nn_intro (.inr (nn_intro (.inl (nn_intro ⟨ofNat i₀, ofNat j₀, e i₀, e j₀, Equiv.refl _,
        (reads_pack hbd.1).2 (Equiv.refl _), (reads_pack hbd.2).2 (Equiv.refl _), hs⟩))))
    | fls => exact hs.elim
    | imp φ₁ φ₂ =>
      have ⟨h1, h2⟩ := nmax_le.1 (Nat.le_of_succ_le_succ hh)
      exact nn_intro (.inr (nn_intro (.inr (nn_intro (.inl (nn_intro ⟨enc φ₁, enc φ₂, Equiv.refl _,
        fun hp => (hT φ₂ n e he).2 ⟨h2, hbd.2, hs ((hT φ₁ n e he).1 hp).2.2⟩⟩))))))
    | all φ₁ =>
      refine nn_intro (.inr (nn_intro (.inr (nn_intro (.inr (nn_intro ⟨enc φ₁, Equiv.refl _, fun x hx => ?_⟩))))))
      have he' : ∀ i, i < n + 1 → Env.cons x e i ∈ A := fun i hi => by
        cases i with
        | zero => exact hx
        | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
      exact nn_intro ⟨pack (n+1) (Env.cons x e), hM.pack_mem_Ea hA hEam he', isCons_pack n,
        (hT φ₁ (n+1) (Env.cons x e) he').2 ⟨Nat.le_of_succ_le_succ hh, hbd, hs x hx⟩⟩

omit hEa hH hsat in
include hEam in
/-- The truth invariant advances along the step. -/
theorem invT_step {d : Nat} {V T V' T' : PSet.{u}} (hV' : InvV (d+1) V') (hT : InvT A d T)
    (st : IsStep A Ea V T V' T') : InvT A (d+1) T' := fun φ n e he =>
  (st.2.2.2 _ _ (hM.pack_mem_Ea hA hEam he)).trans (hM.tbody_enc hA hEam hV' hT φ n e he)

include hEam in
/-- **The invariants of the history**, at every stage. -/
theorem invariants : ∀ d : Nat, ¬¬∃ V T, M V ∧ M T ∧ Row H d V T ∧ InvV d V ∧ InvT A d T
  | 0 => nn_intro ⟨PSet.empty, PSet.empty, hM.empty, hM.empty, (hM.history_spec hA hEa hH hsat).2.1, invV_zero, invT_zero⟩
  | d+1 => by
    refine nn_bind (invariants d) fun ⟨V, T, hV, hT, hr, iV, iT⟩ => ?_
    refine nn_map (fun ⟨V', T', hV', hT', hr'⟩ => ?_) (hM.row_exists hA hEa hH hsat (d+1))
    have st := hM.row_step hA hEa hH hsat hV hT hV' hT' hr hr'
    have iV' := invV_step iV st
    exact ⟨V', T', hV', hT', hr', iV', hM.invT_step hA hEam iV' iT st⟩

end SynZF

/-- info: 'PSet.SynZF.invariants' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.invariants

end PSet
