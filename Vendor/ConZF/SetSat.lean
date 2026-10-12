import Vendor.ConZF.History
/-!
Set-sized satisfaction as a formula (gate 2, checkpoint 4). `setSatF` (free variables: the
domain `A = 0`, the code `q = 1`, the assignment `e = 2`) says: there are `ω` (`omegaF`), the
assignment set of `A` (`assignSetF`), the start state `⟨∅, ∅⟩` (`emptyStateF`), and a history `H`
satisfying the sequence formula for the totalized step (renamed into position, every unused
parameter slot pointing at `ω`), with a stage `d ∈ ω` whose truth table contains `⟨q, e⟩`.

**Uniform correctness** (`setSat_correct`): in a `SynZF` class, for every native formula `φ`,
length `n`, and environment `e` with entries in a member `A`, the class satisfies
`setSatF` at `(A, enc φ, pack n e)` exactly when `Bound n φ` and `φ` holds in the set structure
`A` at `e`. The empty domain and the empty assignment are ordinary cases: the only assignment
into `∅` is the empty package, and closed formulas are evaluated at length `0`. Malformed codes
never enter the tables (`vbody_decode`).
-/
universe u

namespace PSet
open Fml CardF RecF CodeF AssignF StepF

namespace SetSatF

/-- `i` is inductive. -/
def inductiveF (i : Nat) : Fml :=
  and (ex (and (emptyF 0) (mem 0 (i+1)))) (all (imp (mem 0 (i+1)) (ex (and (succF 0 1) (mem 0 (i+2))))))

/-- `w ≈ ω`: inductive and contained in every inductive set. -/
def omegaF (w : Nat) : Fml :=
  and (inductiveF w) (all (imp (inductiveF 0) (all (imp (mem 0 (w+2)) (mem 0 1)))))

/-- `Ea` is the set of assignments into `A`. -/
def assignSetF (Ea A ω : Nat) : Fml :=
  all (iff (mem 0 (Ea+1)) (ex (assignF 1 0 (A+2) (ω+2))))

/-- `s ≈ ⟨∅, ∅⟩`. -/
def emptyStateF (s : Nat) : Fml := ex (and (emptyF 0) (pairF (s+1) 0 0))

/-- The renaming placing the sequence formula: `H = 0`, `s₀ = 1`, `ω = 3`, `A = 4`, `Ea = 2`,
and every unused parameter slot at `ω`. -/
def seqRen : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | 3 => 4
  | 4 => 2
  | _ => 3

/-- **Set satisfaction**: `A = 0`, `q = 1`, `e = 2`. -/
def setSatF : Fml :=
  ex (and (omegaF 0)
    (ex (and (assignSetF 0 2 1)
      (ex (and (emptyStateF 0)
        (ex (and (rename seqRen (seqF totStepF))
          (ex (and (mem 0 4)
            (ex (ex (ex (and (pairF 0 2 1) (and (pairMemF 4 3 0) (pairMemF 1 9 10)))))))))))))))

end SetSatF

open SetSatF

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem sat_inductiveF {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (i : Nat) :
    Sat M (inductiveF i) E ↔ PSet.empty ∈ E i ∧ ∀ x, x ∈ E i → succ x ∈ E i := by
  have hT := hM.toTransClass
  refine sat_and.trans (and_congr ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h x hx => ?_, fun h x hxM hx => ?_⟩)
  · refine Stable.of_nn (sat_ex.1 h) fun ⟨z, hz, hs⟩ => ?_
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact (mem_congr_left ((hT.sat_emptyF (Env.cons_mem hz hE) 0).1 h1)).1 h2
  · exact sat_ex.2 (nn_intro ⟨PSet.empty, hM.empty, sat_and.2 ⟨(hT.sat_emptyF (Env.cons_mem hM.empty hE) 0).2 (Equiv.refl _), h⟩⟩)
  · have hxM := hM.trans (hE i) hx
    refine Stable.of_nn (sat_ex.1 (h x hxM hx)) fun ⟨y, hy, hs⟩ => ?_
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact (mem_congr_left ((hT.sat_succF (Env.cons_mem hy (Env.cons_mem hxM hE)) 0 1).1 h1)).1 h2
  · exact sat_ex.2 (nn_intro ⟨succ x, hM.succ_mem hxM, sat_and.2
      ⟨(hT.sat_succF (Env.cons_mem (hM.succ_mem hxM) (Env.cons_mem hxM hE)) 0 1).2 (Equiv.refl _), h x hx⟩⟩)

/-- `ω` is the least inductive set of the class. -/
theorem sat_omegaF {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (w : Nat) :
    Sat M (omegaF w) E ↔ E w ≈ PSet.omega := by
  have omega_ind : PSet.empty ∈ PSet.omega ∧ ∀ x, x ∈ PSet.omega → succ x ∈ PSet.omega :=
    ⟨ofNat_mem_omega 0, fun _ => succ_mem_omega⟩
  have sub_of_ind : ∀ {i : PSet.{u}}, PSet.empty ∈ i → (∀ x, x ∈ i → succ x ∈ i) → ∀ z, z ∈ PSet.omega → z ∈ i := by
    intro i h0 hs z hz
    have all : ∀ m, ofNat m ∈ i := fun m => by
      induction m with
      | zero => exact h0
      | succ m ih => exact hs _ ih
    exact Stable.of_nn (mem_omega.1 hz) fun ⟨m, em⟩ => (mem_congr_left em).2 (all m)
  refine sat_and.trans ⟨fun ⟨h1, h2⟩ => ?_, fun h => ⟨(hM.sat_inductiveF hE w).2 ⟨(mem_congr_right h).2 omega_ind.1,
    fun x hx => (mem_congr_right h).2 (omega_ind.2 x ((mem_congr_right h).1 hx))⟩, fun i hi hind x _ hx => ?_⟩⟩
  · have ⟨h0, hs⟩ := (hM.sat_inductiveF hE w).1 h1
    refine ext fun z => ⟨fun hz => ?_, fun hz => sub_of_ind h0 hs z hz⟩
    have := h2 PSet.omega hM.omega ((hM.sat_inductiveF (Env.cons_mem hM.omega hE) 0).2 omega_ind) z (hM.trans (hE w) hz) hz
    exact this
  · have ⟨h0, hs⟩ := (hM.sat_inductiveF (Env.cons_mem hi hE) 0).1 hind
    exact sub_of_ind h0 hs x ((mem_congr_right h).1 hx)

theorem sat_assignSetF {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (Ea A ω : Nat) (hω : E ω ≈ PSet.omega) :
    Sat M (assignSetF Ea A ω) E ↔ ∀ e', e' ∈ E Ea ↔ (M e' ∧ ¬¬∃ n, IsAssign (E A) e' n) := by
  have hT := hM.toTransClass
  constructor
  · intro h e'
    constructor
    · intro he
      have heM := hM.trans (hE Ea) he
      refine ⟨heM, nn_map (fun ⟨n, _, hs⟩ => ⟨n, ?_⟩) (sat_ex.1 ((sat_iff.1 (h e' heM)).1 he))⟩
      exact (hT.sat_assignF (Env.cons_mem (by assumption) (Env.cons_mem heM hE)) 1 0 (A+2) (ω+2) hω).1 hs
    · rintro ⟨heM, hn⟩
      refine (sat_iff.1 (h e' heM)).2 (sat_ex.2 (nn_map (fun ⟨n, ha⟩ => ⟨n, hM.trans hM.omega ha.1, ?_⟩) hn))
      exact (hT.sat_assignF (Env.cons_mem (hM.trans hM.omega ha.1) (Env.cons_mem heM hE)) 1 0 (A+2) (ω+2) hω).2 ha
  · intro h e' heM
    refine sat_iff.2 ((h e').trans ⟨fun ⟨_, hn⟩ => sat_ex.2 (nn_map (fun ⟨n, ha⟩ => ⟨n, hM.trans hM.omega ha.1, ?_⟩) hn),
      fun hs => ⟨heM, nn_map (fun ⟨n, hn, hs⟩ => ⟨n, ?_⟩) (sat_ex.1 hs)⟩⟩)
    · exact (hT.sat_assignF (Env.cons_mem (hM.trans hM.omega ha.1) (Env.cons_mem heM hE)) 1 0 (A+2) (ω+2) hω).2 ha
    · exact (hT.sat_assignF (Env.cons_mem hn (Env.cons_mem heM hE)) 1 0 (A+2) (ω+2) hω).1 hs

theorem sat_emptyStateF {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (s : Nat) :
    Sat M (emptyStateF s) E ↔ E s ≈ startState := by
  have hT := hM.toTransClass
  refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨z, hz, hs⟩ => ?_, fun h => ?_⟩
  · have ⟨h1, h2⟩ := sat_and.1 hs
    have ez := (hT.sat_emptyF (Env.cons_mem hz hE) 0).1 h1
    exact ((hT.sat_pairF (Env.cons_mem hz hE) (s+1) 0 0).1 h2).trans (pair_congr ez ez)
  · exact nn_intro ⟨PSet.empty, hM.empty, sat_and.2 ⟨(hT.sat_emptyF (Env.cons_mem hM.empty hE) 0).2 (Equiv.refl _),
      (hT.sat_pairF (Env.cons_mem hM.empty hE) (s+1) 0 0).2 h⟩⟩

omit hM in
/-- The renamed sequence formula, at the environment of `setSatF` after four binders, reads
as the sequence formula at the history environment. -/
theorem sat_seq_renamed {H s₀ Ea ω' A q e : PSet.{u}} (hω : ω' ≈ PSet.omega) (hs₀ : s₀ ≈ startState) {t : Nat → PSet.{u}} :
    Sat M (rename seqRen (seqF totStepF)) (Env.cons H (Env.cons s₀ (Env.cons Ea (Env.cons ω' (Env.cons A (Env.cons q (Env.cons e t))))))) ↔
      Sat M (seqF totStepF) (Env.cons H (Env.cons startState (Env.cons PSet.omega (stepEnv A Ea)))) :=
  (sat_rename _ _ _).trans (Sat.resp_iff (fun _ => Iff.rfl) _ fun i => by
    rcases i with _ | _ | _ | _ | _ | _ | i
    · exact Equiv.refl _
    · exact hs₀
    · exact hω
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact hω
    · exact hω)

/-- **Uniform correctness of set satisfaction.** -/
theorem setSat_correct {A : PSet.{u}} (hA : M A) (φ : Fml) (n : Nat) (e : Nat → PSet.{u})
    (he : ∀ i, i < n → e i ∈ A) :
    Sat M setSatF (Env.cons A (Env.cons (enc φ) (Env.cons (pack n e) envω))) ↔
      (Bound n φ ∧ Sat (fun z => z ∈ A) φ e) := by
  have hT := hM.toTransClass
  have hq : M (enc φ) := by
    clear he
    induction φ with
    | mem i j | eq i j => exact hM.pair (TransClass.ofNat_mem hM.empty hM.succ_mem _) (hM.pair (TransClass.ofNat_mem hM.empty hM.succ_mem _) (TransClass.ofNat_mem hM.empty hM.succ_mem _))
    | fls => exact hM.pair (TransClass.ofNat_mem hM.empty hM.succ_mem _) hM.empty
    | imp _ _ ih1 ih2 => exact hM.pair (TransClass.ofNat_mem hM.empty hM.succ_mem _) (hM.pair ih1 ih2)
    | all _ ih => exact hM.pair (TransClass.ofNat_mem hM.empty hM.succ_mem _) ih
  have hpk : M (pack n e) := hM.pack_mem n fun i hi => hM.trans hA (he i hi)
  let E0 : Nat → PSet.{u} := Env.cons A (Env.cons (enc φ) (Env.cons (pack n e) envω))
  have hE0 : ∀ i, M (E0 i) := Env.cons_mem hA (Env.cons_mem hq (Env.cons_mem hpk hM.envω_mem))
  constructor
  · intro h
    refine Stable.of_nn (sat_ex.1 h) fun ⟨ω', hω'M, h⟩ => ?_
    have ⟨h1, h⟩ := sat_and.1 h
    have hE1 := Env.cons_mem hω'M hE0
    have hω : ω' ≈ PSet.omega := (hM.sat_omegaF hE1 0).1 h1
    refine Stable.of_nn (sat_ex.1 h) fun ⟨Ea, hEa, h⟩ => ?_
    have ⟨h2, h⟩ := sat_and.1 h
    have hE2 := Env.cons_mem hEa hE1
    have hEam := (hM.sat_assignSetF hE2 0 2 1 hω).1 h2
    refine Stable.of_nn (sat_ex.1 h) fun ⟨s₀, hs₀M, h⟩ => ?_
    have ⟨h3, h⟩ := sat_and.1 h
    have hE3 := Env.cons_mem hs₀M hE2
    have hs₀ := (hM.sat_emptyStateF hE3 0).1 h3
    refine Stable.of_nn (sat_ex.1 h) fun ⟨H, hH, h⟩ => ?_
    have ⟨h4, h⟩ := sat_and.1 h
    have hsat := (sat_seq_renamed hω hs₀).1 h4
    have hE4 := Env.cons_mem hH hE3
    refine Stable.of_nn (sat_ex.1 h) fun ⟨d, hdM, h⟩ => ?_
    have ⟨h5, h⟩ := sat_and.1 h
    have hd : d ∈ PSet.omega := (mem_congr_right hω).1 h5
    have hE5 := Env.cons_mem hdM hE4
    refine Stable.of_nn (sat_ex.1 h) fun ⟨V, hV, h⟩ => Stable.of_nn (sat_ex.1 h) fun ⟨T, hT', h⟩ =>
      Stable.of_nn (sat_ex.1 h) fun ⟨st, hst, h⟩ => ?_
    have hE8 := Env.cons_mem hst (Env.cons_mem hT' (Env.cons_mem hV hE5))
    have ⟨h6, h⟩ := sat_and.1 h
    have ⟨h7, h8⟩ := sat_and.1 h
    have est := (hT.sat_pairF hE8 0 2 1).1 h6
    have hrow : PSet.pair d (PSet.pair V T) ∈ H := (mem_congr_left (pair_congr (Equiv.refl _) est)).1
      ((hT.sat_pairMemF hE8 4 3 0).1 h7)
    have hqe : PSet.pair (enc φ) (pack n e) ∈ T := (hT.sat_pairMemF hE8 1 9 10).1 h8
    refine Stable.of_nn (mem_omega.1 hd) fun ⟨m, em⟩ => ?_
    have hrow' : Row H m V T := (mem_congr_left (pair_congr em (Equiv.refl _))).1 hrow
    refine Stable.of_nn (hM.invariants hA hEa hH hsat hEam m) fun ⟨V', T', _, _, hr', _, iT⟩ => ?_
    have ⟨_, eT⟩ := hM.row_unique hA hEa hH hsat hrow' hr'
    have := (iT φ n e he).1 ((mem_congr_right eT).1 hqe)
    exact ⟨this.2.1, this.2.2⟩
  · rintro ⟨hb, hs⟩
    have hE1 := Env.cons_mem hM.omega hE0
    refine sat_ex.2 (nn_intro ⟨PSet.omega, hM.omega, sat_and.2 ⟨(hM.sat_omegaF hE1 0).2 (Equiv.refl _), ?_⟩⟩)
    refine Stable.of_nn (hM.assignSet_exists hA) fun ⟨Ea, hEa, hEam⟩ => ?_
    have hE2 := Env.cons_mem hEa hE1
    refine sat_ex.2 (nn_intro ⟨Ea, hEa, sat_and.2 ⟨(hM.sat_assignSetF hE2 0 2 1 (Equiv.refl _)).2 hEam, ?_⟩⟩)
    have hs₀M : M startState := hM.pair hM.empty hM.empty
    have hE3 := Env.cons_mem hs₀M hE2
    refine sat_ex.2 (nn_intro ⟨startState, hs₀M, sat_and.2 ⟨(hM.sat_emptyStateF hE3 0).2 (Equiv.refl _), ?_⟩⟩)
    refine Stable.of_nn (hM.history_exists hA hEa) fun ⟨H, hH, hsat⟩ => ?_
    have hE4 := Env.cons_mem hH hE3
    refine sat_ex.2 (nn_intro ⟨H, hH, sat_and.2 ⟨(sat_seq_renamed (Equiv.refl _) (Equiv.refl _)).2 hsat, ?_⟩⟩)
    refine Stable.of_nn (hM.invariants hA hEa hH hsat hEam φ.ht) fun ⟨V, T, hV, hT', hr, _, iT⟩ => ?_
    have hdM : M (ofNat φ.ht) := hM.trans hM.omega (ofNat_mem_omega _)
    have hE5 := Env.cons_mem hdM hE4
    have hst : M (PSet.pair V T) := hM.pair hV hT'
    have hE8 := Env.cons_mem hst (Env.cons_mem hT' (Env.cons_mem hV hE5))
    refine sat_ex.2 (nn_intro ⟨ofNat φ.ht, hdM, sat_and.2 ⟨ofNat_mem_omega _, sat_ex.2 (nn_intro ⟨V, hV, sat_ex.2 (nn_intro ⟨T, hT',
      sat_ex.2 (nn_intro ⟨PSet.pair V T, hst, sat_and.2 ⟨(hT.sat_pairF hE8 0 2 1).2 (Equiv.refl _), sat_and.2
        ⟨(hT.sat_pairMemF hE8 4 3 0).2 hr, (hT.sat_pairMemF hE8 1 9 10).2 ((iT φ n e he).2 ⟨Nat.le_refl _, hb, hs⟩)⟩⟩⟩)⟩)⟩)⟩⟩)

/-- **Absoluteness**: two such classes containing the data agree on set satisfaction. -/
theorem setSat_absolute {M' : PSet.{u} → Prop} (hM' : SynZF M') {A : PSet.{u}} (hA : M A) (hA' : M' A)
    (φ : Fml) (n : Nat) (e : Nat → PSet.{u}) (he : ∀ i, i < n → e i ∈ A) :
    Sat M setSatF (Env.cons A (Env.cons (enc φ) (Env.cons (pack n e) envω))) ↔
      Sat M' setSatF (Env.cons A (Env.cons (enc φ) (Env.cons (pack n e) envω))) :=
  (hM.setSat_correct hA φ n e he).trans (hM'.setSat_correct hA' φ n e he).symm

end SynZF

/-- Bounds are decidable, so the scope of the concrete formula is checked by evaluation. -/
def decBound' : ∀ (k : Nat) (φ : Fml), Decidable (Bound k φ)
  | _, .mem _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .eq _ _ => inferInstanceAs (Decidable (_ ∧ _))
  | _, .fls => inferInstanceAs (Decidable True)
  | k, .imp φ ψ =>
    have := decBound' k φ
    have := decBound' k ψ
    inferInstanceAs (Decidable (Bound k φ ∧ Bound k ψ))
  | k, .all φ => decBound' (k+1) φ

instance {k : Nat} {φ : Fml} : Decidable (Bound k φ) := decBound' k φ

set_option maxRecDepth 200000 in
/-- The set-satisfaction formula has free variables `0, 1, 2` only. -/
theorem bound_setSatF : Bound 3 setSatF := by decide

/-- info: 'PSet.bound_setSatF' does not depend on any axioms -/
#guard_msgs in #print axioms bound_setSatF
/-- info: 'PSet.SynZF.setSat_correct' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.setSat_correct

end PSet
