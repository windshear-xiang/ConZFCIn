import Vendor.ConZF.SetSat
/-!
The scoped-code formula (gate 3, prerequisite SC). `scopedCodeF` (free variables the code `q = 0`
and the length `r = 1`, `Bound 2`) reads the scope component of the history over the empty
structure: there are `Z ≈ ∅`, `ω`, the assignment set of `Z`, the start state, a history, and a
stage whose scope table contains `⟨q, r⟩`. **Exact readback** (`scopedCode_correct`): for members
`q, r` of a `SynZF` class, this holds exactly when, negatively, `r ≈ ofNat n`, `q ≈ enc φ`, and
`Bound n φ` for some native `n, φ`. Both directions cover arbitrary supplied codes: the reverse
uses decoding of every scoped row (`vbody_decode`), so malformed codes are excluded.
-/
universe u

namespace PSet
open Fml CardF RecF CodeF AssignF StepF SetSatF

namespace SetSatF

/-- **Scoped codes**: `q = 0`, `r = 1`. -/
def scopedCodeF : Fml :=
  ex (and (emptyF 0)
    (ex (and (omegaF 0)
      (ex (and (assignSetF 0 2 1)
        (ex (and (emptyStateF 0)
          (ex (and (rename seqRen (seqF totStepF))
            (ex (and (mem 0 4)
              (ex (ex (ex (and (pairF 0 2 1) (and (pairMemF 4 3 0) (pairMemF 2 9 10)))))))))))))))))

end SetSatF

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- **Exact scoped-code readback.** -/
theorem scopedCode_correct {q r : PSet.{u}} (hq : M q) (hr : M r) {t : Nat → PSet.{u}} (ht : ∀ i, M (t i)) :
    Sat M scopedCodeF (Env.cons q (Env.cons r t)) ↔
      ¬¬∃ (n : Nat) (φ : Fml), r ≈ ofNat n ∧ q ≈ enc φ ∧ Bound n φ := by
  have hT := hM.toTransClass
  let E0 : Nat → PSet.{u} := Env.cons q (Env.cons r t)
  have hE0 : ∀ i, M (E0 i) := Env.cons_mem hq (Env.cons_mem hr ht)
  constructor
  · intro h
    refine Stable.of_nn (sat_ex.1 h) fun ⟨Z, hZ, h⟩ => ?_
    have ⟨h0, h⟩ := sat_and.1 h
    have hE1 := Env.cons_mem hZ hE0
    have eZ : Z ≈ PSet.empty := (hT.sat_emptyF hE1 0).1 h0
    refine Stable.of_nn (sat_ex.1 h) fun ⟨ω', hω'M, h⟩ => ?_
    have ⟨h1, h⟩ := sat_and.1 h
    have hE2 := Env.cons_mem hω'M hE1
    have hω : ω' ≈ PSet.omega := (hM.sat_omegaF hE2 0).1 h1
    refine Stable.of_nn (sat_ex.1 h) fun ⟨Ea, hEa, h⟩ => ?_
    have ⟨h2, h⟩ := sat_and.1 h
    have hE3 := Env.cons_mem hEa hE2
    have hEam := (hM.sat_assignSetF hE3 0 2 1 hω).1 h2
    refine Stable.of_nn (sat_ex.1 h) fun ⟨s₀, hs₀M, h⟩ => ?_
    have ⟨h3, h⟩ := sat_and.1 h
    have hE4 := Env.cons_mem hs₀M hE3
    have hs₀ := (hM.sat_emptyStateF hE4 0).1 h3
    refine Stable.of_nn (sat_ex.1 h) fun ⟨H, hH, h⟩ => ?_
    have ⟨h4, h⟩ := sat_and.1 h
    have hsat := (sat_seq_renamed hω hs₀).1 h4
    have hE5 := Env.cons_mem hH hE4
    refine Stable.of_nn (sat_ex.1 h) fun ⟨d, hdM, h⟩ => ?_
    have ⟨h5, h⟩ := sat_and.1 h
    have hd : d ∈ PSet.omega := (mem_congr_right hω).1 h5
    have hE6 := Env.cons_mem hdM hE5
    refine Stable.of_nn (sat_ex.1 h) fun ⟨V, hV, h⟩ => Stable.of_nn (sat_ex.1 h) fun ⟨T, hT', h⟩ =>
      Stable.of_nn (sat_ex.1 h) fun ⟨st, hst, h⟩ => ?_
    have hE9 := Env.cons_mem hst (Env.cons_mem hT' (Env.cons_mem hV hE6))
    have ⟨h6, h⟩ := sat_and.1 h
    have ⟨h7, h8⟩ := sat_and.1 h
    have est := (hT.sat_pairF hE9 0 2 1).1 h6
    have hrow : PSet.pair d (PSet.pair V T) ∈ H := (mem_congr_left (pair_congr (Equiv.refl _) est)).1
      ((hT.sat_pairMemF hE9 4 3 0).1 h7)
    have hqr : PSet.pair q r ∈ V := (hT.sat_pairMemF hE9 2 9 10).1 h8
    refine Stable.of_nn (mem_omega.1 hd) fun ⟨m, em⟩ => ?_
    have hrow' : Row H m V T := (mem_congr_left (pair_congr em (Equiv.refl _))).1 hrow
    refine Stable.of_nn (hM.invariants hZ hEa hH hsat hEam m) fun ⟨V', T', _, _, hr', iV, _⟩ => ?_
    have ⟨eV, _⟩ := hM.row_unique hZ hEa hH hsat hrow' hr'
    have hqr' : PSet.pair q r ∈ V' := (mem_congr_right eV).1 hqr
    refine nn_map (fun ⟨φ, n, e⟩ => ?_) (iV.2 _ hqr')
    have ⟨eqq, er⟩ := pair_inj e
    exact ⟨n, φ, er, eqq, ((iV.1 φ n).1 ((mem_congr_left e).1 hqr')).2⟩
  · intro h
    refine Stable.of_nn h fun ⟨n, φ, er, eqq, hb⟩ => ?_
    have hE1 := Env.cons_mem hM.empty hE0
    refine sat_ex.2 (nn_intro ⟨PSet.empty, hM.empty, sat_and.2 ⟨(hT.sat_emptyF hE1 0).2 (Equiv.refl _), ?_⟩⟩)
    have hE2 := Env.cons_mem hM.omega hE1
    refine sat_ex.2 (nn_intro ⟨PSet.omega, hM.omega, sat_and.2 ⟨(hM.sat_omegaF hE2 0).2 (Equiv.refl _), ?_⟩⟩)
    refine Stable.of_nn (hM.assignSet_exists hM.empty) fun ⟨Ea, hEa, hEam⟩ => ?_
    have hE3 := Env.cons_mem hEa hE2
    refine sat_ex.2 (nn_intro ⟨Ea, hEa, sat_and.2 ⟨(hM.sat_assignSetF hE3 0 2 1 (Equiv.refl _)).2 hEam, ?_⟩⟩)
    have hs₀M : M startState := hM.pair hM.empty hM.empty
    have hE4 := Env.cons_mem hs₀M hE3
    refine sat_ex.2 (nn_intro ⟨startState, hs₀M, sat_and.2 ⟨(hM.sat_emptyStateF hE4 0).2 (Equiv.refl _), ?_⟩⟩)
    refine Stable.of_nn (hM.history_exists hM.empty hEa) fun ⟨H, hH, hsat⟩ => ?_
    have hE5 := Env.cons_mem hH hE4
    refine sat_ex.2 (nn_intro ⟨H, hH, sat_and.2 ⟨(sat_seq_renamed (Equiv.refl _) (Equiv.refl _)).2 hsat, ?_⟩⟩)
    refine Stable.of_nn (hM.invariants hM.empty hEa hH hsat hEam φ.ht) fun ⟨V, T, hV, hT', hr, iV, _⟩ => ?_
    have hdM : M (ofNat φ.ht) := hM.trans hM.omega (ofNat_mem_omega _)
    have hE6 := Env.cons_mem hdM hE5
    have hst : M (PSet.pair V T) := hM.pair hV hT'
    have hE9 := Env.cons_mem hst (Env.cons_mem hT' (Env.cons_mem hV hE6))
    have hqr : PSet.pair q r ∈ V := (mem_congr_left (pair_congr eqq.symm er.symm)).1 ((iV.1 φ n).2 ⟨Nat.le_refl _, hb⟩)
    exact sat_ex.2 (nn_intro ⟨ofNat φ.ht, hdM, sat_and.2 ⟨ofNat_mem_omega _, sat_ex.2 (nn_intro ⟨V, hV, sat_ex.2 (nn_intro ⟨T, hT',
      sat_ex.2 (nn_intro ⟨PSet.pair V T, hst, sat_and.2 ⟨(hT.sat_pairF hE9 0 2 1).2 (Equiv.refl _), sat_and.2
        ⟨(hT.sat_pairMemF hE9 4 3 0).2 hr, (hT.sat_pairMemF hE9 2 9 10).2 hqr⟩⟩⟩)⟩)⟩)⟩⟩)

end SynZF

set_option maxRecDepth 200000 in
/-- The scoped-code formula has free variables `0, 1` only. -/
theorem bound_scopedCodeF : Bound 2 scopedCodeF := by decide

/-- info: 'PSet.SynZF.scopedCode_correct' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.scopedCode_correct
/-- info: 'PSet.bound_scopedCodeF' does not depend on any axioms -/
#guard_msgs in #print axioms bound_scopedCodeF

end PSet
