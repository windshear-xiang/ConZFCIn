import Vendor.ConZF.Codes
/-!
The guarded validity/truth step (gate 2, checkpoint 2). A state is a pair `⟨V, T⟩` of a scope
table `V` (pairs of a code and a numeral) and a truth table `T` (pairs of a code and an
assignment). The step reads the new scope table from the old one (`validBodyF`: atoms with
indices below the length, `⊥`, implications whose children are already scoped at the same
length, universals whose body is scoped at the successor length) and the new truth table from
the **new** scope table and the **old** truth table (`truthBodyF`: the assignment is legal, the
row is scoped at its length, and the code is a true atom, an implication between rows of the
old table, or a universal all of whose cons extensions are rows of the old table). The step
formula `stepF` (variables: input state `0`, output state `1`, then the domain `A`, the
assignment set `E`, and `ω`) says both tables are pure and satisfy these membership laws.
Ambient readings and bridges are proved over a transitive pair-closed class with `∅` and
successors.
-/
universe u

namespace PSet
open Fml CardF RecF CodeF AssignF

namespace StepF

/-- The scope body: `n ∈ ω` and the code is scoped at `n` from the old table `V`. -/
def validBodyF (V q n ω : Nat) : Fml :=
  and (mem n ω)
    (or (ex (ex (and (mem 1 (n+2)) (and (mem 0 (n+2)) (or (memCodeF (q+2) 1 0) (eqCodeF (q+2) 1 0))))))
      (or (botCodeF q)
        (or (ex (ex (and (impCodeF (q+2) 1 0) (and (pairMemF (V+2) 1 (n+2)) (pairMemF (V+2) 0 (n+2))))))
          (ex (ex (and (allCodeF (q+2) 1) (and (succF 0 (n+2)) (pairMemF (V+2) 1 0))))))))

/-- The new scope table: pure rows with numerals in `ω`, with the exact membership law. -/
def validNextF (V V' ω : Nat) : Fml :=
  and (all (imp (mem 0 (V'+1)) (ex (ex (and (mem 0 (ω+3)) (pairF 2 1 0))))))
    (all (all (iff (pairMemF (V'+2) 1 0) (validBodyF (V+2) 1 0 (ω+2)))))

/-- The truth body at a code `q` and assignment `e`. -/
def truthBodyF (A E ω V' T q e : Nat) : Fml :=
  ex (and (assignF (e+1) 0 (A+1) (ω+1)) (and (pairMemF (V'+1) (q+1) 0)
    (or (ex (ex (ex (ex (and (memCodeF (q+5) 3 2) (and (pairMemF (e+5) 3 1) (and (pairMemF (e+5) 2 0) (mem 1 0))))))))
      (or (ex (ex (ex (ex (and (eqCodeF (q+5) 3 2) (and (pairMemF (e+5) 3 1) (and (pairMemF (e+5) 2 0) (eq 1 0))))))))
        (or (ex (ex (and (impCodeF (q+3) 1 0) (imp (pairMemF (T+3) 1 (e+3)) (pairMemF (T+3) 0 (e+3))))))
          (ex (and (allCodeF (q+2) 0)
            (all (imp (mem 0 (A+3)) (ex (and (mem 0 (E+4)) (and (consF 0 1 (e+4)) (pairMemF (T+4) 2 0)))))))))))))

/-- The new truth table: pure rows with assignments in `E`, with the exact membership law. -/
def truthNextF (A E ω V' T T' : Nat) : Fml :=
  and (all (imp (mem 0 (T'+1)) (ex (ex (and (mem 0 (E+3)) (pairF 2 1 0))))))
    (all (all (imp (mem 0 (E+2)) (iff (pairMemF (T'+2) 1 0) (truthBodyF (A+2) (E+2) (ω+2) (V'+2) (T+2) 1 0)))))

/-- **The step**: input state `0`, output state `1`, then `A = 2`, `E = 3`, `ω = 4`. -/
def stepF : Fml :=
  ex (ex (ex (ex (and (pairF 4 3 2) (and (pairF 5 1 0)
    (and (validNextF 3 1 8) (truthNextF 6 7 8 1 2 0)))))))

end StepF

open StepF

/-! ### Ambient readings -/

/-- The scope body, ambiently. -/
def VBody (V q n : PSet.{u}) : Prop :=
  n ∈ omega ∧ ¬¬(
    (¬¬∃ i j, i ∈ n ∧ j ∈ n ∧ ¬¬(q ≈ pair (ofNat 0) (pair i j) ∨ q ≈ pair (ofNat 1) (pair i j))) ∨ ¬¬(
    q ≈ pair (ofNat 2) empty ∨ ¬¬(
    (¬¬∃ p r, q ≈ pair (ofNat 3) (pair p r) ∧ pair p n ∈ V ∧ pair r n ∈ V) ∨
    (¬¬∃ p, q ≈ pair (ofNat 4) p ∧ pair p (succ n) ∈ V))))

/-- The truth body, ambiently. -/
def TBody (A E V' T q e : PSet.{u}) : Prop :=
  ¬¬∃ n, IsAssign A e n ∧ pair q n ∈ V' ∧ ¬¬(
    (¬¬∃ i j x y, q ≈ pair (ofNat 0) (pair i j) ∧ pair i x ∈ e ∧ pair j y ∈ e ∧ x ∈ y) ∨ ¬¬(
    (¬¬∃ i j x y, q ≈ pair (ofNat 1) (pair i j) ∧ pair i x ∈ e ∧ pair j y ∈ e ∧ x ≈ y) ∨ ¬¬(
    (¬¬∃ p r, q ≈ pair (ofNat 3) (pair p r) ∧ (pair p e ∈ T → pair r e ∈ T)) ∨
    (¬¬∃ p, q ≈ pair (ofNat 4) p ∧ ∀ x, x ∈ A → ¬¬∃ u, u ∈ E ∧ IsCons u x e ∧ pair p u ∈ T))))

/-- The step, ambiently: the new tables are pure with the membership laws. -/
def IsStep (A E V T V' T' : PSet.{u}) : Prop :=
  (∀ r, r ∈ V' → ¬¬∃ q n, n ∈ omega ∧ r ≈ pair q n) ∧
  (∀ q n, pair q n ∈ V' ↔ VBody V q n) ∧
  (∀ r, r ∈ T' → ¬¬∃ q e, e ∈ E ∧ r ≈ pair q e) ∧
  (∀ q e, e ∈ E → (pair q e ∈ T' ↔ TBody A E V' T q e))

instance {V q n : PSet.{u}} : Stable (VBody V q n) := inferInstanceAs (Stable (_ ∧ ¬_))
instance {A E V' T q e : PSet.{u}} : Stable (TBody A E V' T q e) := inferInstanceAs (Stable (¬_))
instance {A E V T V' T' : PSet.{u}} : Stable (IsStep A E V T V' T') :=
  inferInstanceAs (Stable (_ ∧ (∀ q n, _ ↔ VBody V q n) ∧ _ ∧ ∀ q e, _ → (_ ↔ TBody A E V' T q e)))

namespace TransClass
variable {M : PSet.{u} → Prop} (hN : TransClass M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
  (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y))
include hN hE h0 hsucc

theorem sat_validBodyF (V q n ω : Nat) (hω : E ω ≈ omega) :
    Sat M (validBodyF V q n ω) E ↔ VBody (E V) (E q) (E n) := by
  refine sat_and.trans (and_congr (mem_congr_right hω) (sat_or.trans (nn_congr (or_congr ?_ (sat_or.trans
    (nn_congr (or_congr (hN.sat_botCodeF hE h0 hsucc q) (sat_or.trans (nn_congr (or_congr ?_ ?_))))))))))
  · -- atoms
    constructor
    · intro h
      refine nn_bind (sat_ex.1 h) fun ⟨i, hi, hs⟩ => nn_map (fun ⟨j, hj, hs⟩ => ?_) (sat_ex.1 hs)
      have he2 := Env.cons_mem hj (Env.cons_mem hi hE)
      have ⟨h1, h2⟩ := sat_and.1 hs
      have ⟨h2, h3⟩ := sat_and.1 h2
      exact ⟨i, j, h1, h2, nn_map (fun
        | .inl h => .inl ((hN.sat_memCodeF he2 h0 hsucc (q+2) 1 0).1 h)
        | .inr h => .inr ((hN.sat_eqCodeF he2 h0 hsucc (q+2) 1 0).1 h)) (sat_or.1 h3)⟩
    · intro h
      refine sat_ex.2 (nn_bind h fun ⟨i, j, hi, hj, hc⟩ => ?_)
      have hiM := hN.trans (hE n) hi
      have hjM := hN.trans (hE n) hj
      have he2 := Env.cons_mem hjM (Env.cons_mem hiM hE)
      exact nn_intro ⟨i, hiM, sat_ex.2 (nn_intro ⟨j, hjM, sat_and.2 ⟨hi, sat_and.2 ⟨hj, sat_or.2 (nn_map (fun
        | .inl h => .inl ((hN.sat_memCodeF he2 h0 hsucc (q+2) 1 0).2 h)
        | .inr h => .inr ((hN.sat_eqCodeF he2 h0 hsucc (q+2) 1 0).2 h)) hc)⟩⟩⟩)⟩
  · -- implications
    constructor
    · intro h
      refine nn_bind (sat_ex.1 h) fun ⟨p, hp, hs⟩ => nn_map (fun ⟨r, hr, hs⟩ => ?_) (sat_ex.1 hs)
      have he2 := Env.cons_mem hr (Env.cons_mem hp hE)
      have ⟨h1, h2⟩ := sat_and.1 hs
      have ⟨h2, h3⟩ := sat_and.1 h2
      exact ⟨p, r, (hN.sat_impCodeF he2 h0 hsucc (q+2) 1 0).1 h1, (hN.sat_pairMemF he2 (V+2) 1 (n+2)).1 h2,
        (hN.sat_pairMemF he2 (V+2) 0 (n+2)).1 h3⟩
    · intro h
      refine sat_ex.2 (nn_bind h fun ⟨p, r, hc, hp, hr⟩ => ?_)
      have hpM := (hN.of_pair_mem (hE V) hp).1
      have hrM := (hN.of_pair_mem (hE V) hr).1
      have he2 := Env.cons_mem hrM (Env.cons_mem hpM hE)
      exact nn_intro ⟨p, hpM, sat_ex.2 (nn_intro ⟨r, hrM, sat_and.2 ⟨(hN.sat_impCodeF he2 h0 hsucc (q+2) 1 0).2 hc,
        sat_and.2 ⟨(hN.sat_pairMemF he2 (V+2) 1 (n+2)).2 hp, (hN.sat_pairMemF he2 (V+2) 0 (n+2)).2 hr⟩⟩⟩)⟩
  · -- universals
    constructor
    · intro h
      refine nn_bind (sat_ex.1 h) fun ⟨p, hp, hs⟩ => nn_map (fun ⟨m, hm, hs⟩ => ?_) (sat_ex.1 hs)
      have he2 := Env.cons_mem hm (Env.cons_mem hp hE)
      have ⟨h1, h2⟩ := sat_and.1 hs
      have ⟨h2, h3⟩ := sat_and.1 h2
      have em := (hN.sat_succF he2 0 (n+2)).1 h2
      exact ⟨p, (hN.sat_allCodeF he2 h0 hsucc (q+2) 1).1 h1,
        (mem_congr_left (pair_congr (Equiv.refl _) em)).1 ((hN.sat_pairMemF he2 (V+2) 1 0).1 h3)⟩
    · intro h
      refine sat_ex.2 (nn_bind h fun ⟨p, hc, hp⟩ => ?_)
      have hpM := (hN.of_pair_mem (hE V) hp).1
      have he2 := Env.cons_mem (hsucc (hE n)) (Env.cons_mem hpM hE)
      exact nn_intro ⟨p, hpM, sat_ex.2 (nn_intro ⟨succ (E n), hsucc (hE n), sat_and.2
        ⟨(hN.sat_allCodeF he2 h0 hsucc (q+2) 1).2 hc, sat_and.2 ⟨(hN.sat_succF he2 0 (n+2)).2 (Equiv.refl _),
          (hN.sat_pairMemF he2 (V+2) 1 0).2 hp⟩⟩⟩)⟩

omit hE h0 hsucc in
/-- The components of a pair in the class are in the class. -/
theorem of_pair_class {x y : PSet.{u}} (h : M (pair x y)) : M x ∧ M y :=
  ⟨hN.trans (hN.trans h (mem_upair_left _ _)) (self_mem_singleton x),
   hN.trans (hN.trans h (mem_upair_right _ _)) (mem_upair_right x y)⟩

omit hE h0 hsucc in
/-- A code with a pair payload in the class has components in the class. -/
theorem of_code {q t p : PSet.{u}} (hq : M q) (e : q ≈ pair t p) : M t ∧ M p :=
  hN.of_pair_class (hN.resp e hq)

theorem sat_validNextF (V V' ω : Nat) (hω : E ω ≈ omega) :
    Sat M (validNextF V V' ω) E ↔
      (∀ r, r ∈ E V' → ¬¬∃ q n, n ∈ omega ∧ r ≈ pair q n) ∧ (∀ q n, pair q n ∈ E V' ↔ VBody (E V) q n) := by
  refine sat_and.trans (and_congr ⟨fun h r hr => ?_, fun h r hr hr' => ?_⟩ ⟨fun h q n => ?_, fun h q hq n hn => ?_⟩)
  · have hrM := hN.trans (hE V') hr
    refine nn_bind (sat_ex.1 (h r hrM hr)) fun ⟨q, hq, hs⟩ => nn_map (fun ⟨n, hn, hs⟩ => ?_) (sat_ex.1 hs)
    have he3 := Env.cons_mem hn (Env.cons_mem hq (Env.cons_mem hrM hE))
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨q, n, (mem_congr_right hω).1 h1, (hN.sat_pairF he3 2 1 0).1 h2⟩
  · refine sat_ex.2 (nn_bind (h r hr') fun ⟨q, n, hn, e'⟩ => ?_)
    have ⟨hq, hnM⟩ := hN.of_pair_class (hN.resp e' hr)
    have he3 := Env.cons_mem hnM (Env.cons_mem hq (Env.cons_mem hr hE))
    exact nn_intro ⟨q, hq, sat_ex.2 (nn_intro ⟨n, hnM, sat_and.2 ⟨(mem_congr_right hω).2 hn, (hN.sat_pairF he3 2 1 0).2 e'⟩⟩)⟩
  · -- the law, for arbitrary ambient `q`, `n`
    constructor
    · intro hqn
      have ⟨hq, hn⟩ := hN.of_pair_mem (hE V') hqn
      have he2 := Env.cons_mem hn (Env.cons_mem hq hE)
      exact (hN.sat_validBodyF he2 h0 hsucc (V+2) 1 0 (ω+2) hω).1 (sat_iff.1 (h q hq n hn) |>.1
        ((hN.sat_pairMemF he2 (V'+2) 1 0).2 hqn))
    · intro hb
      have hn : M n := hN.trans (hN.resp hω (hE ω)) hb.1
      -- replace `q` by an equivalent member of the class, read off the body
      have hq' : ¬¬∃ q', M q' ∧ q ≈ q' := by
        refine nn_bind hb.2 fun
          | .inl h => nn_bind h fun ⟨i, j, hi, hj, hc⟩ => nn_map (fun
              | .inl e => ⟨_, hN.pair_mem (ofNat_mem h0 hsucc 0) (hN.pair_mem (hN.trans hn hi) (hN.trans hn hj)), e⟩
              | .inr e => ⟨_, hN.pair_mem (ofNat_mem h0 hsucc 1) (hN.pair_mem (hN.trans hn hi) (hN.trans hn hj)), e⟩) hc
          | .inr h => nn_bind h fun
            | .inl e => nn_intro ⟨_, hN.pair_mem (ofNat_mem h0 hsucc 2) h0, e⟩
            | .inr h => nn_bind h fun
              | .inl h => nn_map (fun ⟨p, r, e, hp, hr⟩ => ⟨_, hN.pair_mem (ofNat_mem h0 hsucc 3)
                  (hN.pair_mem (hN.of_pair_mem (hE V) hp).1 (hN.of_pair_mem (hE V) hr).1), e⟩) h
              | .inr h => nn_map (fun ⟨p, e, hp⟩ => ⟨_, hN.pair_mem (ofNat_mem h0 hsucc 4) (hN.of_pair_mem (hE V) hp).1, e⟩) h
      refine Stable.of_nn hq' fun ⟨q', hq'M, eqq⟩ => ?_
      have he2 := Env.cons_mem hn (Env.cons_mem hq'M hE)
      have hb' : VBody (E V) q' n := ⟨hb.1, nn_map (fun
        | .inl h => .inl (nn_map (fun ⟨i, j, hi, hj, hc⟩ => ⟨i, j, hi, hj, nn_map (fun
            | .inl e => .inl (eqq.symm.trans e)
            | .inr e => .inr (eqq.symm.trans e)) hc⟩) h)
        | .inr h => .inr (nn_map (fun
          | .inl e => .inl (eqq.symm.trans e)
          | .inr h => .inr (nn_map (fun
            | .inl h => .inl (nn_map (fun ⟨p, r, e, hp, hr⟩ => ⟨p, r, eqq.symm.trans e, hp, hr⟩) h)
            | .inr h => .inr (nn_map (fun ⟨p, e, hp⟩ => ⟨p, eqq.symm.trans e, hp⟩) h)) h)) h)) hb.2⟩
      have := (sat_iff.1 (h q' hq'M n hn)).2 ((hN.sat_validBodyF he2 h0 hsucc (V+2) 1 0 (ω+2) hω).2 hb')
      exact (mem_congr_left (pair_congr eqq.symm (Equiv.refl _))).1 ((hN.sat_pairMemF he2 (V'+2) 1 0).1 this)
  · have he2 := Env.cons_mem hn (Env.cons_mem hq hE)
    exact sat_iff.2 ((hN.sat_pairMemF he2 (V'+2) 1 0).trans ((h q n).trans
      (hN.sat_validBodyF he2 h0 hsucc (V+2) 1 0 (ω+2) hω).symm))

/-- The membership-atom clause. -/
theorem sat_bodyMem (q e : Nat) :
    Sat M (ex (ex (ex (ex (and (memCodeF (q+4) 3 2) (and (pairMemF (e+4) 3 1) (and (pairMemF (e+4) 2 0) (mem 1 0)))))))) E ↔
      ¬¬∃ i j x y, E q ≈ pair (ofNat 0) (pair i j) ∧ pair i x ∈ E e ∧ pair j y ∈ E e ∧ x ∈ y := by
  constructor
  · intro h
    refine nn_bind (sat_ex.1 h) fun ⟨i, hi, h⟩ => nn_bind (sat_ex.1 h) fun ⟨j, hj, h⟩ =>
      nn_bind (sat_ex.1 h) fun ⟨x, hx, h⟩ => nn_map (fun ⟨y, hy, h⟩ => ?_) (sat_ex.1 h)
    have he4 := Env.cons_mem hy (Env.cons_mem hx (Env.cons_mem hj (Env.cons_mem hi hE)))
    have ⟨h1, h2⟩ := sat_and.1 h
    have ⟨h2, h3⟩ := sat_and.1 h2
    have ⟨h3, h4⟩ := sat_and.1 h3
    exact ⟨i, j, x, y, (hN.sat_memCodeF he4 h0 hsucc (q+4) 3 2).1 h1, (hN.sat_pairMemF he4 (e+4) 3 1).1 h2,
      (hN.sat_pairMemF he4 (e+4) 2 0).1 h3, h4⟩
  · intro h
    refine sat_ex.2 (nn_bind h fun ⟨i, j, x, y, hc, hix, hjy, hxy⟩ => ?_)
    have ⟨hi, hx⟩ := hN.of_pair_mem (hE e) hix
    have ⟨hj, hy⟩ := hN.of_pair_mem (hE e) hjy
    have he4 := Env.cons_mem hy (Env.cons_mem hx (Env.cons_mem hj (Env.cons_mem hi hE)))
    exact nn_intro ⟨i, hi, sat_ex.2 (nn_intro ⟨j, hj, sat_ex.2 (nn_intro ⟨x, hx, sat_ex.2 (nn_intro ⟨y, hy,
      sat_and.2 ⟨(hN.sat_memCodeF he4 h0 hsucc (q+4) 3 2).2 hc, sat_and.2 ⟨(hN.sat_pairMemF he4 (e+4) 3 1).2 hix,
        sat_and.2 ⟨(hN.sat_pairMemF he4 (e+4) 2 0).2 hjy, hxy⟩⟩⟩⟩)⟩)⟩)⟩

/-- The equality-atom clause. -/
theorem sat_bodyEq (q e : Nat) :
    Sat M (ex (ex (ex (ex (and (eqCodeF (q+4) 3 2) (and (pairMemF (e+4) 3 1) (and (pairMemF (e+4) 2 0) (eq 1 0)))))))) E ↔
      ¬¬∃ i j x y, E q ≈ pair (ofNat 1) (pair i j) ∧ pair i x ∈ E e ∧ pair j y ∈ E e ∧ x ≈ y := by
  constructor
  · intro h
    refine nn_bind (sat_ex.1 h) fun ⟨i, hi, h⟩ => nn_bind (sat_ex.1 h) fun ⟨j, hj, h⟩ =>
      nn_bind (sat_ex.1 h) fun ⟨x, hx, h⟩ => nn_map (fun ⟨y, hy, h⟩ => ?_) (sat_ex.1 h)
    have he4 := Env.cons_mem hy (Env.cons_mem hx (Env.cons_mem hj (Env.cons_mem hi hE)))
    have ⟨h1, h2⟩ := sat_and.1 h
    have ⟨h2, h3⟩ := sat_and.1 h2
    have ⟨h3, h4⟩ := sat_and.1 h3
    exact ⟨i, j, x, y, (hN.sat_eqCodeF he4 h0 hsucc (q+4) 3 2).1 h1, (hN.sat_pairMemF he4 (e+4) 3 1).1 h2,
      (hN.sat_pairMemF he4 (e+4) 2 0).1 h3, h4⟩
  · intro h
    refine sat_ex.2 (nn_bind h fun ⟨i, j, x, y, hc, hix, hjy, hxy⟩ => ?_)
    have ⟨hi, hx⟩ := hN.of_pair_mem (hE e) hix
    have ⟨hj, hy⟩ := hN.of_pair_mem (hE e) hjy
    have he4 := Env.cons_mem hy (Env.cons_mem hx (Env.cons_mem hj (Env.cons_mem hi hE)))
    exact nn_intro ⟨i, hi, sat_ex.2 (nn_intro ⟨j, hj, sat_ex.2 (nn_intro ⟨x, hx, sat_ex.2 (nn_intro ⟨y, hy,
      sat_and.2 ⟨(hN.sat_eqCodeF he4 h0 hsucc (q+4) 3 2).2 hc, sat_and.2 ⟨(hN.sat_pairMemF he4 (e+4) 3 1).2 hix,
        sat_and.2 ⟨(hN.sat_pairMemF he4 (e+4) 2 0).2 hjy, hxy⟩⟩⟩⟩)⟩)⟩)⟩

/-- The implication clause. -/
theorem sat_bodyImp (q e T : Nat) (hq : M (E q)) :
    Sat M (ex (ex (and (impCodeF (q+2) 1 0) (imp (pairMemF (T+2) 1 (e+2)) (pairMemF (T+2) 0 (e+2)))))) E ↔
      ¬¬∃ p r, E q ≈ pair (ofNat 3) (pair p r) ∧ (pair p (E e) ∈ E T → pair r (E e) ∈ E T) := by
  constructor
  · intro h
    refine nn_bind (sat_ex.1 h) fun ⟨p, hp, h⟩ => nn_map (fun ⟨r, hr, h⟩ => ?_) (sat_ex.1 h)
    have he2 := Env.cons_mem hr (Env.cons_mem hp hE)
    have ⟨h1, h2⟩ := sat_and.1 h
    exact ⟨p, r, (hN.sat_impCodeF he2 h0 hsucc (q+2) 1 0).1 h1,
      fun hp' => (hN.sat_pairMemF he2 (T+2) 0 (e+2)).1 (h2 ((hN.sat_pairMemF he2 (T+2) 1 (e+2)).2 hp'))⟩
  · intro h
    refine sat_ex.2 (nn_bind h fun ⟨p, r, hc, hpr⟩ => ?_)
    have ⟨hp, hr⟩ := hN.of_pair_class (hN.of_code hq hc).2
    have he2 := Env.cons_mem hr (Env.cons_mem hp hE)
    exact nn_intro ⟨p, hp, sat_ex.2 (nn_intro ⟨r, hr, sat_and.2 ⟨(hN.sat_impCodeF he2 h0 hsucc (q+2) 1 0).2 hc,
      fun hp' => (hN.sat_pairMemF he2 (T+2) 0 (e+2)).2 (hpr ((hN.sat_pairMemF he2 (T+2) 1 (e+2)).1 hp'))⟩⟩)⟩

/-- The universal clause. -/
theorem sat_bodyAll (q e T A Ea : Nat) (hq : M (E q)) :
    Sat M (ex (and (allCodeF (q+1) 0) (all (imp (mem 0 (A+2)) (ex (and (mem 0 (Ea+3))
      (and (consF 0 1 (e+3)) (pairMemF (T+3) 2 0)))))))) E ↔
      ¬¬∃ p, E q ≈ pair (ofNat 4) p ∧ ∀ x, x ∈ E A → ¬¬∃ u, u ∈ E Ea ∧ IsCons u x (E e) ∧ pair p u ∈ E T := by
  constructor
  · intro h
    refine nn_map (fun ⟨p, hp, h⟩ => ?_) (sat_ex.1 h)
    have he1 := Env.cons_mem hp hE
    have ⟨h1, h2⟩ := sat_and.1 h
    refine ⟨p, (hN.sat_allCodeF he1 h0 hsucc (q+1) 0).1 h1, fun x hx => ?_⟩
    have hxM := hN.trans (hE A) hx
    have he2 := Env.cons_mem hxM he1
    refine nn_map (fun ⟨u, hu, h⟩ => ?_) (sat_ex.1 (h2 x hxM hx))
    have he3 := Env.cons_mem hu he2
    have ⟨h3, h4⟩ := sat_and.1 h
    have ⟨h4, h5⟩ := sat_and.1 h4
    exact ⟨u, h3, (hN.sat_consF he3 0 1 (e+3) hsucc h0).1 h4, (hN.sat_pairMemF he3 (T+3) 2 0).1 h5⟩
  · intro h
    refine sat_ex.2 (nn_map (fun ⟨p, hc, hall⟩ => ?_) h)
    have hp := (hN.of_code hq hc).2
    have he1 := Env.cons_mem hp hE
    refine ⟨p, hp, sat_and.2 ⟨(hN.sat_allCodeF he1 h0 hsucc (q+1) 0).2 hc, fun x hxM hx => ?_⟩⟩
    have he2 := Env.cons_mem hxM he1
    refine sat_ex.2 (nn_map (fun ⟨u, hu, hcons, hpu⟩ => ?_) (hall x hx))
    have huM := hN.trans (hE Ea) hu
    have he3 := Env.cons_mem huM he2
    exact ⟨u, huM, sat_and.2 ⟨hu, sat_and.2 ⟨(hN.sat_consF he3 0 1 (e+3) hsucc h0).2 hcons,
      (hN.sat_pairMemF he3 (T+3) 2 0).2 hpu⟩⟩⟩

theorem sat_truthBodyF (A Ea ω V' T q e : Nat) (hω : E ω ≈ omega) (hq : M (E q)) :
    Sat M (truthBodyF A Ea ω V' T q e) E ↔ TBody (E A) (E Ea) (E V') (E T) (E q) (E e) := by
  refine sat_ex.trans (nn_congr ⟨fun ⟨n, hn, hs⟩ => ?_, fun ⟨n, ha, hv, hb⟩ => ?_⟩)
  · have he1 := Env.cons_mem hn hE
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h2, h3⟩ := sat_and.1 h2
    refine ⟨n, (hN.sat_assignF he1 (e+1) 0 (A+1) (ω+1) hω).1 h1, (hN.sat_pairMemF he1 (V'+1) (q+1) 0).1 h2, ?_⟩
    refine nn_map (fun
      | .inl h => .inl ((hN.sat_bodyMem he1 h0 hsucc (q+1) (e+1)).1 h)
      | .inr h => .inr (nn_map (fun
        | .inl h => .inl ((hN.sat_bodyEq he1 h0 hsucc (q+1) (e+1)).1 h)
        | .inr h => .inr (nn_map (fun
          | .inl h => .inl ((hN.sat_bodyImp he1 h0 hsucc (q+1) (e+1) (T+1) hq).1 h)
          | .inr h => .inr ((hN.sat_bodyAll he1 h0 hsucc (q+1) (e+1) (T+1) (A+1) (Ea+1) hq).1 h)) (sat_or.1 h))) (sat_or.1 h))) (sat_or.1 h3)
  · have hn : M n := hN.trans (hN.resp hω (hE ω)) ha.1
    have he1 := Env.cons_mem hn hE
    refine ⟨n, hn, sat_and.2 ⟨(hN.sat_assignF he1 (e+1) 0 (A+1) (ω+1) hω).2 ha,
      sat_and.2 ⟨(hN.sat_pairMemF he1 (V'+1) (q+1) 0).2 hv, sat_or.2 (nn_map (fun
        | .inl h => .inl ((hN.sat_bodyMem he1 h0 hsucc (q+1) (e+1)).2 h)
        | .inr h => .inr (sat_or.2 (nn_map (fun
          | .inl h => .inl ((hN.sat_bodyEq he1 h0 hsucc (q+1) (e+1)).2 h)
          | .inr h => .inr (sat_or.2 (nn_map (fun
            | .inl h => .inl ((hN.sat_bodyImp he1 h0 hsucc (q+1) (e+1) (T+1) hq).2 h)
            | .inr h => .inr ((hN.sat_bodyAll he1 h0 hsucc (q+1) (e+1) (T+1) (A+1) (Ea+1) hq).2 h)) h))) h))) hb)⟩⟩⟩

theorem sat_truthNextF (A Ea ω V' T T' : Nat) (hω : E ω ≈ omega) :
    Sat M (truthNextF A Ea ω V' T T') E ↔
      (∀ r, r ∈ E T' → ¬¬∃ q e, e ∈ E Ea ∧ r ≈ pair q e) ∧
      (∀ q e, e ∈ E Ea → (pair q e ∈ E T' ↔ TBody (E A) (E Ea) (E V') (E T) q e)) := by
  refine sat_and.trans (and_congr ⟨fun h r hr => ?_, fun h r hr hr' => ?_⟩ ⟨fun h q e he => ?_, fun h q hq e he hee => ?_⟩)
  · have hrM := hN.trans (hE T') hr
    refine nn_bind (sat_ex.1 (h r hrM hr)) fun ⟨q, hq, hs⟩ => nn_map (fun ⟨e, he, hs⟩ => ?_) (sat_ex.1 hs)
    have he3 := Env.cons_mem he (Env.cons_mem hq (Env.cons_mem hrM hE))
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨q, e, h1, (hN.sat_pairF he3 2 1 0).1 h2⟩
  · refine sat_ex.2 (nn_bind (h r hr') fun ⟨q, e, he, e'⟩ => ?_)
    have ⟨hq, heM⟩ := hN.of_pair_class (hN.resp e' hr)
    have he3 := Env.cons_mem heM (Env.cons_mem hq (Env.cons_mem hr hE))
    exact nn_intro ⟨q, hq, sat_ex.2 (nn_intro ⟨e, heM, sat_and.2 ⟨he, (hN.sat_pairF he3 2 1 0).2 e'⟩⟩)⟩
  · have heM := hN.trans (hE Ea) he
    constructor
    · intro hqe
      have hq := (hN.of_pair_mem (hE T') hqe).1
      have he2 := Env.cons_mem heM (Env.cons_mem hq hE)
      exact (hN.sat_truthBodyF he2 h0 hsucc (A+2) (Ea+2) (ω+2) (V'+2) (T+2) 1 0 hω hq).1
        ((sat_iff.1 (h q hq e heM he)).1 ((hN.sat_pairMemF he2 (T'+2) 1 0).2 hqe))
    · intro hb
      -- the code is in the class, since it is scoped in the class's table
      refine Stable.of_nn hb fun ⟨_, _, hv, _⟩ => ?_
      have hq : M q := (hN.of_pair_mem (hE V') hv).1
      have he2 := Env.cons_mem heM (Env.cons_mem hq hE)
      exact (hN.sat_pairMemF he2 (T'+2) 1 0).1 ((sat_iff.1 (h q hq e heM he)).2
        ((hN.sat_truthBodyF he2 h0 hsucc (A+2) (Ea+2) (ω+2) (V'+2) (T+2) 1 0 hω hq).2 hb))
  · have he2 := Env.cons_mem he (Env.cons_mem hq hE)
    exact sat_iff.2 ((hN.sat_pairMemF he2 (T'+2) 1 0).trans ((h q e hee).trans
      (hN.sat_truthBodyF he2 h0 hsucc (A+2) (Ea+2) (ω+2) (V'+2) (T+2) 1 0 hω hq).symm))

omit hE in
/-- **The step bridge**: at states `s, s'` and parameters `A, E, ω`. -/
theorem sat_stepFormula {s s' A Ea : PSet.{u}} {e : Nat → PSet.{u}} (hs : M s) (hs' : M s') (hA : M A) (hEa : M Ea)
    (hω : M omega) (he : ∀ i, M (e i)) :
    Sat M stepF (Env.cons s (Env.cons s' (Env.cons A (Env.cons Ea (Env.cons omega e))))) ↔
      ¬¬∃ V T V' T', M V ∧ M T ∧ M V' ∧ M T' ∧ s ≈ pair V T ∧ s' ≈ pair V' T' ∧ IsStep A Ea V T V' T' := by
  have hE0 : ∀ i, M (Env.cons s (Env.cons s' (Env.cons A (Env.cons Ea (Env.cons omega e)))) i) :=
    Env.cons_mem hs (Env.cons_mem hs' (Env.cons_mem hA (Env.cons_mem hEa (Env.cons_mem hω he))))
  constructor
  · intro h
    refine nn_bind (sat_ex.1 h) fun ⟨V, hV, h⟩ => nn_bind (sat_ex.1 h) fun ⟨T, hT, h⟩ =>
      nn_bind (sat_ex.1 h) fun ⟨V', hV', h⟩ => nn_map (fun ⟨T', hT', h⟩ => ?_) (sat_ex.1 h)
    have hE4 := Env.cons_mem hT' (Env.cons_mem hV' (Env.cons_mem hT (Env.cons_mem hV hE0)))
    have ⟨h1, h2⟩ := sat_and.1 h
    have ⟨h2, h3⟩ := sat_and.1 h2
    have ⟨h3, h4⟩ := sat_and.1 h3
    have ⟨v1, v2⟩ := (hN.sat_validNextF hE4 h0 hsucc 3 1 8 (Equiv.refl _)).1 h3
    have ⟨t1, t2⟩ := (hN.sat_truthNextF hE4 h0 hsucc 6 7 8 1 2 0 (Equiv.refl _)).1 h4
    exact ⟨V, T, V', T', hV, hT, hV', hT', (hN.sat_pairF hE4 4 3 2).1 h1, (hN.sat_pairF hE4 5 1 0).1 h2,
      v1, v2, t1, t2⟩
  · intro h
    refine Stable.of_nn h fun ⟨V, T, V', T', hV, hT, hV', hT', e1, e2, st⟩ => ?_
    have hE4 := Env.cons_mem hT' (Env.cons_mem hV' (Env.cons_mem hT (Env.cons_mem hV hE0)))
    exact sat_ex.2 (nn_intro ⟨V, hV, sat_ex.2 (nn_intro ⟨T, hT, sat_ex.2 (nn_intro ⟨V', hV', sat_ex.2 (nn_intro ⟨T', hT',
      sat_and.2 ⟨(hN.sat_pairF hE4 4 3 2).2 e1, sat_and.2 ⟨(hN.sat_pairF hE4 5 1 0).2 e2, sat_and.2
        ⟨(hN.sat_validNextF hE4 h0 hsucc 3 1 8 (Equiv.refl _)).2 ⟨st.1, st.2.1⟩,
         (hN.sat_truthNextF hE4 h0 hsucc 6 7 8 1 2 0 (Equiv.refl _)).2 ⟨st.2.2.1, st.2.2.2⟩⟩⟩⟩⟩)⟩)⟩)⟩)

end TransClass

/-! ### Congruence -/

theorem VBody.congr {V q q' n n' : PSet.{u}} (eq : q ≈ q') (en : n ≈ n') (h : VBody V q n) : VBody V q' n' :=
  ⟨(mem_congr_left en).1 h.1, nn_map (fun
    | .inl h => .inl (nn_map (fun ⟨i, j, hi, hj, hc⟩ => ⟨i, j, (mem_congr_right en).1 hi, (mem_congr_right en).1 hj,
        nn_map (fun
          | .inl e => .inl (eq.symm.trans e)
          | .inr e => .inr (eq.symm.trans e)) hc⟩) h)
    | .inr h => .inr (nn_map (fun
      | .inl e => .inl (eq.symm.trans e)
      | .inr h => .inr (nn_map (fun
        | .inl h => .inl (nn_map (fun ⟨p, r, e, hp, hr⟩ => ⟨p, r, eq.symm.trans e,
            (mem_congr_left (pair_congr (Equiv.refl _) en)).1 hp, (mem_congr_left (pair_congr (Equiv.refl _) en)).1 hr⟩) h)
        | .inr h => .inr (nn_map (fun ⟨p, e, hp⟩ => ⟨p, eq.symm.trans e,
            (mem_congr_left (pair_congr (Equiv.refl _) (succ_congr en))).1 hp⟩) h)) h)) h)) h.2⟩

theorem IsAssign.congr {A e e' n : PSet.{u}} (ee : e ≈ e') (h : IsAssign A e n) : IsAssign A e' n :=
  ⟨h.1, fun q hq => h.2.1 q ((mem_congr_right ee).2 hq),
   fun i hi => nn_map (fun ⟨v, hv⟩ => ⟨v, (mem_congr_right ee).1 hv⟩) (h.2.2.1 i hi),
   fun i v v' h1 h2 => h.2.2.2 i v v' ((mem_congr_right ee).2 h1) ((mem_congr_right ee).2 h2)⟩

theorem IsCons.congr_tail {u x e e' : PSet.{u}} (ee : e ≈ e') (h : IsCons u x e) : IsCons u x e' :=
  ⟨h.1, fun i v hiv => h.2.1 i v ((mem_congr_right ee).2 hiv), fun i v hiv => (mem_congr_right ee).1 (h.2.2.1 i v hiv),
   fun q hq => nn_map (fun
     | .inl e1 => .inl e1
     | .inr h => .inr (nn_map (fun ⟨i, v, hiv, e2⟩ => ⟨i, v, (mem_congr_right ee).1 hiv, e2⟩) h)) (h.2.2.2 q hq)⟩

theorem TBody.congr {A E V' T q q' e e' : PSet.{u}} (eq : q ≈ q') (ee : e ≈ e') (h : TBody A E V' T q e) :
    TBody A E V' T q' e' :=
  nn_map (fun ⟨n, ha, hv, hb⟩ => ⟨n, ha.congr ee, (mem_congr_left (pair_congr eq (Equiv.refl _))).1 hv,
    nn_map (fun
      | .inl h => .inl (nn_map (fun ⟨i, j, x, y, hc, hix, hjy, hxy⟩ => ⟨i, j, x, y, eq.symm.trans hc,
          (mem_congr_right ee).1 hix, (mem_congr_right ee).1 hjy, hxy⟩) h)
      | .inr h => .inr (nn_map (fun
        | .inl h => .inl (nn_map (fun ⟨i, j, x, y, hc, hix, hjy, hxy⟩ => ⟨i, j, x, y, eq.symm.trans hc,
            (mem_congr_right ee).1 hix, (mem_congr_right ee).1 hjy, hxy⟩) h)
        | .inr h => .inr (nn_map (fun
          | .inl h => .inl (nn_map (fun ⟨p, r, hc, hpr⟩ => ⟨p, r, eq.symm.trans hc, fun hp =>
              (mem_congr_left (pair_congr (Equiv.refl _) ee)).1
                (hpr ((mem_congr_left (pair_congr (Equiv.refl _) ee)).2 hp))⟩) h)
          | .inr h => .inr (nn_map (fun ⟨p, hc, hall⟩ => ⟨p, eq.symm.trans hc, fun x hx =>
              nn_map (fun ⟨u, hu, hcons, hpu⟩ => ⟨u, hu, hcons.congr_tail ee, hpu⟩) (hall x hx)⟩) h)) h)) h)) hb⟩) h

theorem TBody.congr_table {A E V' V'' T q e : PSet.{u}} (ev : V' ≈ V'') (h : TBody A E V' T q e) :
    TBody A E V'' T q e :=
  nn_map (fun ⟨n, ha, hv, hb⟩ => ⟨n, ha, (mem_congr_right ev).1 hv, hb⟩) h

/-- **Functionality of the step.** -/
theorem IsStep.unique {A E V T V' T' V'' T'' : PSet.{u}} (h : IsStep A E V T V' T') (h' : IsStep A E V T V'' T'') :
    V' ≈ V'' ∧ T' ≈ T'' := by
  have eV : V' ≈ V'' := ext fun r => ⟨fun hr => Stable.of_nn (h.1 r hr) fun ⟨q, n, _, e⟩ =>
      (mem_congr_left e).2 ((h'.2.1 q n).2 ((h.2.1 q n).1 ((mem_congr_left e).1 hr))),
    fun hr => Stable.of_nn (h'.1 r hr) fun ⟨q, n, _, e⟩ =>
      (mem_congr_left e).2 ((h.2.1 q n).2 ((h'.2.1 q n).1 ((mem_congr_left e).1 hr)))⟩
  refine ⟨eV, ext fun r => ⟨fun hr => Stable.of_nn (h.2.2.1 r hr) fun ⟨q, e, he, e'⟩ => ?_,
    fun hr => Stable.of_nn (h'.2.2.1 r hr) fun ⟨q, e, he, e'⟩ => ?_⟩⟩
  · exact (mem_congr_left e').2 ((h'.2.2.2 q e he).2 (((h.2.2.2 q e he).1 ((mem_congr_left e').1 hr)).congr_table eV))
  · exact (mem_congr_left e').2 ((h.2.2.2 q e he).2 (((h'.2.2.2 q e he).1 ((mem_congr_left e').1 hr)).congr_table eV.symm))

/-! ### Totality in the class -/

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- The set of first components of the pairs in a member. -/
theorem dom_exists {V : PSet.{u}} (hV : M V) : ¬¬∃ D, M D ∧ ∀ p, p ∈ D ↔ ¬¬∃ n, PSet.pair p n ∈ V := by
  have hT := hM.toTransClass
  let U := PSet.sUnion (PSet.sUnion V)
  have hU : M U := hM.sUnion (hM.sUnion hV)
  have hE : ∀ i, M (Env.cons U (Env.cons V envω) i) := Env.cons_mem hU (Env.cons_mem hV hM.envω_mem)
  let ψ : Fml := ex (pairMemF 3 1 0)
  have key : ∀ p, M p → (Sat M ψ (Env.cons p (Env.cons U (Env.cons V envω))) ↔ ¬¬∃ n, PSet.pair p n ∈ V) := by
    intro p hp
    have he1 := Env.cons_mem hp hE
    refine sat_ex.trans ⟨fun h => nn_map (fun ⟨n, hn, hs⟩ => ⟨n, (hT.sat_pairMemF (Env.cons_mem hn he1) 3 1 0).1 hs⟩) h,
      fun h => nn_map (fun ⟨n, hn⟩ => ⟨n, (hT.of_pair_mem hV hn).2, (hT.sat_pairMemF (Env.cons_mem (hT.of_pair_mem hV hn).2 he1) 3 1 0).2 hn⟩) h⟩
  have hψ : ∀ p p' : PSet.{u}, p ≈ p' → Sat M ψ (Env.cons p (Env.cons U (Env.cons V envω))) →
      Sat M ψ (Env.cons p' (Env.cons U (Env.cons V envω))) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine nn_intro ⟨_, hM.sepM ψ hE, fun p => (mem_sep hψ).trans ⟨fun ⟨hpU, hs⟩ => (key p (hM.trans hU hpU)).1 hs, fun h => ?_⟩⟩
  have hpM : M p := (hM.stable p).dne (nn_map (fun ⟨n, hn⟩ => (hT.of_pair_mem hV hn).1) h)
  refine ⟨mem_sUnion.2 (nn_map (fun ⟨n, hn⟩ => ⟨singleton p, mem_sUnion.2 (nn_intro ⟨PSet.pair p n, hn, mem_upair_left _ _⟩),
    self_mem_singleton p⟩) h), (key p hpM).2 h⟩

/-- A member containing every code scoped by the step from a table `V`. -/
theorem codes_exists {V : PSet.{u}} (hV : M V) :
    ¬¬∃ C, M C ∧ ∀ q n, VBody V q n → q ∈ C := by
  have hT := hM.toTransClass
  refine nn_bind (hM.dom_exists hV) fun ⟨D, hD, hDm⟩ => ?_
  refine nn_bind (hM.prodM hM.omega hM.omega) fun ⟨P₁, hP₁, hP₁m⟩ => ?_
  refine nn_bind (hM.prodM hD hD) fun ⟨P₂, hP₂, hP₂m⟩ => ?_
  have hn : ∀ k, M (ofNat k) := TransClass.ofNat_mem hM.empty hM.succ_mem
  refine nn_bind (hM.prodM (hM.upair (hn 0) (hn 1)) hP₁) fun ⟨At, hAt, hAtm⟩ => ?_
  refine nn_bind (hM.prodM (hM.single (hn 3)) hP₂) fun ⟨Im, hIm, hImm⟩ => ?_
  refine nn_map (fun ⟨Al, hAl, hAlm⟩ => ?_) (hM.prodM (hM.single (hn 4)) hD)
  let Bt := singleton (PSet.pair (ofNat 2) PSet.empty)
  have hBt : M Bt := hM.single (hM.pair (hn 2) hM.empty)
  refine ⟨PSet.union At (PSet.union Bt (PSet.union Im Al)), hM.union hAt (hM.union hBt (hM.union hIm hAl)), fun q n hb => ?_⟩
  have hnω := hb.1
  refine Stable.of_nn hb.2 fun
    | .inl h => Stable.of_nn h fun ⟨i, j, hi, hj, hc⟩ => ?_
    | .inr h => Stable.of_nn h fun
      | .inl e => mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inl (mem_singleton.2 e))))))
      | .inr h => Stable.of_nn h fun
        | .inl h => Stable.of_nn h fun ⟨p, r, e, hp, hr⟩ => ?_
        | .inr h => Stable.of_nn h fun ⟨p, e, hp⟩ => ?_
  · have hij : PSet.pair i j ∈ P₁ := (hP₁m _).2 (nn_intro ⟨i, j, isOrd_omega.trans _ hnω i hi, isOrd_omega.trans _ hnω j hj, Equiv.refl _⟩)
    refine mem_union.2 (nn_intro (.inl ((hAtm q).2 (nn_map (fun
      | .inl e => ⟨ofNat 0, PSet.pair i j, mem_upair_left _ _, hij, e⟩
      | .inr e => ⟨ofNat 1, PSet.pair i j, mem_upair_right _ _, hij, e⟩) hc))))
  · have hpD : p ∈ D := (hDm p).2 (nn_intro ⟨n, hp⟩)
    have hrD : r ∈ D := (hDm r).2 (nn_intro ⟨n, hr⟩)
    exact mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inl ((hImm q).2
      (nn_intro ⟨ofNat 3, PSet.pair p r, self_mem_singleton _, (hP₂m _).2 (nn_intro ⟨p, r, hpD, hrD, Equiv.refl _⟩), e⟩))))))))))
  · have hpD : p ∈ D := (hDm p).2 (nn_intro ⟨succ n, hp⟩)
    exact mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inr (mem_union.2 (nn_intro (.inr ((hAlm q).2
      (nn_intro ⟨ofNat 4, p, self_mem_singleton _, hpD, e⟩))))))))))

/-- **Totality of the step in the class.** -/
theorem step_exists {A Ea V T : PSet.{u}} (hA : M A) (hEa : M Ea) (hV : M V) (hT : M T) :
    ¬¬∃ V' T', M V' ∧ M T' ∧ IsStep A Ea V T V' T' := by
  have hTr := hM.toTransClass
  refine nn_bind (hM.codes_exists hV) fun ⟨C, hC, hCm⟩ => ?_
  refine nn_bind (hM.prodM hC hM.omega) fun ⟨PC, hPC, hPCm⟩ => ?_
  -- the new scope table
  let EV : Nat → PSet.{u} := Env.cons PC (Env.cons V (Env.cons PSet.omega envω))
  have hEV : ∀ i, M (EV i) := Env.cons_mem hPC (Env.cons_mem hV (Env.cons_mem hM.omega hM.envω_mem))
  let ψV : Fml := ex (ex (and (pairF 2 1 0) (validBodyF 4 1 0 5)))
  have keyV : ∀ r, M r → (Sat M ψV (Env.cons r EV) ↔ ¬¬∃ q n, r ≈ PSet.pair q n ∧ VBody V q n) := by
    intro r hr
    have he1 := Env.cons_mem hr hEV
    refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨q, hq, h⟩ => nn_map (fun ⟨n, hn, h⟩ => ?_) (sat_ex.1 h),
      fun h => nn_bind h fun ⟨q, n, e, hb⟩ => ?_⟩
    · have he3 := Env.cons_mem hn (Env.cons_mem hq he1)
      have ⟨h1, h2⟩ := sat_and.1 h
      exact ⟨q, n, (hTr.sat_pairF he3 2 1 0).1 h1, (hTr.sat_validBodyF he3 hM.empty hM.succ_mem 4 1 0 5 (Equiv.refl _)).1 h2⟩
    · have ⟨hq, hn⟩ := hTr.of_pair_class (hM.resp e hr)
      have he3 := Env.cons_mem hn (Env.cons_mem hq he1)
      exact nn_intro ⟨q, hq, sat_ex.2 (nn_intro ⟨n, hn, sat_and.2 ⟨(hTr.sat_pairF he3 2 1 0).2 e,
        (hTr.sat_validBodyF he3 hM.empty hM.succ_mem 4 1 0 5 (Equiv.refl _)).2 hb⟩⟩)⟩
  have hψV : ∀ r r' : PSet.{u}, r ≈ r' → Sat M ψV (Env.cons r EV) → Sat M ψV (Env.cons r' EV) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  let V' := sep (fun r => Sat M ψV (Env.cons r EV)) PC
  have hV' : M V' := hM.sepM ψV hEV
  have memV' : ∀ q n, PSet.pair q n ∈ V' ↔ VBody V q n := by
    intro q n
    refine (mem_sep hψV).trans ⟨fun ⟨hp, hs⟩ => ?_, fun hb => ?_⟩
    · refine Stable.of_nn ((keyV _ (hM.trans hPC hp)).1 hs) fun ⟨q', n', e, hb⟩ => ?_
      have ⟨eqq, en⟩ := pair_inj e
      exact hb.congr eqq.symm en.symm
    · have hqC : q ∈ C := hCm q n hb
      have hp : PSet.pair q n ∈ PC := (hPCm _).2 (nn_intro ⟨q, n, hqC, hb.1, Equiv.refl _⟩)
      exact ⟨hp, (keyV _ (hM.trans hPC hp)).2 (nn_intro ⟨q, n, Equiv.refl _, hb⟩)⟩
  have pureV' : ∀ r, r ∈ V' → ¬¬∃ q n, n ∈ PSet.omega ∧ r ≈ PSet.pair q n := fun r hr =>
    nn_map (fun ⟨q, n, _, hn, e⟩ => ⟨q, n, hn, e⟩) ((hPCm r).1 ((mem_sep hψV).1 hr).1)
  -- the new truth table
  refine nn_map (fun ⟨PT, hPT, hPTm⟩ => ?_) (hM.prodM hC hEa)
  let ET : Nat → PSet.{u} := Env.cons PT (Env.cons V' (Env.cons T (Env.cons A (Env.cons Ea (Env.cons PSet.omega envω)))))
  have hET : ∀ i, M (ET i) := Env.cons_mem hPT (Env.cons_mem hV' (Env.cons_mem hT (Env.cons_mem hA
    (Env.cons_mem hEa (Env.cons_mem hM.omega hM.envω_mem)))))
  let ψT : Fml := ex (ex (and (pairF 2 1 0) (truthBodyF 6 7 8 4 5 1 0)))
  have keyT : ∀ r, M r → (Sat M ψT (Env.cons r ET) ↔ ¬¬∃ q e, M q ∧ r ≈ PSet.pair q e ∧ TBody A Ea V' T q e) := by
    intro r hr
    have he1 := Env.cons_mem hr hET
    refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨q, hq, h⟩ => nn_map (fun ⟨e, he, h⟩ => ?_) (sat_ex.1 h),
      fun h => nn_bind h fun ⟨q, e, hq, e', hb⟩ => ?_⟩
    · have he3 := Env.cons_mem he (Env.cons_mem hq he1)
      have ⟨h1, h2⟩ := sat_and.1 h
      exact ⟨q, e, hq, (hTr.sat_pairF he3 2 1 0).1 h1,
        (hTr.sat_truthBodyF he3 hM.empty hM.succ_mem 6 7 8 4 5 1 0 (Equiv.refl _) hq).1 h2⟩
    · have he := (hTr.of_pair_class (hM.resp e' hr)).2
      have he3 := Env.cons_mem he (Env.cons_mem hq he1)
      exact nn_intro ⟨q, hq, sat_ex.2 (nn_intro ⟨e, he, sat_and.2 ⟨(hTr.sat_pairF he3 2 1 0).2 e',
        (hTr.sat_truthBodyF he3 hM.empty hM.succ_mem 6 7 8 4 5 1 0 (Equiv.refl _) hq).2 hb⟩⟩)⟩
  have hψT : ∀ r r' : PSet.{u}, r ≈ r' → Sat M ψT (Env.cons r ET) → Sat M ψT (Env.cons r' ET) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  let T' := sep (fun r => Sat M ψT (Env.cons r ET)) PT
  have hT' : M T' := hM.sepM ψT hET
  refine ⟨V', T', hV', hT', pureV', memV', fun r hr => ?_, fun q e he => ?_⟩
  · exact nn_map (fun ⟨q, e, _, he, e'⟩ => ⟨q, e, he, e'⟩) ((hPTm r).1 ((mem_sep hψT).1 hr).1)
  · refine (mem_sep hψT).trans ⟨fun ⟨hp, hs⟩ => ?_, fun hb => ?_⟩
    · refine Stable.of_nn ((keyT _ (hM.trans hPT hp)).1 hs) fun ⟨q', e', _, ee, hb⟩ => ?_
      have ⟨eqq, en⟩ := pair_inj ee
      exact hb.congr eqq.symm en.symm
    · -- the code is scoped, hence in the carrier and in the class
      refine Stable.of_nn hb fun ⟨n, _, hv, _⟩ => ?_
      have hqC : q ∈ C := Stable.of_nn ((hPCm _).1 ((mem_sep hψV).1 hv).1) fun ⟨q', _, hq', _, e'⟩ =>
        (mem_congr_left (pair_inj e').1).2 hq'
      have hq : M q := hM.trans hC hqC
      have hp : PSet.pair q e ∈ PT := (hPTm _).2 (nn_intro ⟨q, e, hqC, he, Equiv.refl _⟩)
      exact ⟨hp, (keyT _ (hM.trans hPT hp)).2 (nn_intro ⟨q, e, hq, Equiv.refl _, hb⟩)⟩

end SynZF

/-- info: 'PSet.SynZF.step_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.step_exists
/-- info: 'PSet.IsStep.unique' does not depend on any axioms -/
#guard_msgs in #print axioms IsStep.unique
/-- info: 'PSet.TransClass.sat_stepFormula' does not depend on any axioms -/
#guard_msgs in #print axioms TransClass.sat_stepFormula

end PSet
