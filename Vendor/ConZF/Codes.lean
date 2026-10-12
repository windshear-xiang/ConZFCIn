import Vendor.ConZF.Assign
/-!
Formula codes as sets (gate 2, checkpoint 2, first part). The codes are the existing `Fml.enc`:
a Kuratowski pair of a numeral tag and the payload. Numeral formulas `numF k` (`Bound 1`) read
`x ≈ ofNat k` (`sat_numF`); the five constructor formulas read the exact code shapes
(`sat_memCodeF`, `sat_eqCodeF`, `sat_botCodeF`, `sat_impCodeF`, `sat_allCodeF`), so tag
disjointness and pair injectivity give constructor disjointness and injectivity, and with
`enc_inj` a represented code decodes uniquely. Everything is over a transitive pair-closed
class with environments in the class.
-/
universe u

namespace PSet
open Fml CardF RecF

namespace CodeF

/-- `x ≈ ofNat k`, as a chain of successor formulas. -/
def numF : Nat → Nat → Fml
  | 0, x => emptyF x
  | k+1, x => ex (and (numF k 0) (succF (x+1) 0))

/-- `q ≈ pair (ofNat t) (pair i j)`. -/
def tagPairF (t q i j : Nat) : Fml :=
  ex (ex (and (numF t 1) (and (pairF 0 (i+2) (j+2)) (pairF (q+2) 1 0))))

def memCodeF (q i j : Nat) : Fml := tagPairF 0 q i j
def eqCodeF (q i j : Nat) : Fml := tagPairF 1 q i j
/-- `q ≈ pair (ofNat 2) ∅`; the payload must be empty. -/
def botCodeF (q : Nat) : Fml := ex (ex (and (numF 2 1) (and (emptyF 0) (pairF (q+2) 1 0))))
def impCodeF (q p r : Nat) : Fml := tagPairF 3 q p r
/-- `q ≈ pair (ofNat 4) p`. -/
def allCodeF (q p : Nat) : Fml := ex (and (numF 4 0) (pairF (q+1) 0 (p+1)))

end CodeF

open CodeF

namespace TransClass
variable {M : PSet.{u} → Prop} (hN : TransClass M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hN hE

omit hN hE in
theorem ofNat_mem (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) : ∀ k, M (ofNat k)
  | 0 => h0
  | k+1 => hsucc (ofNat_mem h0 hsucc k)

omit hE in
theorem sat_numF' (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) :
    ∀ (k x : Nat) {E : Nat → PSet.{u}}, (∀ i, M (E i)) → (Sat M (numF k x) E ↔ E x ≈ ofNat k)
  | 0, x, _, hE => hN.sat_emptyF hE x
  | k+1, x, E, hE => by
    refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨y, hy, hs⟩ => ?_, fun h => ?_⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      have he1 := Env.cons_mem hy hE
      exact ((hN.sat_succF he1 (x+1) 0).1 h2).trans (succ_congr ((sat_numF' h0 hsucc k 0 he1).1 h1))
    · have hk : M (ofNat k) := ofNat_mem h0 hsucc k
      have he1 := Env.cons_mem hk hE
      exact nn_intro ⟨ofNat k, hk, sat_and.2 ⟨(sat_numF' h0 hsucc k 0 he1).2 (Equiv.refl _),
        (hN.sat_succF he1 (x+1) 0).2 h⟩⟩

theorem sat_numF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (k x : Nat) :
    Sat M (numF k x) E ↔ E x ≈ ofNat k := hN.sat_numF' h0 hsucc k x hE

theorem sat_tagPairF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (t q i j : Nat) :
    Sat M (tagPairF t q i j) E ↔ E q ≈ pair (ofNat t) (pair (E i) (E j)) := by
  refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨tt, ht, hs⟩ => Stable.of_nn (sat_ex.1 hs) fun ⟨p, hp, hs⟩ => ?_,
    fun h => ?_⟩
  · have he2 := Env.cons_mem hp (Env.cons_mem ht hE)
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h2, h3⟩ := sat_and.1 h2
    have et := (hN.sat_numF he2 h0 hsucc t 1).1 h1
    have ep := (hN.sat_pairF he2 0 (i+2) (j+2)).1 h2
    exact ((hN.sat_pairF he2 (q+2) 1 0).1 h3).trans (pair_congr et ep)
  · have hk : M (ofNat t) := ofNat_mem h0 hsucc t
    have hp : M (pair (E i) (E j)) := hN.pair_mem (hE i) (hE j)
    have he2 := Env.cons_mem hp (Env.cons_mem hk hE)
    exact nn_intro ⟨ofNat t, hk, sat_ex.2 (nn_intro ⟨_, hp, sat_and.2 ⟨(hN.sat_numF he2 h0 hsucc t 1).2 (Equiv.refl _),
      sat_and.2 ⟨(hN.sat_pairF he2 0 (i+2) (j+2)).2 (Equiv.refl _), (hN.sat_pairF he2 (q+2) 1 0).2 h⟩⟩⟩)⟩

theorem sat_memCodeF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (q i j : Nat) :
    Sat M (memCodeF q i j) E ↔ E q ≈ pair (ofNat 0) (pair (E i) (E j)) := hN.sat_tagPairF hE h0 hsucc 0 q i j
theorem sat_eqCodeF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (q i j : Nat) :
    Sat M (eqCodeF q i j) E ↔ E q ≈ pair (ofNat 1) (pair (E i) (E j)) := hN.sat_tagPairF hE h0 hsucc 1 q i j
theorem sat_impCodeF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (q p r : Nat) :
    Sat M (impCodeF q p r) E ↔ E q ≈ pair (ofNat 3) (pair (E p) (E r)) := hN.sat_tagPairF hE h0 hsucc 3 q p r

theorem sat_botCodeF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (q : Nat) :
    Sat M (botCodeF q) E ↔ E q ≈ pair (ofNat 2) empty := by
  refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨tt, ht, hs⟩ => Stable.of_nn (sat_ex.1 hs) fun ⟨z, hz, hs⟩ => ?_,
    fun h => ?_⟩
  · have he2 := Env.cons_mem hz (Env.cons_mem ht hE)
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h2, h3⟩ := sat_and.1 h2
    exact ((hN.sat_pairF he2 (q+2) 1 0).1 h3).trans (pair_congr ((hN.sat_numF he2 h0 hsucc 2 1).1 h1)
      ((hN.sat_emptyF he2 0).1 h2))
  · have h2 : M (ofNat 2) := hsucc (hsucc h0)
    have he2 := Env.cons_mem h0 (Env.cons_mem h2 hE)
    exact nn_intro ⟨ofNat 2, h2, sat_ex.2 (nn_intro ⟨empty, h0, sat_and.2 ⟨(hN.sat_numF he2 h0 hsucc 2 1).2 (Equiv.refl _),
      sat_and.2 ⟨(hN.sat_emptyF he2 0).2 (Equiv.refl _), (hN.sat_pairF he2 (q+2) 1 0).2 h⟩⟩⟩)⟩

theorem sat_allCodeF (h0 : M empty) (hsucc : ∀ {y}, M y → M (succ y)) (q p : Nat) :
    Sat M (allCodeF q p) E ↔ E q ≈ pair (ofNat 4) (E p) := by
  refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨tt, ht, hs⟩ => ?_, fun h => ?_⟩
  · have he1 := Env.cons_mem ht hE
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact ((hN.sat_pairF he1 (q+1) 0 (p+1)).1 h2).trans (pair_congr ((hN.sat_numF he1 h0 hsucc 4 0).1 h1) (Equiv.refl _))
  · have h4 : M (ofNat 4) := hsucc (hsucc (hsucc (hsucc h0)))
    have he1 := Env.cons_mem h4 hE
    exact nn_intro ⟨ofNat 4, h4, sat_and.2 ⟨(hN.sat_numF he1 h0 hsucc 4 0).2 (Equiv.refl _),
      (hN.sat_pairF he1 (q+1) 0 (p+1)).2 h⟩⟩

end TransClass

/-! ### Tag disjointness -/

theorem ofNat_ne_of_ne {m n : Nat} (h : m ≠ n) : ¬ ofNat.{u} m ≈ ofNat n := fun e => h (ofNat_inj e)

/-- The codes of the constructors are disjoint and injective, from pair injectivity and tag
distinctness; a represented code determines its native formula (`enc_inj`). -/
theorem enc_shape : ∀ φ : Fml, ∃ t : Nat, ∃ payload : PSet.{u}, enc φ ≈ pair (ofNat t) payload ∧ t < 5
  | .mem i j => ⟨0, _, Equiv.refl _, by decide⟩
  | .eq i j => ⟨1, _, Equiv.refl _, by decide⟩
  | .fls => ⟨2, _, Equiv.refl _, by decide⟩
  | .imp _ _ => ⟨3, _, Equiv.refl _, by decide⟩
  | .all _ => ⟨4, _, Equiv.refl _, by decide⟩

/-- info: 'PSet.TransClass.sat_allCodeF' does not depend on any axioms -/
#guard_msgs in #print axioms TransClass.sat_allCodeF
/-- info: 'PSet.TransClass.sat_botCodeF' does not depend on any axioms -/
#guard_msgs in #print axioms TransClass.sat_botCodeF

end PSet
