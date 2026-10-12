import Vendor.ConZF.Cardinal

/-!
Definitions of the target theories for manual review. The formula syntax, proof system,
consistency predicate, ZF axiom schemes, choice axiom, and inaccessible formula are taken
directly from the vendored ConZF library.

The natural number `n` determines a finite closed formula. The model proofs use a separate
finite universe expansion for each externally fixed `n`.
-/

namespace ConZFCIn
open PSet PSet.Fml PSet.CardF

/-- A provable truth of the object logic. -/
def trueF : Fml := imp fls fls

/-- A chain of `n` inaccessible witnesses above the lower bound in free variable `k`.
Each witness strictly contains the preceding bound. -/
def aboveInaccF : Nat → Nat → Fml
  | 0, _ => trueF
  | n+1, k => ex (and (inaccF 0) (and (mem (k+1) 0) (aboveInaccF n 0)))

/-- A closed formula asserting at least `n` strictly increasing strongly inaccessible
cardinals. The case `n = 1` uses the upstream formula `exInacc` verbatim. -/
def atLeastInaccF : Nat → Fml
  | 0 => trueF
  | 1 => exInacc
  | n+2 => ex (and (inaccF 0) (aboveInaccF (n+1) 0))

/-- All ZF axiom schemes, the upstream choice axiom, and the closed formula asserting
at least `n` inaccessible cardinals. -/
inductive ZFCIn (n : Nat) : Fml → Prop
  | zf {p} : ZF p → ZFCIn n p
  | ac : ZFCIn n PSet.ac
  | inacc : ZFCIn n (atLeastInaccF n)

/-- ZFC without an additional inaccessible axiom, used to calibrate the case `n = 0`. -/
def ZFC (p : Fml) : Prop := ZF p ∨ p = PSet.ac

end ConZFCIn
