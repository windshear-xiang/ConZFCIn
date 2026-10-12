import Vendor.ConZF.Relativize
import Vendor.ConZF.Cardinal
/-!
The finite-fragment reflection compiler (conzf16, ported from the supplied syntax draft, with
the relativizer `Fml.restrictClass` reused). Native data: a computed free-variable bound
`fv` (`bound_fv`); the counterexample requests of the raw universal nodes of a formula
(`requests`, every request valid: `requests_valid`); the capture formula of a request, with
free variables `A = 0`, `B = 1` (`capture`, `Bound 2`); the conjunction `closes` over the
requests of a native finite list; the good-stage formula and the least-next-stage formula
`nextF` over supplied unary `ell` and binary `level` templates (`Bound 2`); the set-relativized
formula `setRel` and the reflection sentence `reflectionAt` (`Bound 1`).

Scope lemmas: renaming with a bounded renaming (`bound_rename`), relativization preserves
every bound including `0` (`bound_restrictClass`), and the bounds of every compiled formula.
Semantics: conjunctions (`sat_conjoin`), iterated universals (`sat_allN`, as the recursive
`SatAll`), guards (`sat_guardsF`), the two-slot instantiation (`sat_at2`), and the exact
capture law (`sat_capture_body`): inside the parameter binders, if the parameters lie in `A`
and some member of the defined class satisfies the request's matrix in the defined class, then
some such member lies in `B`. The internal existence of the next stage and the reflection
theorem are not proved here.
-/
universe u

namespace PSet
open Fml

namespace Fml

theorem le_pred_succ : ∀ k : Nat, k ≤ k.pred + 1
  | 0 => Nat.zero_le _
  | _+1 => Nat.le_refl _

/-- A native, computed free-variable bound. -/
def fv : Fml → Nat
  | .mem i j | .eq i j => nmax i j + 1
  | .fls => 0
  | .imp p q => nmax (fv p) (fv q)
  | .all p => (fv p).pred

theorem bound_fv : ∀ p : Fml, Bound (fv p) p
  | .mem i j | .eq i j => ⟨Nat.lt_succ_of_le (le_nmax_left i j), Nat.lt_succ_of_le (le_nmax_right i j)⟩
  | .fls => trivial
  | .imp p q => ⟨(bound_fv p).mono (le_nmax_left _ _), (bound_fv q).mono (le_nmax_right _ _)⟩
  | .all p => show Bound ((fv p).pred + 1) p from (bound_fv p).mono (le_pred_succ _)

/-- Renaming with a renaming bounded on the free variables. -/
theorem bound_rename : ∀ {p : Fml} {k m : Nat} {ρ : Nat → Nat}, Bound k p →
    (∀ i, i < k → ρ i < m) → Bound m (rename ρ p)
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => ⟨h i hi, h j hj⟩
  | .eq i j, _, _, _, ⟨hi, hj⟩, h => ⟨h i hi, h j hj⟩
  | .fls, _, _, _, _, _ => trivial
  | .imp _ _, _, _, _, ⟨h1, h2⟩, h => ⟨bound_rename h1 h, bound_rename h2 h⟩
  | .all p, _, _, ρ, h1, h => bound_rename (p := p) h1 fun i hi => by
      cases i with
      | zero => exact Nat.succ_pos _
      | succ i => exact Nat.succ_lt_succ (h i (Nat.lt_of_succ_lt_succ hi))

/-- Relativization preserves every bound, including `0`. -/
theorem bound_restrictClass {ell : Fml} (hell : Bound 1 ell) :
    ∀ {p : Fml} {k : Nat}, Bound k p → Bound k (restrictClass ell p)
  | .mem _ _, _, h | .eq _ _, _, h => h
  | .fls, _, h => h
  | .imp _ _, _, ⟨h1, h2⟩ => ⟨bound_restrictClass hell h1, bound_restrictClass hell h2⟩
  | .all p, k, h => ⟨hell.mono (Nat.succ_le_succ (Nat.zero_le k)), bound_restrictClass hell (p := p) h⟩

theorem Bound.and {k : Nat} {φ ψ : Fml} (h1 : Bound k φ) (h2 : Bound k ψ) : Bound k (and φ ψ) :=
  ⟨⟨h1, h2, trivial⟩, trivial⟩
theorem Bound.neg {k : Nat} {φ : Fml} (h : Bound k φ) : Bound k (neg φ) := ⟨h, trivial⟩
theorem Bound.ex {k : Nat} {φ : Fml} (h : Bound (k+1) φ) : Bound k (ex φ) := ⟨⟨h, trivial⟩, trivial⟩
theorem Bound.iff {k : Nat} {φ ψ : Fml} (h1 : Bound k φ) (h2 : Bound k ψ) : Bound k (iff φ ψ) :=
  Bound.and ⟨h1, h2⟩ ⟨h2, h1⟩
theorem Bound.or {k : Nat} {φ ψ : Fml} (h1 : Bound k φ) (h2 : Bound k ψ) : Bound k (or φ ψ) :=
  ⟨⟨h1, trivial⟩, h2⟩

end Fml

namespace Reflection
open Fml CardF

/-- A counterexample request: an arity and a matrix whose variable `0` is the witness. -/
structure Matrix where
  arity : Nat
  body : Fml

/-- The requests of the raw universal nodes. -/
def requests : Fml → List Matrix
  | .mem _ _ | .eq _ _ | .fls => []
  | .imp p q => requests p ++ requests q
  | .all p => ⟨(fv p).pred, neg p⟩ :: requests p

def matrices : List Fml → List Matrix
  | [] => []
  | p :: ps => requests p ++ matrices ps

theorem mem_append_elim {α : Type} {a : α} : ∀ {s t : List α}, a ∈ s ++ t → a ∈ s ∨ a ∈ t
  | [], _, h => .inr h
  | _ :: s, t, h => by
    cases h with
    | head => exact .inl (.head _)
    | tail _ h => exact (mem_append_elim (s := s) (t := t) h).elim (fun h => .inl (.tail _ h)) .inr

/-- Every generated request has its witness variable `0` and parameters `1, …, arity`. -/
theorem requests_valid : ∀ (p : Fml) (m : Matrix), m ∈ requests p → Bound (m.arity + 1) m.body
  | .mem _ _, _, h | .eq _ _, _, h | .fls, _, h => nomatch h
  | .imp p q, m, h => (mem_append_elim h).elim (requests_valid p m) (requests_valid q m)
  | .all p, m, h => by
    cases h with
    | head => exact ((bound_fv p).mono (le_pred_succ _)).neg
    | tail _ h => exact requests_valid p m h

theorem matrices_valid : ∀ (Δ : List Fml) (m : Matrix), m ∈ matrices Δ → Bound (m.arity + 1) m.body
  | [], _, h => nomatch h
  | p :: ps, m, h => (mem_append_elim h).elim (requests_valid p m) (matrices_valid ps m)

def trueF : Fml := .imp .fls .fls

def conjoin : List Fml → Fml
  | [] => trueF
  | p :: ps => and p (conjoin ps)

def allN : Nat → Fml → Fml
  | 0, p => p
  | n+1, p => .all (allN n p)

/-- `p₀ ∈ A ∧ … ∧ p_{k-1} ∈ A`, with `A` at index `n`. -/
def guardsF (n : Nat) : Nat → Fml
  | 0 => trueF
  | k+1 => and (mem k n) (guardsF n k)

/-- Instantiate a formula of `Bound 2` at the variables `i, j`. -/
def at2 (p : Fml) (i j : Nat) : Fml := rename (fun k => if k = 0 then i else if k = 1 then j else 0) p

/-- **The capture formula** of a request, free variables `A = 0`, `B = 1`: for all parameters in
`A`, if some `z` in the class satisfies the matrix in the class, some such `z` lies in `B`.
Inside the binders the environment is `[p₀, …, p_{n-1}, A, B, …]`, under the existentials
`[z, p₀, …, p_{n-1}, A, B, …]`. -/
def capture (ell : Fml) (m : Matrix) : Fml :=
  let n := m.arity
  let test := and ell (restrictClass ell m.body)
  allN n (.imp (guardsF n n) (.imp (ex test) (ex (and (mem 0 (n+2)) test))))

def closes (ell : Fml) (Δ : List Fml) : Fml := conjoin ((matrices Δ).map (capture ell))

/-- `Bound 2`, free `α = 0`, `β = 1`: `β > α` are ordinals and the levels at `α, β` close `Δ`.
After the two existentials the environment is `[B, A, α, β, …]`. -/
def goodF (ell level : Fml) (Δ : List Fml) : Fml :=
  conjoin [ordF 0, ordF 1, mem 0 1,
    ex (ex (conjoin [at2 level 2 1, at2 level 3 0, at2 (closes ell Δ) 1 0]))]

/-- `Bound 2`: the least `β > α` that is good. -/
def nextF (ell level : Fml) (Δ : List Fml) : Fml :=
  and (goodF ell level Δ) (.all (.imp (mem 0 2) (neg (at2 (goodF ell level Δ) 1 0))))

/-- Relativize the quantifiers to the set named by the extra free variable `a`. -/
def setRel (a : Nat) : Fml → Fml
  | .mem i j => .mem i j
  | .eq i j => .eq i j
  | .fls => .fls
  | .imp p q => .imp (setRel a p) (setRel a q)
  | .all p => .all (.imp (.mem 0 (a+1)) (setRel (a+1) p))

/-- `Bound 1`, free `B = 0`: for all relevant parameters in `B`, `p` holds in the class iff in
`B`. -/
def reflectionClause (ell p : Fml) : Fml :=
  let n := fv p
  allN n (.imp (guardsF n n) (iff (restrictClass ell p) (setRel n p)))

def reflectionAt (ell : Fml) (Δ : List Fml) : Fml := conjoin (Δ.map (reflectionClause ell))

/-! ### Scope -/

theorem bound_trueF {k : Nat} : Bound k trueF := ⟨trivial, trivial⟩

theorem bound_conjoin {k : Nat} : ∀ {l : List Fml}, (∀ q, q ∈ l → Bound k q) → Bound k (conjoin l)
  | [], _ => bound_trueF
  | _ :: _, h => (h _ (.head _)).and (bound_conjoin fun q hq => h q (.tail _ hq))

theorem bound_allN {k n : Nat} {p : Fml} (h : Bound (k + n) p) : Bound k (allN n p) := by
  induction n generalizing k with
  | zero => exact h
  | succ n ih => exact ih (k := k+1) (by rw [Nat.succ_add]; exact h)

theorem bound_guardsF {n k : Nat} (h : k ≤ n) : Bound (n+1) (guardsF n k) := by
  induction k with
  | zero => exact bound_trueF
  | succ k ih => exact Bound.and ⟨Nat.lt_succ_of_lt h, Nat.lt_succ_self n⟩ (ih (Nat.le_of_succ_le h))

theorem bound_at2 {p : Fml} {i j m : Nat} (hp : Bound 2 p) (hi : i < m) (hj : j < m) :
    Bound m (at2 p i j) :=
  bound_rename hp fun k hk => by
    rcases k with _ | _ | k
    · exact hi
    · exact hj
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hk))).elim

theorem bound_capture {ell : Fml} (hell : Bound 1 ell) {m : Matrix} (hm : Bound (m.arity + 1) m.body) :
    Bound 2 (capture ell m) := by
  have htest : Bound (m.arity + 1) (and ell (restrictClass ell m.body)) :=
    (hell.mono (Nat.succ_le_succ (Nat.zero_le _))).and (bound_restrictClass hell hm)
  refine bound_allN (k := 2) (n := m.arity) ?_
  rw [Nat.add_comm]
  refine ⟨(bound_guardsF (Nat.le_refl _)).mono (Nat.le_succ _), ?_, ?_⟩
  · exact (Bound.ex htest).mono (Nat.le_add_right _ 2)
  · exact Bound.ex (Bound.and ⟨Nat.succ_pos _, Nat.lt_succ_self _⟩ (htest.mono (Nat.le_add_right _ 2)))

theorem bound_closes {ell : Fml} (hell : Bound 1 ell) (Δ : List Fml) : Bound 2 (closes ell Δ) := by
  refine bound_conjoin fun q hq => ?_
  have : ∀ {l : List Matrix}, q ∈ l.map (capture ell) → (∀ m, m ∈ l → Bound (m.arity + 1) m.body) →
      Bound 2 q := by
    intro l hq hl
    induction l with
    | nil => exact nomatch hq
    | cons m ms ih =>
      cases hq with
      | head => exact bound_capture hell (hl m (.head _))
      | tail _ h => exact ih h fun m' hm' => hl m' (.tail _ hm')
  exact this hq (matrices_valid Δ)

theorem bound_transF {x : Nat} : Bound (x+1) (transF x) :=
  ⟨⟨Nat.succ_pos _, Nat.succ_lt_succ (Nat.succ_pos _)⟩,
    ⟨Nat.succ_lt_succ (Nat.succ_pos _), Nat.lt_succ_self (x+2)⟩,
    ⟨Nat.succ_pos _, Nat.lt_succ_self (x+2)⟩⟩

theorem bound_ordF {x : Nat} : Bound (x+1) (ordF x) :=
  bound_transF.and ⟨⟨Nat.succ_pos _, Nat.lt_succ_self _⟩, bound_transF (x := 0) |>.mono (Nat.succ_le_succ (Nat.zero_le _))⟩

theorem bound_goodF {ell level : Fml} (hell : Bound 1 ell) (hlevel : Bound 2 level) (Δ : List Fml) :
    Bound 2 (goodF ell level Δ) := by
  refine bound_conjoin fun q hq => ?_
  rcases hq with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, h⟩⟩⟩⟩
  · exact bound_ordF.mono (Nat.le_succ _)
  · exact bound_ordF
  · exact ⟨Nat.zero_lt_succ _, Nat.lt_succ_self _⟩
  · refine Bound.ex (Bound.ex (bound_conjoin fun q hq => ?_))
    rcases hq with _ | ⟨_, _ | ⟨_, _ | ⟨_, h⟩⟩⟩
    · exact bound_at2 hlevel (by decide) (by decide)
    · exact bound_at2 hlevel (by decide) (by decide)
    · exact bound_at2 (bound_closes hell Δ) (by decide) (by decide)
    · exact nomatch h
  · exact nomatch h

theorem bound_nextF {ell level : Fml} (hell : Bound 1 ell) (hlevel : Bound 2 level) (Δ : List Fml) :
    Bound 2 (nextF ell level Δ) :=
  (bound_goodF hell hlevel Δ).and ⟨⟨Nat.zero_lt_succ _, Nat.lt_succ_self _⟩,
    (bound_at2 (bound_goodF hell hlevel Δ) (by decide) (by decide)).neg⟩

theorem bound_setRel : ∀ {p : Fml} {k a : Nat}, Bound k p → k ≤ a → Bound (a+1) (setRel a p)
  | .mem _ _, _, _, ⟨hi, hj⟩, h => ⟨Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hi h), Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hj h)⟩
  | .eq _ _, _, _, ⟨hi, hj⟩, h => ⟨Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hi h), Nat.lt_succ_of_lt (Nat.lt_of_lt_of_le hj h)⟩
  | .fls, _, _, _, _ => trivial
  | .imp _ _, _, _, ⟨h1, h2⟩, h => ⟨bound_setRel h1 h, bound_setRel h2 h⟩
  | .all p, _, a, h1, h => ⟨⟨Nat.succ_pos _, Nat.lt_succ_self _⟩,
      bound_setRel (p := p) (a := a+1) h1 (Nat.succ_le_succ h)⟩

theorem bound_reflectionClause {ell : Fml} (hell : Bound 1 ell) (p : Fml) :
    Bound 1 (reflectionClause ell p) := by
  refine bound_allN (k := 1) (n := fv p) ?_
  rw [Nat.add_comm]
  exact ⟨bound_guardsF (Nat.le_refl _), ((bound_restrictClass hell (bound_fv p)).mono (Nat.le_succ _)).iff
    (bound_setRel (bound_fv p) (Nat.le_refl _))⟩

theorem bound_reflectionAt {ell : Fml} (hell : Bound 1 ell) (Δ : List Fml) : Bound 1 (reflectionAt ell Δ) := by
  refine bound_conjoin fun q hq => ?_
  have : ∀ {l : List Fml}, q ∈ l.map (reflectionClause ell) → Bound 1 q := by
    intro l hq
    induction l with
    | nil => exact nomatch hq
    | cons p ps ih =>
      cases hq with
      | head => exact bound_reflectionClause hell p
      | tail _ h => exact ih h
  exact this hq

/-! ### Semantics -/

variable {M : PSet.{u} → Prop}

theorem sat_trueF {e : Nat → PSet.{u}} : Sat M trueF e := fun h => h

theorem sat_conjoin {e : Nat → PSet.{u}} {l : List Fml} : Sat M (conjoin l) e ↔ ∀ q, q ∈ l → Sat M q e := by
  induction l with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => sat_trueF⟩
  | cons p ps ih =>
    refine sat_and.trans (Iff.intro (fun h q hq => ?_) fun h => ⟨h p (.head _), ih.2 fun q hq => h q (.tail _ hq)⟩)
    cases hq with
    | head => exact h.1
    | tail _ h' => exact ih.1 h.2 q h'

/-- Iterated universal quantification over the class, innermost binder at index `0`. -/
def SatAll (M : PSet.{u} → Prop) : Nat → Fml → (Nat → PSet.{u}) → Prop
  | 0, p, e => Sat M p e
  | n+1, p, e => ∀ x, M x → SatAll M n p (Env.cons x e)

theorem sat_allN {n : Nat} {p : Fml} {e : Nat → PSet.{u}} : Sat M (allN n p) e ↔ SatAll M n p e := by
  induction n generalizing e with
  | zero => exact Iff.rfl
  | succ n ih => exact ⟨fun h x hx => ih.1 (h x hx), fun h x hx => ih.2 (h x hx)⟩

theorem sat_guardsF {n : Nat} {e : Nat → PSet.{u}} {k : Nat} :
    Sat M (guardsF n k) e ↔ ∀ i, i < k → e i ∈ e n := by
  induction k with
  | zero => exact ⟨fun _ i h => (Nat.not_lt_zero i h).elim, fun _ => sat_trueF⟩
  | succ k ih =>
    refine sat_and.trans ⟨fun ⟨h1, h2⟩ i hi => ?_, fun h => ⟨h k (Nat.lt_succ_self k),
      ih.2 fun i hi => h i (Nat.lt_succ_of_lt hi)⟩⟩
    rcases Nat.lt_or_ge i k with h | h
    · exact ih.1 h2 i h
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h; exact h1

theorem sat_at2 {p : Fml} (hp : Bound 2 p) {i j : Nat} {e e' : Nat → PSet.{u}} :
    Sat M (at2 p i j) e ↔ Sat M p (Env.cons (e i) (Env.cons (e j) e')) :=
  (sat_rename p _ e).trans (sat_bound hp fun
    | 0, _ => Equiv.refl _
    | 1, _ => Equiv.refl _
    | _+2, h => (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ h))).elim)

/-- The test of a capture formula at a witness reads as membership in the defined class and
satisfaction of the matrix there. -/
theorem sat_test {ell : Fml} (hell : Bound 1 ell) {body : Fml} {E : Nat → PSet.{u}} :
    Sat M (and ell (restrictClass ell body)) E ↔
      (Sat M ell E ∧ Sat (definedClass M ell) body E) :=
  sat_and.trans (and_congr Iff.rfl (sat_restrictClass ell hell body E))

/-- With the witness in `M`, the test says the witness is in the defined class. -/
theorem sat_test' {ell : Fml} (hell : Bound 1 ell) {body : Fml} {z : PSet.{u}} {E : Nat → PSet.{u}}
    (hz : M z) : Sat M (and ell (restrictClass ell body)) (Env.cons z E) ↔
      definedClass M ell z ∧ Sat (definedClass M ell) body (Env.cons z E) :=
  (sat_test hell).trans (and_congr ⟨fun h => ⟨hz, (sat_unary hell z E).1 h⟩,
    fun h => (sat_unary hell z E).2 h.2⟩ Iff.rfl)

/-- **The exact capture law**, inside the parameter binders: with parameters in `A = E n`, if
some member of the defined class satisfies the matrix there, some such member lies in
`B = E (n+1)`. -/
theorem sat_capture_body {ell : Fml} (hell : Bound 1 ell) {m : Matrix} {E : Nat → PSet.{u}} :
    Sat M (.imp (guardsF m.arity m.arity) (.imp (ex (and ell (restrictClass ell m.body)))
      (ex (and (mem 0 (m.arity+2)) (and ell (restrictClass ell m.body)))))) E ↔
    ((∀ i, i < m.arity → E i ∈ E m.arity) →
      (¬¬∃ z, definedClass M ell z ∧ Sat (definedClass M ell) m.body (Env.cons z E)) →
      ¬¬∃ z, z ∈ E (m.arity + 1) ∧ definedClass M ell z ∧ Sat (definedClass M ell) m.body (Env.cons z E)) := by
  have G := sat_guardsF (M := M) (n := m.arity) (e := E) (k := m.arity)
  have A : Sat M (ex (and ell (restrictClass ell m.body))) E ↔
      ¬¬∃ z, definedClass M ell z ∧ Sat (definedClass M ell) m.body (Env.cons z E) :=
    sat_ex.trans (nn_congr ⟨fun ⟨z, hz, h⟩ => ⟨z, (sat_test' hell hz).1 h⟩,
      fun ⟨z, h⟩ => ⟨z, h.1.1, (sat_test' hell h.1.1).2 h⟩⟩)
  have B : Sat M (ex (and (mem 0 (m.arity+2)) (and ell (restrictClass ell m.body)))) E ↔
      ¬¬∃ z, z ∈ E (m.arity + 1) ∧ definedClass M ell z ∧ Sat (definedClass M ell) m.body (Env.cons z E) :=
    sat_ex.trans (nn_congr ⟨fun ⟨z, hz, h⟩ => have ⟨h1, h2⟩ := sat_and.1 h; ⟨z, h1, (sat_test' hell hz).1 h2⟩,
      fun ⟨z, h1, h⟩ => ⟨z, h.1.1, sat_and.2 ⟨h1, (sat_test' hell h.1.1).2 h⟩⟩⟩)
  exact ⟨fun h g x => B.1 (h (G.2 g) (A.2 x)), fun h g x => B.2 (h (G.1 g) (A.1 x))⟩

/-- info: 'PSet.Reflection.sat_capture_body' does not depend on any axioms -/
#guard_msgs in #print axioms sat_capture_body
/-- info: 'PSet.Reflection.bound_nextF' does not depend on any axioms -/
#guard_msgs in #print axioms bound_nextF
/-- info: 'PSet.Reflection.bound_reflectionAt' does not depend on any axioms -/
#guard_msgs in #print axioms bound_reflectionAt

end Reflection

end PSet
