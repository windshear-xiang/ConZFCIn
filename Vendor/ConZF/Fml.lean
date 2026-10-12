import Vendor.ConZF.VLevel
/-!
First-order formulas of set theory with de Bruijn variables, satisfaction in a class model
`M : PSet → Prop` (quantifiers range over `M`), renaming of variables, bounds on the free
variables, and an injective coding of formulas as sets (used to put a formula into a label).
-/
universe u

namespace PSet

inductive Fml : Type
  | mem (i j : Nat)
  | eq (i j : Nat)
  | fls
  | imp (φ ψ : Fml)
  | all (φ : Fml)

namespace Fml
def neg (φ : Fml) : Fml := imp φ fls
def and (φ ψ : Fml) : Fml := neg (imp φ (neg ψ))
def or (φ ψ : Fml) : Fml := imp (neg φ) ψ
def iff (φ ψ : Fml) : Fml := and (imp φ ψ) (imp ψ φ)
def ex (φ : Fml) : Fml := neg (all (neg φ))

/-- Lifting a renaming under a binder. -/
def up (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ρ n + 1

def rename (ρ : Nat → Nat) : Fml → Fml
  | mem i j => mem (ρ i) (ρ j)
  | eq i j => eq (ρ i) (ρ j)
  | fls => fls
  | imp φ ψ => imp (rename ρ φ) (rename ρ ψ)
  | all φ => all (rename (up ρ) φ)

/-- Substitution of the variable `j` for the bound variable `0`. -/
def inst (j : Nat) : Nat → Nat
  | 0 => j
  | n+1 => n

def lift (φ : Fml) : Fml := rename Nat.succ φ

/-- All free variables of `φ` are below `k`. -/
def Bound : Nat → Fml → Prop
  | k, mem i j => i < k ∧ j < k
  | k, eq i j => i < k ∧ j < k
  | _, fls => True
  | k, imp φ ψ => Bound k φ ∧ Bound k ψ
  | k, all φ => Bound (k+1) φ

theorem Bound.mono : ∀ {φ : Fml} {k k' : Nat}, k ≤ k' → Bound k φ → Bound k' φ
  | mem _ _, _, _, h, ⟨h1, h2⟩ => ⟨Nat.lt_of_lt_of_le h1 h, Nat.lt_of_lt_of_le h2 h⟩
  | eq _ _, _, _, h, ⟨h1, h2⟩ => ⟨Nat.lt_of_lt_of_le h1 h, Nat.lt_of_lt_of_le h2 h⟩
  | fls, _, _, _, _ => trivial
  | imp _ _, _, _, h, ⟨h1, h2⟩ => ⟨Bound.mono h h1, Bound.mono h h2⟩
  | all φ, _, _, h, h1 => Bound.mono (φ := φ) (Nat.succ_le_succ h) h1

/-- `max`, by recursion (the core lemmas about `max` use `propext`). -/
def nmax : Nat → Nat → Nat
  | 0, b => b
  | a+1, 0 => a+1
  | a+1, b+1 => nmax a b + 1

theorem le_nmax_left : ∀ a b, a ≤ nmax a b
  | 0, _ => Nat.zero_le _
  | _+1, 0 => Nat.le_refl _
  | a+1, b+1 => Nat.succ_le_succ (le_nmax_left a b)

theorem le_nmax_right : ∀ a b, b ≤ nmax a b
  | 0, _ => Nat.le_refl _
  | _+1, 0 => Nat.zero_le _
  | a+1, b+1 => Nat.succ_le_succ (le_nmax_right a b)

theorem exists_bound : ∀ φ : Fml, ∃ k, Bound k φ
  | mem i j | eq i j => ⟨nmax i j + 1, Nat.lt_succ_of_le (le_nmax_left i j),
      Nat.lt_succ_of_le (le_nmax_right i j)⟩
  | fls => ⟨0, trivial⟩
  | imp φ ψ => have ⟨a, ha⟩ := exists_bound φ; have ⟨b, hb⟩ := exists_bound ψ
      ⟨nmax a b, ha.mono (le_nmax_left a b), hb.mono (le_nmax_right a b)⟩
  | all φ => have ⟨a, ha⟩ := exists_bound φ; ⟨a, Bound.mono (φ := φ) (Nat.le_succ a) ha⟩
end Fml

open Fml

def Env.cons (x : PSet.{u}) (e : Nat → PSet.{u}) : Nat → PSet.{u}
  | 0 => x
  | n+1 => e n

/-- Satisfaction in the class model `M`. -/
def Sat (M : PSet.{u} → Prop) : Fml → (Nat → PSet.{u}) → Prop
  | .mem i j, e => e i ∈ e j
  | .eq i j, e => e i ≈ e j
  | .fls, _ => False
  | .imp φ ψ, e => Sat M φ e → Sat M ψ e
  | .all φ, e => ∀ x, M x → Sat M φ (Env.cons x e)

theorem Env.cons_resp {x x' : PSet.{u}} {e e' : Nat → PSet.{u}} (hx : x ≈ x')
    (he : ∀ i, e i ≈ e' i) : ∀ i, Env.cons x e i ≈ Env.cons x' e' i
  | 0 => hx
  | n+1 => he n

theorem Sat.resp_iff {M M' : PSet.{u} → Prop} (hM : ∀ x, M x ↔ M' x) :
    ∀ (φ : Fml) {e e' : Nat → PSet.{u}}, (∀ i, e i ≈ e' i) → (Sat M φ e ↔ Sat M' φ e')
  | .mem i j, _, _, h =>
    (mem_congr_left (h i)).trans (mem_congr_right (h j))
  | .eq i j, _, _, h =>
    ⟨fun s => (h i).symm.trans (s.trans (h j)), fun s => (h i).trans (s.trans (h j).symm)⟩
  | .fls, _, _, _ => Iff.rfl
  | .imp φ ψ, _, _, h =>
    have h1 := Sat.resp_iff hM φ h; have h2 := Sat.resp_iff hM ψ h
    ⟨fun s a => h2.1 (s (h1.2 a)), fun s a => h2.2 (s (h1.1 a))⟩
  | .all φ, _, _, h =>
    ⟨fun s x hx => (Sat.resp_iff hM φ (Env.cons_resp (Equiv.refl x) h)).1 (s x ((hM x).2 hx)),
     fun s x hx => (Sat.resp_iff hM φ (Env.cons_resp (Equiv.refl x) h)).2 (s x ((hM x).1 hx))⟩

theorem Sat.resp {M : PSet.{u} → Prop} (φ : Fml) {e e' : Nat → PSet.{u}}
    (h : ∀ i, e i ≈ e' i) (s : Sat M φ e) : Sat M φ e' :=
  (Sat.resp_iff (fun _ => Iff.rfl) φ h).1 s

theorem sat_rename {M : PSet.{u} → Prop} :
    ∀ (φ : Fml) (ρ : Nat → Nat) (e : Nat → PSet.{u}),
      Sat M (rename ρ φ) e ↔ Sat M φ (fun i => e (ρ i))
  | .mem _ _, _, _ | .eq _ _, _, _ | .fls, _, _ => Iff.rfl
  | .imp φ ψ, ρ, e =>
    have h1 := sat_rename φ ρ e; have h2 := sat_rename ψ ρ e
    ⟨fun s a => h2.1 (s (h1.2 a)), fun s a => h2.2 (s (h1.1 a))⟩
  | .all φ, ρ, e =>
    have H : ∀ x, Sat M (rename (up ρ) φ) (Env.cons x e) ↔
        Sat M φ (Env.cons x fun i => e (ρ i)) := fun x =>
      (sat_rename φ (up ρ) (Env.cons x e)).trans <| Sat.resp_iff (fun _ => Iff.rfl) φ
        fun i => by cases i <;> exact Equiv.refl _
    ⟨fun s x hx => (H x).1 (s x hx), fun s x hx => (H x).2 (s x hx)⟩

/-- Satisfaction depends only on the free variables. -/
theorem sat_bound {M : PSet.{u} → Prop} :
    ∀ {φ : Fml} {k : Nat} {e e' : Nat → PSet.{u}}, Bound k φ → (∀ i, i < k → e i ≈ e' i) →
      (Sat M φ e ↔ Sat M φ e')
  | .mem i j, _, _, _, ⟨hi, hj⟩, h => (mem_congr_left (h i hi)).trans (mem_congr_right (h j hj))
  | .eq i j, _, _, _, ⟨hi, hj⟩, h =>
    ⟨fun s => (h i hi).symm.trans (s.trans (h j hj)),
     fun s => (h i hi).trans (s.trans (h j hj).symm)⟩
  | .fls, _, _, _, _, _ => Iff.rfl
  | .imp φ ψ, _, _, _, ⟨b1, b2⟩, h =>
    have h1 := sat_bound b1 h; have h2 := sat_bound b2 h
    ⟨fun s a => h2.1 (s (h1.2 a)), fun s a => h2.2 (s (h1.1 a))⟩
  | .all φ, _, _, _, b, h =>
    have H : ∀ x, Sat M φ (Env.cons x _) ↔ Sat M φ (Env.cons x _) := fun x =>
      sat_bound b fun i hi => by
        cases i with
        | zero => exact Equiv.refl _
        | succ i => exact h i (Nat.lt_of_succ_lt_succ hi)
    ⟨fun s x hx => (H x).1 (s x hx), fun s x hx => (H x).2 (s x hx)⟩

/-! ### Stability and the derived connectives

Satisfaction is stable, because the atoms are and formulas are built from `⊥`, `→`, `∀`. So
the classical reading of the derived connectives needs no excluded middle. -/

theorem Sat.stable {M : PSet.{u} → Prop} : ∀ (φ : Fml) (e : Nat → PSet.{u}), Stable (Sat M φ e)
  | .mem _ _, _ => inferInstanceAs (Stable (_ ∈ _))
  | .eq _ _, _ => inferInstanceAs (Stable (_ ≈ _))
  | .fls, _ => inferInstanceAs (Stable False)
  | .imp _ ψ, e => have := Sat.stable (M := M) ψ e; inferInstanceAs (Stable (_ → _))
  | .all φ, e => have := fun x => Sat.stable (M := M) φ (Env.cons x e)
    inferInstanceAs (Stable (∀ _, _ → _))

instance {M : PSet.{u} → Prop} {φ e} : Stable (Sat M φ e) := Sat.stable φ e

theorem sat_neg {M : PSet.{u} → Prop} {φ : Fml} {e} : Sat M (neg φ) e ↔ ¬ Sat M φ e := Iff.rfl

theorem sat_and {M : PSet.{u} → Prop} {φ ψ : Fml} {e} :
    Sat M (and φ ψ) e ↔ Sat M φ e ∧ Sat M ψ e :=
  ⟨fun h => ⟨Stable.dne fun h1 => h fun a => (h1 a).elim, Stable.dne fun h2 => h fun _ b => h2 b⟩,
   fun ⟨a, b⟩ h => h a b⟩

theorem sat_or {M : PSet.{u} → Prop} {φ ψ : Fml} {e} :
    Sat M (or φ ψ) e ↔ ¬¬(Sat M φ e ∨ Sat M ψ e) :=
  ⟨fun h hn => hn (.inr (h fun a => hn (.inl a))),
   fun h n => Stable.of_nn h fun
    | .inl a => (n a).elim
    | .inr b => b⟩

theorem sat_iff {M : PSet.{u} → Prop} {φ ψ : Fml} {e} :
    Sat M (iff φ ψ) e ↔ (Sat M φ e ↔ Sat M ψ e) :=
  sat_and.trans ⟨fun ⟨a, b⟩ => ⟨a, b⟩, fun ⟨a, b⟩ => ⟨a, b⟩⟩

theorem sat_ex {M : PSet.{u} → Prop} {φ : Fml} {e} :
    Sat M (ex φ) e ↔ ¬¬∃ x, M x ∧ Sat M φ (Env.cons x e) :=
  ⟨fun h hn => h fun x hx s => hn ⟨x, hx, s⟩, fun h k => h fun ⟨x, hx, s⟩ => k x hx s⟩

/-! ### Codes -/

/-- Codes: a tag followed by the components. -/
def enc : Fml → PSet.{u}
  | .mem i j => pair (ofNat 0) (pair (ofNat i) (ofNat j))
  | .eq i j => pair (ofNat 1) (pair (ofNat i) (ofNat j))
  | .fls => pair (ofNat 2) empty
  | .imp φ ψ => pair (ofNat 3) (pair (enc φ) (enc ψ))
  | .all φ => pair (ofNat 4) (enc φ)

theorem enc_inj : ∀ {φ ψ : Fml}, enc.{u} φ ≈ enc ψ → φ = ψ := by
  intro φ
  induction φ with
  | mem i j | eq i j => intro ψ h; cases ψ <;> first
    | exact absurd (ofNat_inj (pair_inj h).1) (by decide)
    | (have ⟨a, b⟩ := pair_inj (pair_inj h).2; cases ofNat_inj a; cases ofNat_inj b; rfl)
  | fls => intro ψ h; cases ψ <;> first
    | exact absurd (ofNat_inj (pair_inj h).1) (by decide)
    | rfl
  | imp φ₁ φ₂ ih₁ ih₂ => intro ψ h; cases ψ <;> first
    | exact absurd (ofNat_inj (pair_inj h).1) (by decide)
    | (have ⟨a, b⟩ := pair_inj (pair_inj h).2; cases ih₁ a; cases ih₂ b; rfl)
  | all φ ih => intro ψ h; cases ψ <;> first
    | exact absurd (ofNat_inj (pair_inj h).1) (by decide)
    | (cases ih (pair_inj h).2; rfl)
