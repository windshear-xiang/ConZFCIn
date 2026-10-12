import Vendor.ConZF.Fml
/-!
A Hilbert-style proof system for first-order logic with `∈` and `=` (Mendelson's system with
de Bruijn variables): the axioms `K`, `S`, double negation elimination, instantiation of a
universal quantifier by a variable, distribution of `∀` over an implication whose antecedent
does not mention the bound variable, reflexivity of `=` and substitutivity of `=` in atomic
formulas; the rules modus ponens and generalization. The nonlogical axioms of a theory are
open formulas, their free variables standing for arbitrary parameters.

Soundness is proved for class models: if every axiom holds in `M` under every environment of
elements of `M`, so does every theorem. A theory with a nonempty model is consistent. Double
negation elimination is sound without excluded middle, because satisfaction is stable.
-/
universe u

namespace PSet
open Fml

inductive Prf (T : Fml → Prop) : Fml → Prop
  | ax {φ} : T φ → Prf T φ
  | k {φ ψ} : Prf T (imp φ (imp ψ φ))
  | s {φ ψ χ} : Prf T (imp (imp φ (imp ψ χ)) (imp (imp φ ψ) (imp φ χ)))
  | dne {φ} : Prf T (imp (neg (neg φ)) φ)
  | mp {φ ψ} : Prf T (imp φ ψ) → Prf T φ → Prf T ψ
  | gen {φ} : Prf T φ → Prf T (all φ)
  | inst {φ} (j : Nat) : Prf T (imp (all φ) (rename (inst j) φ))
  | dist {φ ψ} : Prf T (imp (all (imp (lift φ) ψ)) (imp φ (all ψ)))
  | refl (i : Nat) : Prf T (eq i i)
  | eq_mem_l (i j k : Nat) : Prf T (imp (eq i j) (imp (mem i k) (mem j k)))
  | eq_mem_r (i j k : Nat) : Prf T (imp (eq i j) (imp (mem k i) (mem k j)))
  | eq_eq (i j k : Nat) : Prf T (imp (eq i j) (imp (eq i k) (eq j k)))

/-- `T` is consistent: it does not prove `⊥`. -/
def Con (T : Fml → Prop) : Prop := ¬ Prf T fls

/-- `φ` holds in `M` under every environment of elements of `M`. -/
def Valid (M : PSet.{u} → Prop) (φ : Fml) : Prop :=
  ∀ e : Nat → PSet.{u}, (∀ i, M (e i)) → Sat M φ e

theorem Env.cons_mem {M : PSet.{u} → Prop} {x : PSet.{u}} {e : Nat → PSet.{u}} (hx : M x)
    (he : ∀ i, M (e i)) : ∀ i, M (Env.cons x e i)
  | 0 => hx
  | n+1 => he n

theorem soundness {T : Fml → Prop} {M : PSet.{u} → Prop}
    (hT : ∀ φ, T φ → Valid M φ) {φ : Fml} (h : Prf T φ) : Valid M φ := by
  induction h with
  | ax h => exact hT _ h
  | k => exact fun _ _ a _ => a
  | s => exact fun _ _ f g a => f a (g a)
  | dne => exact fun _ _ h => Stable.dne h
  | mp _ _ ih1 ih2 => exact fun e he => ih1 e he (ih2 e he)
  | gen _ ih => exact fun e he x hx => ih _ (Env.cons_mem hx he)
  | @inst φ j =>
    intro e he h
    refine (sat_rename φ (Fml.inst j) e).2 (Sat.resp φ (fun i => ?_) (h (e j) (he j)))
    cases i <;> exact Equiv.refl _
  | @dist φ ψ =>
    intro e _ h a x hx
    refine h x hx ((sat_rename φ Nat.succ (Env.cons x e)).2 ?_)
    exact Sat.resp φ (fun _ => Equiv.refl _) a
  | refl i => exact fun e _ => Equiv.refl (e i)
  | eq_mem_l => exact fun _ _ h1 h2 => (mem_congr_left h1).1 h2
  | eq_mem_r => exact fun _ _ h1 h2 => (mem_congr_right h1).1 h2
  | eq_eq => exact fun _ _ h1 h2 => h1.symm.trans h2

/-- A theory with a nonempty class model is consistent. -/
theorem Con.of_model {T : Fml → Prop} {M : PSet.{u} → Prop}
    (hT : ∀ φ, T φ → Valid M φ) (x : PSet.{u}) (hx : M x) : Con T :=
  fun h => soundness hT h (fun _ => x) (fun _ => hx)
