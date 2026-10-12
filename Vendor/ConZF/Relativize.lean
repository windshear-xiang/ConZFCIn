import Vendor.ConZF.Proof
/-!
Uniform relativization (conzf15 §2, ported from the supplied draft). For a unary formula `d`
(free variable `0` only), `restrictClass d φ` restricts every quantifier of `φ` to `d`, and
`definedClass M d` is the class of members of `M` satisfying `d`. Satisfaction of the
relativized formula in `M` is satisfaction of the original in the defined class
(`sat_restrictClass`), uniformly over native formulas and environments, so validity transfers
(`valid_definedClass`). No truth predicate for a proper class is encoded: the recursion is on
native finite syntax.
-/
universe u

namespace PSet

namespace Fml
/-- Restrict each quantifier to a unary formula, whose sole free variable is `0`. -/
def restrictClass (d : Fml) : Fml → Fml
  | .mem i j => .mem i j
  | .eq i j => .eq i j
  | .fls => .fls
  | .imp p q => .imp (restrictClass d p) (restrictClass d q)
  | .all p => .all (.imp d (restrictClass d p))
end Fml

/-- A class defined over `M` by a unary formula. -/
def definedClass (M : PSet.{u} → Prop) (d : Fml) (x : PSet.{u}) : Prop :=
  M x ∧ Sat M d (Env.cons x (fun _ => empty))

/-- A unary formula does not see the tail of the environment. -/
theorem sat_unary {M : PSet.{u} → Prop} {d : Fml} (hd : Fml.Bound 1 d) (x : PSet.{u})
    (e : Nat → PSet.{u}) : Sat M d (Env.cons x e) ↔ Sat M d (Env.cons x (fun _ => empty)) :=
  sat_bound hd fun i hi => by
    cases i with
    | zero => exact Equiv.refl _
    | succ i => exact (Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ hi)).elim

/-- **The uniform bridge**: satisfaction of the relativized formula in `M` is satisfaction of
the formula in the defined class. -/
theorem sat_restrictClass {M : PSet.{u} → Prop} (d : Fml) (hd : Fml.Bound 1 d) :
    ∀ (p : Fml) (e : Nat → PSet.{u}),
      Sat M (Fml.restrictClass d p) e ↔ Sat (definedClass M d) p e
  | .mem _ _, _ | .eq _ _, _ | .fls, _ => Iff.rfl
  | .imp p q, e =>
    have hp := sat_restrictClass (M := M) d hd p e
    have hq := sat_restrictClass (M := M) d hd q e
    ⟨fun h a => hq.1 (h (hp.2 a)), fun h a => hq.2 (h (hp.1 a))⟩
  | .all p, e =>
    ⟨fun h x hx => (sat_restrictClass (M := M) d hd p (Env.cons x e)).1
        (h x hx.1 ((sat_unary hd x e).2 hx.2)),
     fun h x hx hd' => (sat_restrictClass (M := M) d hd p (Env.cons x e)).2
        (h x ⟨hx, (sat_unary hd x e).1 hd'⟩)⟩

/-- Validity of a relativized formula in `M` gives validity in the defined class. -/
theorem valid_definedClass {M : PSet.{u} → Prop} (d : Fml) (hd : Fml.Bound 1 d)
    {p : Fml} (h : Valid M (Fml.restrictClass d p)) : Valid (definedClass M d) p :=
  fun e he => (sat_restrictClass d hd p e).1 (h e (fun i => (he i).1))

/-- info: 'PSet.sat_restrictClass' does not depend on any axioms -/
#guard_msgs in #print axioms sat_restrictClass
/-- info: 'PSet.valid_definedClass' does not depend on any axioms -/
#guard_msgs in #print axioms valid_definedClass

end PSet
