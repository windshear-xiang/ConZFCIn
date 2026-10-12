import Vendor.ConZF.ChoiceN

/-!
The seeded model and its constructible inner class in one upper universe.
Choose the seed `b` once; all lower-universe interval arguments then use the same `L b`.

This parameterizes the constructions in the pinned upstream `UpperN.lean` and
`ChoiceN.lean`, replacing the fixed seed `K` with an arbitrary seed `b`.
-/

universe u

namespace PSet.Multi

/-- The hereditarily-good class for the budget containing the supplied set seed. -/
def M (b : PSet.{u}) : PSet.{u} → Prop := HG (B := seeded b)

/-- The constructible inner class shared by all interval arguments. -/
def L (b : PSet.{u}) : PSet.{u} → Prop := Constr (M b)

theorem synZF_M (b : PSet.{u}) (em : ∀ p : Prop, p ∨ ¬p) : SynZF (M b) :=
  SynZF.of_zfModel (hg_model (B := seeded b)
    (accHyp_of_not_not_em fun k => k em))
    (fun x => inferInstanceAs (Stable (HG (B := seeded b) x)))
    (fun e h => HG.resp (B := seeded b) e h)

theorem synZF_L (b : PSet.{u}) (em : ∀ p : Prop, p ∨ ¬p) : SynZF (L b) :=
  (synZF_M b em).synZF_constr

theorem M_seed (b : PSet.{u}) : M b b := hg_seed b

theorem L_seed {b : PSet.{u}} (em : ∀ p : Prop, p ∨ ¬p) (hb : IsOrd b) : L b b :=
  (synZF_M b em).constr_of_ord hb (M_seed b)

theorem L_mem_seed {b x : PSet.{u}} (em : ∀ p : Prop, p ∨ ¬p)
    (hb : IsOrd b) (hx : x ∈ b) : L b x :=
  (synZF_L b em).trans (L_seed em hb) hx

theorem L_le_seed {b x : PSet.{u}} (em : ∀ p : Prop, p ∨ ¬p)
    (hb : IsOrd b) (hx : x ∈ succ b) : L b x := by
  have := (synZF_L b em).stable x
  exact Stable.of_nn (mem_succ.1 hx) fun
    | .inl h => L_mem_seed em hb h
    | .inr e => (synZF_L b em).resp e.symm (L_seed em hb)

theorem L_self (b : PSet.{u}) (em : ∀ p : Prop, p ∨ ¬p) :
    ∀ x, L b x → Constr (L b) x :=
  fun x hx => ((synZF_M b em).constr_constr (synZF_L b em) x).2 hx

theorem valid_ac_L (b : PSet.{u}) (em : ∀ p : Prop, p ∨ ¬p) : Valid (L b) ac :=
  (synZF_L b em).valid_ac (L_self b em)

/- These queries display the axiom dependencies of this module's declarations.
The interval results and final consistency theorems are checked at their own entry points. -/
#print axioms synZF_M
#print axioms synZF_L
#print axioms valid_ac_L

end PSet.Multi
