import ConZFCIn.Model.SeededClass
import ConZFCIn.Logic.FiniteInaccessibles

/-! First-order consistency from a finite inaccessible chain in one concrete
constructible class. The seed `b` may be any set; existence and nonemptiness of the
model require no ordinal assumption on it. The final finite proofs supply `hc` using
the interval theorem and the strictly increasing universe heights. -/

universe u

namespace ConZFCIn
open PSet PSet.Multi

theorem con_ZFCIn_seeded (b : PSet.{u}) (em : ∀ p : Prop, p ∨ ¬p)
    {n : Nat} (hc : InaccChain (L b) n) : Con (ZFCIn n) :=
  let hL := synZF_L b em
  con_ZFCIn_of_model hL.toTransClass hL.valid (valid_ac_L b em) hc ⟨empty, hL.empty⟩

#print axioms con_ZFCIn_seeded

end ConZFCIn
