/-!
Stable propositions. A proposition is *stable* if it follows from its double negation. Stable
propositions are closed under `∀`, `→`, `∧`, `¬`, and to prove one we may reason classically:
case distinctions (`Stable.by_cases`) and the opening of a doubly negated hypothesis
(`Stable.of_nn`) are available without excluded middle.
-/

class Stable (p : Prop) : Prop where
  dne : ¬¬p → p

namespace Stable

instance : Stable False := ⟨fun h => h id⟩
instance : Stable True := ⟨fun _ => trivial⟩
instance {p q : Prop} [Stable q] : Stable (p → q) := ⟨fun h hp => dne fun hq => h fun f => hq (f hp)⟩
instance {α : Sort _} {P : α → Prop} [∀ x, Stable (P x)] : Stable (∀ x, P x) :=
  ⟨fun h x => dne fun hx => h fun f => hx (f x)⟩
instance {p q : Prop} [Stable p] [Stable q] : Stable (p ∧ q) :=
  ⟨fun h => ⟨dne fun hp => h fun f => hp f.1, dne fun hq => h fun f => hq f.2⟩⟩
instance {p q : Prop} [Stable p] [Stable q] : Stable (p ↔ q) :=
  ⟨fun h => ⟨fun hp => dne fun hq => h fun f => hq (f.1 hp),
    fun hq => dne fun hp => h fun f => hp (f.2 hq)⟩⟩
instance {p : Prop} : Stable (¬p) := inferInstanceAs (Stable (p → False))

/-- To prove a stable goal, a doubly negated hypothesis may be used as if it held. -/
theorem of_nn {g : Prop} [Stable g] {p : Prop} (h : ¬¬p) (f : p → g) : g :=
  dne fun hg => h fun hp => hg (f hp)

/-- To prove a stable goal, any case distinction is available. -/
theorem by_cases {g : Prop} [Stable g] (p : Prop) (f : p → g) (f' : ¬p → g) : g :=
  dne fun hg => hg (f' fun hp => hg (f hp))

end Stable

/-- The weak existential and disjunction of the negative translation. -/
def NEx {α : Sort _} (P : α → Prop) : Prop := ¬¬∃ x, P x
def NOr (p q : Prop) : Prop := ¬¬(p ∨ q)

theorem nn_intro {p : Prop} (h : p) : ¬¬p := fun hn => hn h
theorem nn_map {p q : Prop} (f : p → q) (h : ¬¬p) : ¬¬q := fun hn => h fun hp => hn (f hp)
theorem nn_bind {p q : Prop} (h : ¬¬p) (f : p → ¬¬q) : ¬¬q := fun hn => h fun hp => f hp hn
theorem nn_congr {p q : Prop} (h : p ↔ q) : ¬¬p ↔ ¬¬q := ⟨nn_map h.1, nn_map h.2⟩
theorem nn_nn {p : Prop} : ¬¬¬¬p ↔ ¬¬p := ⟨fun h hn => h fun h' => h' hn, nn_intro⟩
