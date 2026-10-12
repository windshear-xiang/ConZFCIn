import Vendor.ConZF.Rule
/-!
Replacement from pointwise accessibility. Instead of a proof that the root of the glued tree is
not not accessible (`replacement`), guard the value of the recursion at each component
`[.c x]` separately by its own accessibility proof (`componentBound`, an unconditional term).
Pointwise double-negated accessibility of the components, or of the output values under
membership, then suffices, and the image exists positively (`replacement_pointwise`,
`replacement_of_pointwise_mem_acc`). No simultaneous accessibility certificate is formed: the
quantifier over components stays outside the double negations.
-/

universe u
namespace PSet

/-- A proof-indexed partial evaluation, available without an accessibility assumption. -/
def guardedValue (D : PSet.{u} → PSet.{u}) (U : PSet.{u})
    (τ : Path.{u} → PSet.{u} → Prop) (p : Path.{u}) : PSet.{u} :=
  guard (Acc (Rel τ) p) fun h => F D U (Rel τ) p h

/-- Pointwise double-negated accessibility suffices to identify the guarded value. -/
theorem guardedValue_equiv {D : PSet.{u} → PSet.{u}} {U : PSet.{u}}
    {τ : Path.{u} → PSet.{u} → Prop} (hτ : Coherent D U τ)
    {p : Path.{u}} {t : PSet.{u}} (ht : τ p t)
    (ha : ¬¬Acc (Rel τ) p) : guardedValue D U τ p ≈ t := by
  refine Stable.of_nn ha fun acc => ?_
  refine ext fun x => ?_
  change x ∈ guard (Acc (Rel τ) p) (fun h => F D U (Rel τ) p h) ↔ x ∈ t
  constructor
  · intro hx
    exact Stable.of_nn (mem_guard.1 hx) fun ⟨acc', hx'⟩ =>
      (mem_congr_right (materialize hτ t p ht acc')).1 hx'
  · intro hx
    exact mem_guard.2 (nn_intro ⟨acc,
      (mem_congr_right (materialize hτ t p ht acc)).2 hx⟩)

/-- A bound made from separately guarded evaluations at the literal domain indices. -/
def componentBound (D : PSet.{u} → PSet.{u}) (s : PSet.{u})
    (τ : Path.{u} → PSet.{u} → Prop) : PSet.{u} :=
  iUnion fun i : s.Idx =>
    guard (Acc (Rel τ) [.c (s.Func i)]) fun acc =>
      succ (F D s (Rel τ) [.c (s.Func i)] acc)

theorem mem_componentBound {D : PSet.{u} → PSet.{u}} {s : PSet.{u}}
    {τ : Path.{u} → PSet.{u} → Prop} (hτ : Coherent D s τ)
    {i : s.Idx} {t : PSet.{u}} (ht : τ [.c (s.Func i)] t)
    (ha : ¬¬Acc (Rel τ) [.c (s.Func i)]) : t ∈ componentBound D s τ := by
  refine Stable.of_nn ha fun acc => ?_
  exact mem_iUnion.2 (nn_intro ⟨i, mem_guard.2 (nn_intro ⟨acc,
    mem_succ_of_equiv (materialize hτ t [.c (s.Func i)] ht acc).symm⟩)⟩)

/-- Separation recovers an exact image from any ambient bound. -/
theorem replacement_from_bound {s B : PSet.{u}}
    {φ : PSet.{u} → PSet.{u} → Prop}
    (hresp : ∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (hbound : ∀ {x y}, x ∈ s → φ x y → y ∈ B) :
    ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ¬¬∃ x, x ∈ s ∧ φ x y := by
  refine ⟨sep (fun y => ¬¬∃ x, x ∈ s ∧ φ x y) B, fun y => ?_⟩
  refine (mem_sep (fun y y' e => nn_map fun ⟨x, hx, h⟩ =>
    ⟨x, hx, hresp (Equiv.refl _) e h⟩)).trans ?_
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Stable.of_nn h (fun ⟨x, hx, hφ⟩ => hbound hx hφ), h⟩

/-- No accessibility assumption on the glued root; no outer double negation on the image. -/
theorem replacement_pointwise {D : PSet.{u} → PSet.{u}}
    {T : PSet.{u} → Path.{u} → PSet.{u} → Prop} {s : PSet.{u}}
    {φ : PSet.{u} → PSet.{u} → Prop} {C : PSet.{u} → Prop}
    (hT : ∀ η, C η → Coherent D s (T η) ∧ T η [] η)
    (hTresp : ∀ {η η' p t}, η ≈ η' → T η p t → T η' p t)
    (hresp : ∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (hfunc : ∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (hC : ∀ {x y}, x ∈ s → φ x y → C y)
    (hacc : ∀ x η, x ∈ s → φ x η →
      ¬¬Acc (Rel (Glue T s φ)) [.c x]) :
    ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ¬¬∃ x, x ∈ s ∧ φ x y := by
  have hτ := glue_coherent (D := D) hT hTresp hresp hfunc hC
  apply replacement_from_bound (B := componentBound D s (Glue T s φ)) hresp
  intro x y hx hφ
  refine hx.elim fun i ex => ?_
  have hi : φ (s.Func i) y := hresp ex (Equiv.refl _) hφ
  have ht : Glue T s φ [.c (s.Func i)] y :=
    ⟨[], s.Func i, y, rfl, func_mem s i, hi, (hT y (hC (func_mem s i) hi)).2⟩
  exact mem_componentBound hτ ht (hacc (s.Func i) y (func_mem s i) hi)

/-- A sufficient, simpler condition: each output is individually not not accessible. -/
theorem replacement_of_pointwise_mem_acc {D : PSet.{u} → PSet.{u}}
    {T : PSet.{u} → Path.{u} → PSet.{u} → Prop} {s : PSet.{u}}
    {φ : PSet.{u} → PSet.{u} → Prop} {C : PSet.{u} → Prop}
    (hT : ∀ η, C η → Coherent D s (T η) ∧ T η [] η)
    (hTresp : ∀ {η η' p t}, η ≈ η' → T η p t → T η' p t)
    (hresp : ∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (hfunc : ∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (hC : ∀ {x y}, x ∈ s → φ x y → C y)
    (hacc : ∀ η, C η → ¬¬Acc (· ∈ ·) η) :
    ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ¬¬∃ x, x ∈ s ∧ φ x y := by
  have hτ := glue_coherent (D := D) hT hTresp hresp hfunc hC
  apply replacement_pointwise hT hTresp hresp hfunc hC
  intro x η hx hφ
  have ht : Glue T s φ [.c x] η :=
    ⟨[], x, η, rfl, hx, hφ, (hT η (hC hx hφ)).2⟩
  exact nn_map (fun ha => acc_of_desc hτ.desc ha [.c x] ht) (hacc η (hC hx hφ))

namespace Rule
variable {D : PSet.{u} → PSet.{u}} {U : PSet.{u}}
    {r : PSet.{u} → Label.{u} → PSet.{u} → Prop} {C : PSet.{u} → Prop}

/-- Rule-level wrapper, with the same arguments as the original Replacement interface
except for its last hypothesis, and with a positive existential conclusion. -/
theorem replacement_pointwise (hr : Rule D U r C)
    (s : PSet.{u}) (hU : U = s) (φ : PSet.{u} → PSet.{u} → Prop)
    (hresp : ∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
    (hfunc : ∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y')
    (hC : ∀ {x y}, x ∈ s → φ x y → C y)
    (hacc : ∀ η, C η → ¬¬Acc (· ∈ ·) η) :
    ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ¬¬∃ x, x ∈ s ∧ φ x y := by
  subst hU
  have hT η hη := hr.coherent (η := η) hη
  have hTr : ∀ {η η' p t}, η ≈ η' → Tr r η p t → Tr r η' p t :=
    fun e h => tr_resp_root e h
  exact PSet.replacement_of_pointwise_mem_acc (D := D)
    hT hTr hresp hfunc hC hacc

end Rule

/-- info: 'PSet.Rule.replacement_pointwise' does not depend on any axioms -/
#guard_msgs in #print axioms Rule.replacement_pointwise
end PSet
