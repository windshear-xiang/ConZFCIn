import Vendor.ConZF.Mat
/-
Replacement for functional relations with values in a class that has uniformly defined
coherent assignments. No totality, no choice: the image is obtained from the value of the
materializing recursion at the root of a tree glued from the assignments of the values.
-/
universe u

namespace PSet

variable {D : PSet.{u} → PSet.{u}}

section glue
variable (T : PSet.{u} → Path.{u} → PSet.{u} → Prop) (s : PSet.{u})
  (φ : PSet.{u} → PSet.{u} → Prop)

/-- The glued assignment: below the child `c x` of the root, the assignment of the value of
`φ` at `x`. The root itself has no target; its value is what we want to construct. -/
def Glue (q : Path.{u}) (t : PSet.{u}) : Prop :=
  ∃ r x η, q = r ++ [.c x] ∧ x ∈ s ∧ φ x η ∧ T η r t

theorem append_inj' (h : s₁ ++ [a] = s₂ ++ [a']) : s₁ = s₂ ∧ a = a' := by
  induction s₁ generalizing s₂ with
  | nil =>
    match s₂ with
    | [] => cases h; exact ⟨rfl, rfl⟩
    | [_] | _::_::_ => cases h
  | cons c s₁ ih =>
    cases s₂ with | nil => cases s₁ <;> cases h | cons d s₂
    injection h with h1 h2; cases h1
    obtain ⟨rfl, rfl⟩ := ih h2; exact ⟨rfl, rfl⟩

variable {T s φ} {C : PSet.{u} → Prop}
  (hT : ∀ η, C η → Coherent D s (T η) ∧ T η [] η)
  (hTresp : ∀ {η η' p t}, η ≈ η' → T η p t → T η' p t)
  (φ_resp : ∀ {x x' y y'}, x ≈ x' → y ≈ y' → φ x y → φ x' y')
  (φ_func : ∀ {x y y'}, x ∈ s → φ x y → φ x y' → y ≈ y')
  (φ_C : ∀ {x y}, x ∈ s → φ x y → C y)
include hTresp φ_func

theorem glue_iff {r x η t} (hx : x ∈ s) (hη : φ x η) : Glue T s φ (r ++ [.c x]) t ↔ T η r t := by
  constructor
  · rintro ⟨r', x', η', e, hx', hη', h⟩
    have ⟨e1, e2⟩ := append_inj' e
    cases e1; cases e2
    exact hTresp (φ_func hx hη' hη) h
  · exact fun h => ⟨r, x, η, rfl, hx, hη, h⟩

include hT φ_resp φ_C

theorem glue_coherent : Coherent D s (Glue T s φ) where
  resp := by
    rintro _ t t' ⟨r, x, η, rfl, hx, hη, h⟩ e
    exact ⟨r, x, η, rfl, hx, hη, (hT η (φ_C hx hη)).1.resp h e⟩
  func := by
    rintro _ t t' ⟨r, x, η, rfl, hx, hη, h⟩ h'
    exact (hT η (φ_C hx hη)).1.func h ((glue_iff (T := T) (φ := φ) hTresp φ_func hx hη).1 h')
  lab := by
    rintro l l' p t e ⟨r, x, η, eq, hx, hη, h⟩
    cases r with
    | nil =>
      cases eq
      cases e with | c e =>
      exact ⟨[], _, η, rfl, (mem_congr_left e).1 hx, φ_resp e (Equiv.refl _) hη, h⟩
    | cons l0 r =>
      cases eq
      exact ⟨l' :: r, x, η, rfl, hx, hη, (hT η (φ_C hx hη)).1.lab e h⟩
  desc := by
    rintro l _ t t' h ⟨r, x, η, rfl, hx, hη, h'⟩
    exact (hT η (φ_C hx hη)).1.desc
      ((glue_iff (T := T) (φ := φ) (r := l :: r) hTresp φ_func hx hη).1 h) h'
  sup := by
    rintro _ t G ⟨r, x, η, rfl, hx, hη, h⟩ hG y
    have hG' : IsG (T η) r G := fun z => (hG z).trans <| nn_congr <| exists_congr fun ζ =>
      and_congr (glue_iff (T := T) (φ := φ) (r := .a :: r) hTresp φ_func hx hη) Iff.rfl
    refine (hT η (φ_C hx hη)).1.sup h hG' y |>.trans ?_
    exact nn_congr <| exists_congr fun l => exists_congr fun t' => and_congr Iff.rfl <|
      and_congr (glue_iff (T := T) (φ := φ) (r := l :: r) hTresp φ_func hx hη).symm Iff.rfl

/-- If the root is accessible, the value of the recursion there is the union of the successors
of the values of `φ` on `s`. -/
theorem mem_F_root (acc : Acc (Rel (Glue T s φ)) []) (y : PSet.{u}) :
    y ∈ F D s (Rel (Glue T s φ)) [] acc ↔ ¬¬∃ x η, x ∈ s ∧ φ x η ∧ y ∈ succ η := by
  have coh := glue_coherent hT hTresp φ_resp φ_func φ_C
  refine F_eq .. ▸ ?_
  refine mem_step_iff coh (fun c h tc htc => materialize coh tc c htc _) _ |>.trans
    ⟨nn_map ?_, nn_map ?_⟩
  · rintro ⟨l, t', -, ⟨r, x, η, eq, hx, hη, h⟩, hy⟩
    cases r with
    | nil =>
      have e := (hT η (φ_C hx hη)).1.func h (hT η (φ_C hx hη)).2
      exact ⟨x, η, hx, hη, (mem_congr_right (succ_congr e)).1 hy⟩
    | cons _ r => cases r <;> cases eq
  · rintro ⟨x, η, hx, hη, hy⟩
    exact ⟨.c x, η, .inr (.inr ⟨x, hx, .c (Equiv.refl _)⟩),
      ⟨[], x, η, rfl, hx, hη, (hT η (φ_C hx hη)).2⟩, hy⟩

/-- **Replacement** for `φ` on `s`, provided the values of `φ` lie in a class `C` every member
`η` of which is the root target of a coherent assignment `T η` given uniformly in `η`, and
provided the root of the glued tree is not not accessible. -/
theorem replacement (acc : Acc (Rel (Glue T s φ)) []) :
    ∃ img : PSet.{u}, ∀ y, y ∈ img ↔ ¬¬∃ x, x ∈ s ∧ φ x y := by
  have hθ := mem_F_root (D := D) hT hTresp φ_resp φ_func φ_C acc
  refine ⟨sep (fun y => ¬¬∃ x, x ∈ s ∧ φ x y) (F D s (Rel (Glue T s φ)) [] acc), fun y => ?_⟩
  refine (mem_sep fun y y' e => nn_map fun ⟨x, hx, h⟩ =>
    ⟨x, hx, φ_resp (Equiv.refl _) e h⟩).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  exact (hθ y).2 (nn_map (fun ⟨x, hx, h⟩ => ⟨x, y, hx, h, self_mem_succ y⟩) h)

end glue

/-- info: 'PSet.replacement' does not depend on any axioms -/
#guard_msgs in #print axioms replacement
