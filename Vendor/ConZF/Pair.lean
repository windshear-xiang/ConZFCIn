import Vendor.ConZF.PSet
/-! Kuratowski pairs and tuples, used to put a definition with its parameters into a label. -/
universe u

namespace PSet

def upair (a b : PSet.{u}) : PSet.{u} := union (singleton a) (singleton b)

theorem mem_upair {a b x : PSet.{u}} : x ∈ upair a b ↔ ¬¬(x ≈ a ∨ x ≈ b) :=
  mem_union.trans (nn_congr (or_congr mem_singleton mem_singleton))

theorem mem_upair_left (a b : PSet.{u}) : a ∈ upair a b := mem_upair.2 (nn_intro (.inl (.refl _)))
theorem mem_upair_right (a b : PSet.{u}) : b ∈ upair a b := mem_upair.2 (nn_intro (.inr (.refl _)))

theorem upair_congr {a a' b b' : PSet.{u}} (ha : a ≈ a') (hb : b ≈ b') : upair a b ≈ upair a' b' :=
  ext fun _ => mem_upair.trans <| .trans
    (nn_congr (or_congr ⟨fun e => e.trans ha, fun e => e.trans ha.symm⟩
      ⟨fun e => e.trans hb, fun e => e.trans hb.symm⟩)) mem_upair.symm

theorem singleton_congr {a a' : PSet.{u}} (h : a ≈ a') : singleton a ≈ singleton a' :=
  ext fun _ => mem_singleton.trans <| .trans
    ⟨fun e => e.trans h, fun e => e.trans h.symm⟩ mem_singleton.symm

def pair (a b : PSet.{u}) : PSet.{u} := upair (singleton a) (upair a b)

theorem pair_congr {a a' b b' : PSet.{u}} (ha : a ≈ a') (hb : b ≈ b') : pair a b ≈ pair a' b' :=
  upair_congr (singleton_congr ha) (upair_congr ha hb)

theorem self_mem_singleton (a : PSet.{u}) : a ∈ singleton a := mem_singleton.2 (Equiv.refl _)

theorem singleton_eq_upair {a c d : PSet.{u}} (h : singleton a ≈ upair c d) : c ≈ a ∧ d ≈ a :=
  ⟨mem_singleton.1 ((mem_congr_right h).2 (mem_upair_left c d)),
   mem_singleton.1 ((mem_congr_right h).2 (mem_upair_right c d))⟩

theorem pair_inj {a b c d : PSet.{u}} (h : pair a b ≈ pair c d) : a ≈ c ∧ b ≈ d := by
  have h1 : singleton a ∈ pair c d := (mem_congr_right h).1 (mem_upair_left _ _)
  have hac : a ≈ c := Stable.of_nn (mem_upair.1 h1) fun
    | .inl e => mem_singleton.1 ((mem_congr_right e).1 (self_mem_singleton a))
    | .inr e => (singleton_eq_upair e).1.symm
  refine ⟨hac, ?_⟩
  have h2 : upair a b ∈ pair c d := (mem_congr_right h).1 (mem_upair_right _ _)
  have h3 : upair c d ∈ pair a b := (mem_congr_right h).2 (mem_upair_right _ _)
  have hb : b ∈ upair a b := mem_upair_right a b
  have hd : d ∈ upair c d := mem_upair_right c d
  refine Stable.of_nn (mem_upair.1 h2) fun h2 => Stable.of_nn (mem_upair.1 h3) fun h3 => ?_
  rcases h2 with e | e
  · have hbc : b ≈ c := mem_singleton.1 ((mem_congr_right e).1 hb)
    rcases h3 with e' | e'
    · exact hbc.trans (hac.symm.trans (mem_singleton.1 ((mem_congr_right e').1 hd)).symm)
    · exact Stable.of_nn (mem_upair.1 ((mem_congr_right e').1 hd)) fun
        | .inl e'' => hbc.trans (hac.symm.trans e''.symm)
        | .inr e'' => e''.symm
  · refine Stable.of_nn (mem_upair.1 ((mem_congr_right e).1 hb)) fun
      | .inl e' => ?_
      | .inr e' => e'
    exact Stable.of_nn (mem_upair.1 ((mem_congr_right e).2 hd)) fun
      | .inl e'' => e'.trans (hac.symm.trans e''.symm)
      | .inr e'' => e''.symm

/-- Triples, as nested pairs. -/
def triple (a b c : PSet.{u}) : PSet.{u} := pair a (pair b c)

theorem triple_congr {a a' b b' c c' : PSet.{u}} (ha : a ≈ a') (hb : b ≈ b') (hc : c ≈ c') :
    triple a b c ≈ triple a' b' c' :=
  pair_congr ha (pair_congr hb hc)

theorem triple_inj {a b c a' b' c' : PSet.{u}} (h : triple a b c ≈ triple a' b' c') :
    a ≈ a' ∧ b ≈ b' ∧ c ≈ c' :=
  have ⟨h1, h2⟩ := pair_inj h
  have ⟨h3, h4⟩ := pair_inj h2
  ⟨h1, h3, h4⟩
