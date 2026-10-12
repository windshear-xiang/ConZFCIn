import Vendor.ConZF.Words
/-!
Finite definition programs as ordinal words, evaluated by a stack machine (conzf20, con31–32,
with the pointer discipline replaced by a stack). A program is an ordinal word; a token below `9`
is an opcode and any other ordinal is pushed as a value. Opcodes: `0, 1, 3` pop two values and
push the code of a membership, equality, or implication; `2` pushes the code of falsum; `4` pops
a value and pushes the code of a universal; `6` pushes `∅`; `7` pops a value and pushes its
successor; `8` pops a package and a value and pushes their cons; `5` pops a stage, a code, and a
package and pushes the value of the package at the level of the stage (the first Separation of
the guarded `Def` adapter). Stacks are pure finite functions on numerals (`Push`, `Top`); a run
is a pure finite history of stacks (`Run`), and the denotation of a program is the top of its
final stack from the empty stack (`Den`). Every predicate has a fixed native formula with exact
semantics in a `SynZF` class. Evaluation is functional up to bisimulation (`Den.unique`); no
pointers occur, so programs concatenate without shifting, and every constructible set is the
denotation of a program of the class (`coverage`).
-/
universe u

namespace PSet
open Fml CardF LF AssignF RecF CodeF DefAdapter SetSatF Reflection

/-! ### Stacks -/

/-- `s' = s ∪ {⟨m, v⟩}` for the numeral domain `m` of `s`. -/
def Push (s v s' : PSet.{u}) : Prop :=
  ¬¬∃ m, m ∈ omega ∧ IsMap s m ∧ ∀ q, q ∈ s' ↔ ¬¬(q ∈ s ∨ q ≈ pair m v)

/-- `v` is the last entry of `s`. -/
def Top (s v : PSet.{u}) : Prop := ¬¬∃ m, pair m v ∈ s ∧ IsMap s (succ m)

instance {s v s' : PSet.{u}} : Stable (Push s v s') := inferInstanceAs (Stable (¬_))
instance {s v : PSet.{u}} : Stable (Top s v) := inferInstanceAs (Stable (¬_))

/-- Append a value to the first `m` entries of a native environment. -/
def snoc (m : Nat) (vs : Nat → PSet.{u}) (v : PSet.{u}) : Nat → PSet.{u} := fun i => if i < m then vs i else v

theorem snoc_lt {m : Nat} {vs : Nat → PSet.{u}} {v : PSet.{u}} {i : Nat} (h : i < m) : snoc m vs v i = vs i := by
  show (if i < m then vs i else v) = vs i
  split
  · rfl
  · exact absurd h ‹_›

theorem snoc_eq {m : Nat} {vs : Nat → PSet.{u}} {v : PSet.{u}} : snoc m vs v m = v := by
  show (if m < m then vs m else v) = v
  split
  · exact absurd ‹m < m› (Nat.lt_irrefl m)
  · rfl

theorem isMap_pack (m : Nat) (vs : Nat → PSet.{u}) : IsMap (pack m vs) (ofNat m) := by
  refine ⟨fun q hq => ?_, fun i hi => ?_, fun i v v' h1 h2 => ?_⟩
  · exact nn_map (fun ⟨i, hi, e'⟩ => ⟨ofNat i, vs i, mem_ofNat.2 (nn_intro ⟨i, hi, Equiv.refl _⟩), e'⟩) (mem_pack.1 hq)
  · refine Stable.of_nn (mem_ofNat.1 hi) fun ⟨k, hk, ek⟩ => ?_
    exact nn_intro ⟨vs k, mem_pack.2 (nn_intro ⟨k, hk, pair_congr ek (Equiv.refl _)⟩)⟩
  · refine Stable.of_nn (mem_pack.1 h1) fun ⟨j, _, e1⟩ => Stable.of_nn (mem_pack.1 h2) fun ⟨j', _, e2⟩ => ?_
    have ⟨ej, ev⟩ := pair_inj e1
    have ⟨ej', ev'⟩ := pair_inj e2
    have : j = j' := ofNat_inj (ej.symm.trans ej')
    subst this
    exact ev.trans ev'.symm

theorem push_pack (m : Nat) (vs : Nat → PSet.{u}) (v : PSet.{u}) : Push (pack m vs) v (pack (m+1) (snoc m vs v)) := by
  refine nn_intro ⟨ofNat m, ofNat_mem_omega m, isMap_pack m vs, fun q => mem_pack.trans ⟨fun k => nn_map (fun ⟨i, hi, e⟩ => ?_) k,
    fun k => nn_bind k fun
      | .inl h => nn_map (fun ⟨i, hi, e⟩ => ⟨i, Nat.lt_succ_of_lt hi, by rw [snoc_lt hi]; exact e⟩) (mem_pack.1 h)
      | .inr e => nn_intro ⟨m, Nat.lt_succ_self m, by rw [snoc_eq]; exact e⟩⟩⟩
  rcases Nat.lt_or_ge i m with h' | h'
  · rw [snoc_lt h'] at e
    exact .inl (mem_pack.2 (nn_intro ⟨i, h', e⟩))
  · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
    rw [snoc_eq] at e
    exact .inr e

theorem top_pack (m : Nat) (vs : Nat → PSet.{u}) : Top (pack (m+1) vs) (vs m) :=
  nn_intro ⟨ofNat m, mem_pack.2 (nn_intro ⟨m, Nat.lt_succ_self m, Equiv.refl _⟩), isMap_pack (m+1) vs⟩

theorem Push.congr {s v s' t w t' : PSet.{u}} (es : s ≈ t) (ev : v ≈ w) (es' : s' ≈ t') (h : Push s v s') : Push t w t' :=
  nn_map (fun ⟨m, hm, hmap, hq⟩ => ⟨m, hm, hmap.congr es, fun q => (mem_congr_right es').symm.trans ((hq q).trans
    (nn_congr (or_congr (mem_congr_right es) ⟨fun e => e.trans (pair_congr (Equiv.refl _) ev),
      fun e => e.trans (pair_congr (Equiv.refl _) ev.symm)⟩)))⟩) h

theorem Top.congr {s v t w : PSet.{u}} (es : s ≈ t) (ev : v ≈ w) (h : Top s v) : Top t w :=
  nn_map (fun ⟨m, hm, hmap⟩ => ⟨m, (mem_congr_right es).1 ((mem_congr_left (pair_congr (Equiv.refl _) ev)).1 hm), hmap.congr es⟩) h

theorem Push.isMap {s v s' m : PSet.{u}} (h : Push s v s') (hm : IsMap s m) : IsMap s' (succ m) := by
  refine Stable.of_nn h fun ⟨m', _, hm', hq⟩ => ?_
  have em : m' ≈ m := hm'.dom_unique hm
  refine ⟨fun q hq' => nn_bind ((hq q).1 hq') fun
      | .inl h => nn_map (fun ⟨i, w, hi, e⟩ => ⟨i, w, mem_succ_of_mem hi, e⟩) (hm.1 q h)
      | .inr e => nn_intro ⟨m, v, self_mem_succ m, e.trans (pair_congr em (Equiv.refl _))⟩,
    fun i hi => Stable.of_nn (mem_succ.1 hi) fun
      | .inl h => nn_map (fun ⟨w, hw⟩ => ⟨w, (hq _).2 (nn_intro (.inl hw))⟩) (hm.2.1 i h)
      | .inr e => nn_intro ⟨v, (hq _).2 (nn_intro (.inr (pair_congr (e.trans em.symm) (Equiv.refl _))))⟩,
    fun i w w' h1 h2 => ?_⟩
  refine Stable.of_nn ((hq _).1 h1) fun k1 => Stable.of_nn ((hq _).1 h2) fun k2 => ?_
  rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
  · exact hm.2.2 i w w' k1 k2
  · have ⟨ei, _⟩ := pair_inj k2
    exact (not_mem_self m' (Stable.of_nn (hm.1 _ k1) fun ⟨_, _, hi, e⟩ =>
      (mem_congr_left ((pair_inj e).1.symm.trans ei)).1 ((mem_congr_right em.symm).1 hi))).elim
  · have ⟨ei, _⟩ := pair_inj k1
    exact (not_mem_self m' (Stable.of_nn (hm.1 _ k2) fun ⟨_, _, hi, e⟩ =>
      (mem_congr_left ((pair_inj e).1.symm.trans ei)).1 ((mem_congr_right em.symm).1 hi))).elim
  · exact (pair_inj k1).2.trans (pair_inj k2).2.symm

theorem Push.top {s v s' : PSet.{u}} (h : Push s v s') : Top s' v :=
  Stable.of_nn h fun ⟨m, _, hm, hq⟩ => nn_intro ⟨m, (hq _).2 (nn_intro (.inr (Equiv.refl _))), h.isMap hm⟩

theorem Push.unique {s v s₁ s₂ : PSet.{u}} (h1 : Push s v s₁) (h2 : Push s v s₂) : s₁ ≈ s₂ := by
  refine Stable.of_nn h1 fun ⟨m, _, hm, hq⟩ => Stable.of_nn h2 fun ⟨m', _, hm', hq'⟩ => ?_
  have em := hm.dom_unique hm'
  refine PSet.ext fun q => (hq q).trans (Iff.trans (nn_congr (or_congr Iff.rfl
    ⟨fun e => e.trans (pair_congr em (Equiv.refl _)), fun e => e.trans (pair_congr em.symm (Equiv.refl _))⟩)) (hq' q).symm)

theorem Top.unique {s v v' : PSet.{u}} (h1 : Top s v) (h2 : Top s v') : v ≈ v' := by
  refine Stable.of_nn h1 fun ⟨m, hm, hmap⟩ => Stable.of_nn h2 fun ⟨m', hm', hmap'⟩ => ?_
  have em : m ≈ m' := succ_inj (hmap.dom_unique hmap')
  exact hmap.2.2 m v v' hm ((mem_congr_left (pair_congr em.symm (Equiv.refl _))).1 hm')

/-- Popping is deterministic: the stack below and the value are determined. -/
theorem Push.inj {s₁ v s₂ w s : PSet.{u}} (h1 : Push s₁ v s) (h2 : Push s₂ w s) : s₁ ≈ s₂ ∧ v ≈ w := by
  refine Stable.of_nn h1 fun ⟨m₁, _, hm₁, hq₁⟩ => Stable.of_nn h2 fun ⟨m₂, _, hm₂, hq₂⟩ => ?_
  have hs₁ : IsMap s (succ m₁) := h1.isMap hm₁
  have hs₂ : IsMap s (succ m₂) := h2.isMap hm₂
  have em : m₁ ≈ m₂ := succ_inj (hs₁.dom_unique hs₂)
  have hv : pair m₁ v ∈ s := (hq₁ _).2 (nn_intro (.inr (Equiv.refl _)))
  have hw : pair m₁ w ∈ s := (mem_congr_left (pair_congr em.symm (Equiv.refl _))).1 ((hq₂ _).2 (nn_intro (.inr (Equiv.refl _))))
  refine ⟨PSet.ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩, hs₁.2.2 m₁ v w hv hw⟩
  · refine Stable.of_nn ((hq₂ q).1 ((hq₁ q).2 (nn_intro (.inl hq)))) fun
      | .inl h => h
      | .inr e => ?_
    exact (not_mem_self m₂ (Stable.of_nn (hm₁.1 q hq) fun ⟨_, _, hi, e'⟩ =>
      (mem_congr_left (pair_inj (e'.symm.trans e)).1).1 ((mem_congr_right em).1 hi))).elim
  · refine Stable.of_nn ((hq₁ q).1 ((hq₂ q).2 (nn_intro (.inl hq)))) fun
      | .inl h => h
      | .inr e => ?_
    exact (not_mem_self m₁ (Stable.of_nn (hm₂.1 q hq) fun ⟨_, _, hi, e'⟩ =>
      (mem_congr_left (pair_inj (e'.symm.trans e)).1).1 ((mem_congr_right em.symm).1 hi))).elim

namespace LF

/-- `s' = s ∪ {⟨m, v⟩}` with `m` the domain of `s`; `ω` at `w`. Variables `s v s' w`. -/
def pushF (s v s' w : Nat) : Fml :=
  ex (and (mem 0 (w+1)) (and (mapF (s+1) 0) (all (iff (mem 0 (s'+2)) (or (mem 0 (s+2)) (pairF 0 1 (v+2)))))))

/-- `v` is the last entry of `s`. Variables `s v`. -/
def topF (s v : Nat) : Fml := ex (and (pairMemF (s+1) 0 (v+1)) (ex (and (succF 0 1) (mapF (s+2) 0))))

end LF

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hM hE

theorem sat_pushF (s v s' w : Nat) (hw : E w ≈ PSet.omega) : Sat M (pushF s v s' w) E ↔ Push (E s) (E v) (E s') := by
  have hN := hM.toTransClass
  refine sat_ex.trans (nn_congr ⟨fun ⟨m, hmM, hs⟩ => ?_, fun ⟨m, hm, hmap, hq⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h3, h4⟩ := sat_and.1 h2
    have hE1 := Env.cons_mem hmM hE
    refine ⟨m, (mem_congr_right hw).1 h1, (hN.sat_mapF hE1 (s+1) 0).1 h3, fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
    · have hqM := hN.trans (hE s') hq
      have hE2 := Env.cons_mem hqM hE1
      exact nn_map (fun h => h.imp id fun h => (hN.sat_pairF hE2 0 1 (v+2)).1 h) (sat_or.1 ((sat_iff.1 (h4 q hqM)).1 hq))
    · have hqM : M q := have := hM.stable q; Stable.of_nn hq fun
        | .inl h => hN.trans (hE s) h
        | .inr e => hN.resp e.symm (hN.pair_mem hmM (hE v))
      have hE2 := Env.cons_mem hqM hE1
      exact (sat_iff.1 (h4 q hqM)).2 (sat_or.2 (nn_map (fun h => h.imp id fun h => (hN.sat_pairF hE2 0 1 (v+2)).2 h) hq))
  · have hmM : M m := hN.trans (hN.resp hw (hE w)) hm
    have hE1 := Env.cons_mem hmM hE
    refine ⟨m, hmM, sat_and.2 ⟨(mem_congr_right hw).2 hm, sat_and.2 ⟨(hN.sat_mapF hE1 (s+1) 0).2 hmap, fun q hqM => ?_⟩⟩⟩
    have hE2 := Env.cons_mem hqM hE1
    exact sat_iff.2 ((hq q).trans (Iff.trans (nn_congr (or_congr Iff.rfl (hN.sat_pairF hE2 0 1 (v+2)).symm))
      (sat_or (M := M) (φ := mem 0 (s+2)) (ψ := pairF 0 1 (v+2)) (e := Env.cons q (Env.cons m E))).symm))

theorem sat_topF (s v : Nat) : Sat M (topF s v) E ↔ Top (E s) (E v) := by
  have hN := hM.toTransClass
  refine sat_ex.trans (nn_congr ⟨fun ⟨m, hmM, hs⟩ => ?_, fun ⟨m, hm, hmap⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    have hE1 := Env.cons_mem hmM hE
    refine ⟨m, (hN.sat_pairMemF hE1 (s+1) 0 (v+1)).1 h1, ?_⟩
    refine Stable.of_nn (sat_ex.1 h2) fun ⟨m', hm'M, hs⟩ => ?_
    have ⟨h3, h4⟩ := sat_and.1 hs
    have hE2 := Env.cons_mem hm'M hE1
    exact ((hN.sat_mapF hE2 (s+2) 0).1 h4).congr_dom ((hN.sat_succF hE2 0 1).1 h3)
  · have hmM := (hN.of_pair_mem (hE s) hm).1
    have hE1 := Env.cons_mem hmM hE
    have hE2 := Env.cons_mem (hM.succ_mem hmM) hE1
    exact ⟨m, hmM, sat_and.2 ⟨(hN.sat_pairMemF hE1 (s+1) 0 (v+1)).2 hm, sat_ex.2 (nn_intro ⟨succ m, hM.succ_mem hmM,
      sat_and.2 ⟨(hN.sat_succF hE2 0 1).2 (Equiv.refl _), (hN.sat_mapF hE2 (s+2) 0).2 hmap⟩⟩)⟩⟩

end SynZF

/-! ### The step relation -/

/-- The opcode of a token: numerals below `9` are opcodes, every other ordinal pushes itself. -/
def Tag (τ : PSet.{u}) : Nat → Prop
  | 0 => τ ≈ ofNat 0
  | 1 => τ ≈ ofNat 1
  | 2 => τ ≈ ofNat 2
  | 3 => τ ≈ ofNat 3
  | 4 => τ ≈ ofNat 4
  | 5 => τ ≈ ofNat 5
  | 6 => τ ≈ ofNat 6
  | 7 => τ ≈ ofNat 7
  | 8 => τ ≈ ofNat 8
  | _ => ¬ τ ∈ ofNat 9

/-- Pop two values and push a tagged pair of them. -/
def CaseBin (t : Nat) (s s' : PSet.{u}) : Prop :=
  ¬¬∃ b s₁, Push s₁ b s ∧ ¬¬∃ a s₂, Push s₂ a s₁ ∧ ¬¬∃ q, q ≈ pair (ofNat t) (pair a b) ∧ Push s₂ q s'

/-- The effect of an opcode on a stack, in the class `M`. -/
def Case (M : PSet.{u} → Prop) : Nat → PSet.{u} → PSet.{u} → PSet.{u} → Prop
  | 0, _, s, s' => CaseBin 0 s s'
  | 1, _, s, s' => CaseBin 1 s s'
  | 2, _, s, s' => ¬¬∃ q, q ≈ pair (ofNat 2) empty ∧ Push s q s'
  | 3, _, s, s' => CaseBin 3 s s'
  | 4, _, s, s' => ¬¬∃ a s₁, Push s₁ a s ∧ ¬¬∃ q, q ≈ pair (ofNat 4) a ∧ Push s₁ q s'
  | 5, _, s, s' => ¬¬∃ β s₁, Push s₁ β s ∧ ¬¬∃ q s₂, Push s₂ q s₁ ∧ ¬¬∃ p s₃, Push s₃ p s₂ ∧
      ¬¬∃ A, OrdLevel M β A ∧ ¬¬∃ y, y ≈ SynZF.valueOf (M := M) setSatF A q p ∧ Push s₃ y s'
  | 6, _, s, s' => ¬¬∃ z, z ≈ empty ∧ Push s z s'
  | 7, _, s, s' => ¬¬∃ a s₁, Push s₁ a s ∧ ¬¬∃ b, b ≈ succ a ∧ Push s₁ b s'
  | 8, _, s, s' => ¬¬∃ p s₁, Push s₁ p s ∧ ¬¬∃ v s₂, Push s₂ v s₁ ∧ ¬¬∃ t, IsCons t v p ∧ Push s₂ t s'
  | _, τ, s, s' => Push s τ s'

/-- **The step**: some opcode applies. -/
def Step (M : PSet.{u} → Prop) (τ s s' : PSet.{u}) : Prop := ¬¬∃ k, k < 10 ∧ Tag τ k ∧ Case M k τ s s'

instance {M : PSet.{u} → Prop} {τ s s' : PSet.{u}} : Stable (Step M τ s s') := inferInstanceAs (Stable (¬_))

theorem Tag.unique {τ : PSet.{u}} : ∀ {k k' : Nat}, k < 10 → k' < 10 → Tag τ k → Tag τ k' → k = k' := by
  have key : ∀ {k : Nat}, k < 9 → Tag τ k → τ ≈ ofNat k := by
    intro k hk h
    match k, h with
    | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h => exact h
    | k+9, _ => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim
  have key9 : ∀ {k : Nat}, k < 10 → ¬ k < 9 → Tag τ k → ¬ τ ∈ ofNat 9 := by
    intro k hk hk' h
    match k, h with
    | 9, h => exact h
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ => exact absurd (by decide) hk'
    | k+10, _ => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim
  intro k k' hk hk' h h'
  rcases Nat.lt_or_ge k 9 with h9 | h9 <;> rcases Nat.lt_or_ge k' 9 with h9' | h9'
  · exact ofNat_inj ((key h9 h).symm.trans (key h9' h'))
  · exact (key9 hk' (Nat.not_lt_of_ge h9') h' (mem_ofNat.2 (nn_intro ⟨k, h9, key h9 h⟩))).elim
  · exact (key9 hk (Nat.not_lt_of_ge h9) h (mem_ofNat.2 (nn_intro ⟨k', h9', key h9' h'⟩))).elim
  · have e1 : k = 9 := Nat.le_antisymm (Nat.le_of_lt_succ hk) h9
    have e2 : k' = 9 := Nat.le_antisymm (Nat.le_of_lt_succ hk') h9'
    rw [e1, e2]

theorem IsCons.congr_vp {t v v' p p' : PSet.{u}} (ev : v ≈ v') (ep : p ≈ p') (h : IsCons t v p) : IsCons t v' p' :=
  ⟨(mem_congr_left (pair_congr (Equiv.refl _) ev)).1 h.1,
   fun i w hw => h.2.1 i w ((mem_congr_right ep).2 hw),
   fun i w hw => (mem_congr_right ep).1 (h.2.2.1 i w hw),
   fun q hq => nn_map (fun h => h.imp (fun e => e.trans (pair_congr (Equiv.refl _) ev))
     fun k => nn_map (fun ⟨i, w, hw, e⟩ => ⟨i, w, (mem_congr_right ep).1 hw, e⟩) k) (h.2.2.2 q hq)⟩

/-- The value of a package respects bisimulation in all three arguments. -/
theorem SynZF.valueOf_congr_all {M : PSet.{u} → Prop} {S : Fml} {A A' q q' p p' : PSet.{u}} (eA : A ≈ A') (eqq : q ≈ q') (ep : p ≈ p') :
    SynZF.valueOf (M := M) S A q p ≈ SynZF.valueOf (M := M) S A' q' p' := by
  have hψ : ∀ (A q p : PSet.{u}) (x x' : PSet.{u}), x ≈ x' →
      Sat M (valueSepF S) (Env.cons x (Env.cons A (Env.cons q (Env.cons p envω)))) →
      Sat M (valueSepF S) (Env.cons x' (Env.cons A (Env.cons q (Env.cons p envω)))) := fun _ _ _ _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine PSet.ext fun x => (mem_sep (hψ A q p)).trans (Iff.trans (and_congr (mem_congr_right eA)
    (Sat.resp_iff (fun _ => Iff.rfl) _ (Env.cons_resp (Equiv.refl _) (Env.cons_resp eA (Env.cons_resp eqq
      (Env.cons_resp ep fun _ => Equiv.refl _)))))) (mem_sep (hψ A' q' p')).symm)

theorem CaseBin.det {t : Nat} {s s₁ s₂ : PSet.{u}} (h1 : CaseBin t s s₁) (h2 : CaseBin t s s₂) : s₁ ≈ s₂ := by
  refine Stable.of_nn h1 fun ⟨b, u₁, hb, k⟩ => Stable.of_nn k fun ⟨a, u₂, ha, k⟩ => Stable.of_nn k fun ⟨q, eq₁, hq⟩ =>
    Stable.of_nn h2 fun ⟨b', u₁', hb', k'⟩ => Stable.of_nn k' fun ⟨a', u₂', ha', k'⟩ => Stable.of_nn k' fun ⟨q', eq₂, hq'⟩ => ?_
  have ⟨eu₁, eb⟩ := hb.inj hb'
  have ⟨eu₂, ea⟩ := ha.inj (ha'.congr (Equiv.refl _) (Equiv.refl _) eu₁.symm)
  have eqq : q ≈ q' := eq₁.trans ((pair_congr (Equiv.refl _) (pair_congr ea eb)).trans eq₂.symm)
  exact hq.unique (hq'.congr eu₂.symm eqq.symm (Equiv.refl _))

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

omit hM in
/-- **Determinism of the step**, up to bisimulation. -/
theorem Case.det : ∀ {k : Nat}, k < 10 → ∀ {τ s s₁ s₂ : PSet.{u}}, Case M k τ s s₁ → Case M k τ s s₂ → s₁ ≈ s₂ := by
  intro k hk τ s s₁ s₂ h1 h2
  match k, h1, h2 with
  | k+10, _, _ => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim
  | 0, h1, h2 | 1, h1, h2 | 3, h1, h2 => exact CaseBin.det h1 h2
  | 2, h1, h2 =>
    refine Stable.of_nn h1 fun ⟨q, e, hq⟩ => Stable.of_nn h2 fun ⟨q', e', hq'⟩ => ?_
    exact hq.unique (hq'.congr (Equiv.refl _) (e'.trans e.symm) (Equiv.refl _))
  | 4, h1, h2 =>
    refine Stable.of_nn h1 fun ⟨a, u, ha, k⟩ => Stable.of_nn k fun ⟨q, e, hq⟩ =>
      Stable.of_nn h2 fun ⟨a', u', ha', k'⟩ => Stable.of_nn k' fun ⟨q', e', hq'⟩ => ?_
    have ⟨eu, ea⟩ := ha.inj ha'
    exact hq.unique (hq'.congr eu.symm (e'.trans ((pair_congr (Equiv.refl _) ea.symm).trans e.symm)) (Equiv.refl _))
  | 5, h1, h2 =>
    refine Stable.of_nn h1 fun ⟨β, u₁, hβ, k⟩ => Stable.of_nn k fun ⟨q, u₂, hq, k⟩ => Stable.of_nn k fun ⟨p, u₃, hp, k⟩ =>
      Stable.of_nn k fun ⟨A, hA, k⟩ => Stable.of_nn k fun ⟨y, ey, hy⟩ =>
      Stable.of_nn h2 fun ⟨β', u₁', hβ', k'⟩ => Stable.of_nn k' fun ⟨q', u₂', hq', k'⟩ => Stable.of_nn k' fun ⟨p', u₃', hp', k'⟩ =>
      Stable.of_nn k' fun ⟨A', hA', k'⟩ => Stable.of_nn k' fun ⟨y', ey', hy'⟩ => ?_
    have ⟨eu₁, eβ⟩ := hβ.inj hβ'
    have ⟨eu₂, eqq⟩ := hq.inj (hq'.congr (Equiv.refl _) (Equiv.refl _) eu₁.symm)
    have ⟨eu₃, ep⟩ := hp.inj (hp'.congr (Equiv.refl _) (Equiv.refl _) eu₂.symm)
    have eA : A ≈ A' := level_unique hA.1 hA.2 (level_congr eβ.symm hA'.2)
    have eyy : y ≈ y' := ey.trans ((SynZF.valueOf_congr_all eA eqq ep).trans ey'.symm)
    exact hy.unique (hy'.congr eu₃.symm eyy.symm (Equiv.refl _))
  | 6, h1, h2 =>
    refine Stable.of_nn h1 fun ⟨z, e, hz⟩ => Stable.of_nn h2 fun ⟨z', e', hz'⟩ => ?_
    exact hz.unique (hz'.congr (Equiv.refl _) (e'.trans e.symm) (Equiv.refl _))
  | 7, h1, h2 =>
    refine Stable.of_nn h1 fun ⟨a, u, ha, k⟩ => Stable.of_nn k fun ⟨b, e, hb⟩ =>
      Stable.of_nn h2 fun ⟨a', u', ha', k'⟩ => Stable.of_nn k' fun ⟨b', e', hb'⟩ => ?_
    have ⟨eu, ea⟩ := ha.inj ha'
    exact hb.unique (hb'.congr eu.symm (e'.trans ((succ_congr ea.symm).trans e.symm)) (Equiv.refl _))
  | 8, h1, h2 =>
    refine Stable.of_nn h1 fun ⟨p, u₁, hp, k⟩ => Stable.of_nn k fun ⟨v, u₂, hv, k⟩ => Stable.of_nn k fun ⟨t, ht, hpush⟩ =>
      Stable.of_nn h2 fun ⟨p', u₁', hp', k'⟩ => Stable.of_nn k' fun ⟨v', u₂', hv', k'⟩ => Stable.of_nn k' fun ⟨t', ht', hpush'⟩ => ?_
    have ⟨eu₁, ep⟩ := hp.inj hp'
    have ⟨eu₂, ev⟩ := hv.inj (hv'.congr (Equiv.refl _) (Equiv.refl _) eu₁.symm)
    have et : t ≈ t' := IsCons.unique ht (IsCons.congr_vp ev.symm ep.symm ht')
    exact hpush.unique (hpush'.congr eu₂.symm et.symm (Equiv.refl _))
  | 9, h1, h2 => exact h1.unique h2

end SynZF

theorem SynZF.Step.det {M : PSet.{u} → Prop} (_hM : SynZF M) {τ s s₁ s₂ : PSet.{u}} (h1 : Step M τ s s₁) (h2 : Step M τ s s₂) : s₁ ≈ s₂ := by
  refine Stable.of_nn h1 fun ⟨k, hk, ht, hc⟩ => Stable.of_nn h2 fun ⟨k', hk', ht', hc'⟩ => ?_
  cases Tag.unique hk hk' ht ht'
  exact SynZF.Case.det hk hc hc'

theorem Tag.congr {τ τ' : PSet.{u}} (e : τ ≈ τ') : ∀ {k : Nat}, k < 10 → Tag τ k → Tag τ' k := by
  intro k hk h
  match k, h with
  | 0, h | 1, h | 2, h | 3, h | 4, h | 5, h | 6, h | 7, h | 8, h => exact e.symm.trans h
  | 9, h => exact fun k => h ((mem_congr_left e).2 k)
  | k+10, _ => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim

theorem Step.congr {M : PSet.{u} → Prop} {τ τ' s s' t t' : PSet.{u}} (eτ : τ ≈ τ') (es : s ≈ t) (es' : s' ≈ t') (h : Step M τ s s') :
    Step M τ' t t' := by
  refine nn_map (fun ⟨k, hk, ht, hc⟩ => ⟨k, hk, Tag.congr eτ hk ht, ?_⟩) h
  match k, hc with
  | k+10, _ => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim
  | 0, hc | 1, hc | 3, hc =>
    exact nn_map (fun ⟨b, s₁, hb, k⟩ => ⟨b, s₁, hb.congr (Equiv.refl _) (Equiv.refl _) es, nn_map (fun ⟨a, s₂, ha, k⟩ =>
      ⟨a, s₂, ha, nn_map (fun ⟨q, e, hq⟩ => ⟨q, e, hq.congr (Equiv.refl _) (Equiv.refl _) es'⟩) k⟩) k⟩) hc
  | 2, hc | 6, hc =>
    exact nn_map (fun ⟨q, e, hq⟩ => ⟨q, e, hq.congr es (Equiv.refl _) es'⟩) hc
  | 4, hc | 7, hc =>
    exact nn_map (fun ⟨a, s₁, ha, k⟩ => ⟨a, s₁, ha.congr (Equiv.refl _) (Equiv.refl _) es, nn_map (fun ⟨q, e, hq⟩ =>
      ⟨q, e, hq.congr (Equiv.refl _) (Equiv.refl _) es'⟩) k⟩) hc
  | 5, hc =>
    exact nn_map (fun ⟨β, s₁, hβ, k⟩ => ⟨β, s₁, hβ.congr (Equiv.refl _) (Equiv.refl _) es, nn_map (fun ⟨q, s₂, hq, k⟩ =>
      ⟨q, s₂, hq, nn_map (fun ⟨p, s₃, hp, k⟩ => ⟨p, s₃, hp, nn_map (fun ⟨A, hA, k⟩ => ⟨A, hA, nn_map (fun ⟨y, e, hy⟩ =>
        ⟨y, e, hy.congr (Equiv.refl _) (Equiv.refl _) es'⟩) k⟩) k⟩) k⟩) k⟩) hc
  | 8, hc =>
    exact nn_map (fun ⟨p, s₁, hp, k⟩ => ⟨p, s₁, hp.congr (Equiv.refl _) (Equiv.refl _) es, nn_map (fun ⟨v, s₂, hv, k⟩ =>
      ⟨v, s₂, hv, nn_map (fun ⟨t, ht, hpush⟩ => ⟨t, ht, hpush.congr (Equiv.refl _) (Equiv.refl _) es'⟩) k⟩) k⟩) hc
  | 9, hc => exact hc.congr es eτ es'

/-- The stack below a push is in the class, by Separation. -/
theorem SynZF.Push.mem_in {M : PSet.{u} → Prop} (hM : SynZF M) {s₁ v s : PSet.{u}} (h : Push s₁ v s) (hs : M s) : M s₁ ∧ M v := by
  have hN := hM.toTransClass
  have := hM.stable s₁
  have := hM.stable v
  refine Stable.of_nn h fun ⟨m, hm, hmap, hq⟩ => ?_
  have hmM : M m := hM.trans hM.omega hm
  have hv : PSet.pair m v ∈ s := (hq _).2 (nn_intro (.inr (Equiv.refl _)))
  refine ⟨?_, (hN.of_pair_mem hs hv).2⟩
  let e := Env.cons s (Env.cons m envω)
  have he : ∀ i, M (e i) := Env.cons_mem hs (Env.cons_mem hmM hM.envω_mem)
  let ψ : Fml := ex (and (mem 0 3) (ex (pairF 2 1 0)))
  refine hM.resp (PSet.ext fun q => ?_) (hM.sepM ψ he)
  refine (mem_sep fun _ _ e' k => Sat.resp _ (Env.cons_resp e' fun _ => Equiv.refl _) k).trans ⟨fun ⟨hqs, hsat⟩ => ?_, fun hq₁ => ?_⟩
  · have hqM := hM.trans hs hqs
    refine Stable.of_nn ((hq q).1 hqs) fun
      | .inl h => h
      | .inr eq' => ?_
    refine Stable.of_nn (sat_ex.1 hsat) fun ⟨i, hiM, hs'⟩ => ?_
    have ⟨h1, h2⟩ := sat_and.1 hs'
    refine Stable.of_nn (sat_ex.1 h2) fun ⟨w, hwM, h3⟩ => ?_
    have hE3 := Env.cons_mem hwM (Env.cons_mem hiM (Env.cons_mem hqM he))
    have e' := (hN.sat_pairF hE3 2 1 0).1 h3
    exact (not_mem_self m ((mem_congr_left (pair_inj (e'.symm.trans eq')).1).1 h1)).elim
  · have hqs : q ∈ s := (hq q).2 (nn_intro (.inl hq₁))
    have hqM := hM.trans hs hqs
    refine ⟨hqs, ?_⟩
    refine Stable.of_nn (hmap.1 q hq₁) fun ⟨i, w, hi, e'⟩ => ?_
    have hiM := hM.trans hmM hi
    have hpM : M (PSet.pair i w) := hM.resp e' hqM
    have hwM : M w := hM.trans (hM.trans hpM (mem_upair_right _ _)) (mem_upair_right _ _)
    have hE3 := Env.cons_mem hwM (Env.cons_mem hiM (Env.cons_mem hqM he))
    exact sat_ex.2 (nn_intro ⟨i, hiM, sat_and.2 ⟨hi, sat_ex.2 (nn_intro ⟨w, hwM, (hN.sat_pairF hE3 2 1 0).2 e'⟩)⟩⟩)


/-! ### The step formula -/

set_option maxRecDepth 200000 in
theorem bound_evalF : Bound 4 (evalF setSatF) := by decide

namespace LF

/-- `y = valueOf S A q p`: `∀ x (x ∈ y ↔ x ∈ A ∧ eval)`. Variables `y A q p`. -/
def valF (y A q p : Nat) : Fml :=
  all (iff (mem 0 (y+1)) (and (mem 0 (A+1)) (inst (evalF setSatF) [A+1, q+1, p+1, 0])))

/-- Pop two values (`b` then `a`) and push `⟨t̄, ⟨a, b⟩⟩`. -/
def caseBinF (code : Nat → Nat → Nat → Fml) (t τ s s' w : Nat) : Fml :=
  and (numF t τ) (ex (ex (and (pushF 0 1 (s+2) (w+2)) (ex (ex (and (pushF 0 1 2 (w+4))
    (ex (and (code 0 2 4) (pushF 1 0 (s'+5) (w+5))))))))))

/-- The formula of opcode `k`, variables `τ s s' w`. -/
def caseF : Nat → Nat → Nat → Nat → Nat → Fml
  | 0, τ, s, s', w => caseBinF memCodeF 0 τ s s' w
  | 1, τ, s, s', w => caseBinF eqCodeF 1 τ s s' w
  | 2, τ, s, s', w => and (numF 2 τ) (ex (and (botCodeF 0) (pushF (s+1) 0 (s'+1) (w+1))))
  | 3, τ, s, s', w => caseBinF impCodeF 3 τ s s' w
  | 4, τ, s, s', w => and (numF 4 τ) (ex (ex (and (pushF 0 1 (s+2) (w+2))
      (ex (and (allCodeF 0 2) (pushF 1 0 (s'+3) (w+3)))))))
  | 5, τ, s, s', w => and (numF 5 τ) (ex (ex (and (pushF 0 1 (s+2) (w+2)) (ex (ex (and (pushF 0 1 2 (w+4))
      (ex (ex (and (pushF 0 1 2 (w+6)) (ex (and (at2 ordLevelF 6 0)
        (ex (and (valF 0 1 5 3) (pushF 2 0 (s'+8) (w+8)))))))))))))))
  | 6, τ, s, s', w => and (numF 6 τ) (ex (and (emptyF 0) (pushF (s+1) 0 (s'+1) (w+1))))
  | 7, τ, s, s', w => and (numF 7 τ) (ex (ex (and (pushF 0 1 (s+2) (w+2))
      (ex (and (succF 0 2) (pushF 1 0 (s'+3) (w+3)))))))
  | 8, τ, s, s', w => and (numF 8 τ) (ex (ex (and (pushF 0 1 (s+2) (w+2)) (ex (ex (and (pushF 0 1 2 (w+4))
      (ex (and (consF 0 2 4) (pushF 1 0 (s'+5) (w+5))))))))))
  | _, τ, s, s', w => and (ex (and (numF 9 0) (neg (mem (τ+1) 0)))) (pushF s τ s' w)

/-- **The step formula.** Variables `τ s s' w`. -/
def stepF (τ s s' w : Nat) : Fml :=
  or (caseF 0 τ s s' w) (or (caseF 1 τ s s' w) (or (caseF 2 τ s s' w) (or (caseF 3 τ s s' w)
    (or (caseF 4 τ s s' w) (or (caseF 5 τ s s' w) (or (caseF 6 τ s s' w) (or (caseF 7 τ s s' w)
      (or (caseF 8 τ s s' w) (caseF 9 τ s s' w)))))))))

end LF

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hM hE

/-- A pop: two existentials with the pushed relation. -/
theorem sat_pop {φ : Fml} {P : PSet.{u} → PSet.{u} → Prop} (s w : Nat) (hw : E w ≈ PSet.omega)
    (hφ : ∀ b s₁, M b → M s₁ → (Sat M φ (Env.cons s₁ (Env.cons b E)) ↔ P b s₁)) :
    Sat M (ex (ex (and (pushF 0 1 (s+2) (w+2)) φ))) E ↔ ¬¬∃ b s₁, Push s₁ b (E s) ∧ P b s₁ := by
  refine sat_ex.trans ⟨fun k => nn_bind k fun ⟨b, hb, k⟩ => nn_map (fun ⟨s₁, hs₁, hs⟩ => ?_) (sat_ex.1 k),
    fun k => nn_map (fun ⟨b, s₁, hp, hP⟩ => ?_) k⟩
  · have ⟨h1, h2⟩ := sat_and.1 hs
    have hE2 := Env.cons_mem hs₁ (Env.cons_mem hb hE)
    exact ⟨b, s₁, (hM.sat_pushF hE2 0 1 (s+2) (w+2) hw).1 h1, (hφ b s₁ hb hs₁).1 h2⟩
  · have ⟨hs₁, hb⟩ := SynZF.Push.mem_in hM hp (hE s)
    have hE2 := Env.cons_mem hs₁ (Env.cons_mem hb hE)
    exact ⟨b, hb, sat_ex.2 (nn_intro ⟨s₁, hs₁, sat_and.2 ⟨(hM.sat_pushF hE2 0 1 (s+2) (w+2) hw).2 hp, (hφ b s₁ hb hs₁).2 hP⟩⟩)⟩

/-- A push of a fresh value: one existential with a defining formula. -/
theorem sat_pushVal {ψ : Fml} {Q : PSet.{u} → Prop} (a s' w : Nat) (hw : E w ≈ PSet.omega)
    (hψ : ∀ q, M q → (Sat M ψ (Env.cons q E) ↔ Q q)) :
    Sat M (ex (and ψ (pushF (a+1) 0 (s'+1) (w+1)))) E ↔ ¬¬∃ q, Q q ∧ Push (E a) q (E s') := by
  refine sat_ex.trans (nn_congr ⟨fun ⟨q, hq, hs⟩ => ?_, fun ⟨q, hQq, hp⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨q, (hψ q hq).1 h1, (hM.sat_pushF (Env.cons_mem hq hE) (a+1) 0 (s'+1) (w+1) hw).1 h2⟩
  · have := hM.stable q
    have hq : M q := Stable.of_nn hp fun ⟨m, _, _, hqs⟩ =>
      (hM.toTransClass.of_pair_mem (hE s') ((hqs _).2 (nn_intro (.inr (Equiv.refl _))))).2
    exact ⟨q, hq, sat_and.2 ⟨(hψ q hq).2 hQq, (hM.sat_pushF (Env.cons_mem hq hE) (a+1) 0 (s'+1) (w+1) hw).2 hp⟩⟩

theorem sat_valF (y A q p : Nat) : Sat M (valF y A q p) E ↔ E y ≈ valueOf (M := M) setSatF (E A) (E q) (E p) := by
  have key : ∀ x, M x → (Sat M (inst (evalF setSatF) [A+1, q+1, p+1, 0]) (Env.cons x E) ↔ EvalP M setSatF (E A) (E q) (E p) x) := by
    intro x hx
    refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_evalF bound_setSatF (hE A) (hE q) (hE p) hx (E := E) hE))
    refine sat_bound bound_evalF fun i hi => ?_
    rcases i with _ | _ | _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))))).elim
  constructor
  · intro h
    refine PSet.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have hxM := hM.trans (hE y) hx
      have ⟨h1, h2⟩ := sat_and.1 ((sat_iff.1 (h x hxM)).1 hx)
      exact (hM.mem_valueOf bound_setSatF (hE A) (hE q) (hE p)).2 ⟨h1, (key x hxM).1 h2⟩
    · have ⟨h1, h2⟩ := (hM.mem_valueOf bound_setSatF (hE A) (hE q) (hE p)).1 hx
      have hxM := hM.trans (hE A) h1
      exact (sat_iff.1 (h x hxM)).2 (sat_and.2 ⟨h1, (key x hxM).2 h2⟩)
  · intro e x hx
    exact sat_iff.2 (Iff.trans (mem_congr_right e) (Iff.trans (hM.mem_valueOf bound_setSatF (hE A) (hE q) (hE p))
      (Iff.trans (and_congr Iff.rfl (key x hx).symm) (sat_and (M := M) (φ := mem 0 (A+1))
        (ψ := inst (evalF setSatF) [A+1, q+1, p+1, 0]) (e := Env.cons x E)).symm)))

theorem sat_caseBinF {code : Nat → Nat → Nat → Fml} (t τ s s' w : Nat) (hw : E w ≈ PSet.omega)
    (hcode : ∀ {E' : Nat → PSet.{u}}, (∀ i, M (E' i)) → ∀ q i j, Sat M (code q i j) E' ↔ E' q ≈ PSet.pair (ofNat t) (PSet.pair (E' i) (E' j))) :
    Sat M (caseBinF code t τ s s' w) E ↔ E τ ≈ ofNat t ∧ CaseBin t (E s) (E s') := by
  have hN := hM.toTransClass
  refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem t τ) ?_)
  refine hM.sat_pop hE s w hw fun b s₁ hb hs₁ => ?_
  have hE2 := Env.cons_mem hs₁ (Env.cons_mem hb hE)
  refine hM.sat_pop hE2 0 (w+2) hw fun a s₂ ha hs₂ => ?_
  have hE4 := Env.cons_mem hs₂ (Env.cons_mem ha hE2)
  exact hM.sat_pushVal hE4 0 (s'+4) (w+4) hw fun q hq => hcode (Env.cons_mem hq hE4) 0 2 4


theorem sat_caseF (k : Nat) (hk : k < 10) (τ s s' w : Nat) (hw : E w ≈ PSet.omega) :
    Sat M (caseF k τ s s' w) E ↔ Tag (E τ) k ∧ Case M k (E τ) (E s) (E s') := by
  have hN := hM.toTransClass
  match k with
  | k+10 => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim
  | 0 => exact hM.sat_caseBinF hE 0 τ s s' w hw fun hE' q i j => hN.sat_memCodeF hE' hM.empty hM.succ_mem q i j
  | 1 => exact hM.sat_caseBinF hE 1 τ s s' w hw fun hE' q i j => hN.sat_eqCodeF hE' hM.empty hM.succ_mem q i j
  | 3 => exact hM.sat_caseBinF hE 3 τ s s' w hw fun hE' q i j => hN.sat_impCodeF hE' hM.empty hM.succ_mem q i j
  | 2 =>
    refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem 2 τ) ?_)
    exact hM.sat_pushVal hE s s' w hw fun q hq => hN.sat_botCodeF (Env.cons_mem hq hE) hM.empty hM.succ_mem 0
  | 6 =>
    refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem 6 τ) ?_)
    exact hM.sat_pushVal hE s s' w hw fun q hq => hN.sat_emptyF (Env.cons_mem hq hE) 0
  | 4 =>
    refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem 4 τ) ?_)
    refine hM.sat_pop hE s w hw fun a s₁ ha hs₁ => ?_
    have hE2 := Env.cons_mem hs₁ (Env.cons_mem ha hE)
    exact hM.sat_pushVal hE2 0 (s'+2) (w+2) hw fun q hq => hN.sat_allCodeF (Env.cons_mem hq hE2) hM.empty hM.succ_mem 0 2
  | 7 =>
    refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem 7 τ) ?_)
    refine hM.sat_pop hE s w hw fun a s₁ ha hs₁ => ?_
    have hE2 := Env.cons_mem hs₁ (Env.cons_mem ha hE)
    exact hM.sat_pushVal hE2 0 (s'+2) (w+2) hw fun q hq => hN.sat_succF (Env.cons_mem hq hE2) 0 2
  | 8 =>
    refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem 8 τ) ?_)
    refine hM.sat_pop hE s w hw fun p s₁ hp hs₁ => ?_
    have hE2 := Env.cons_mem hs₁ (Env.cons_mem hp hE)
    refine hM.sat_pop hE2 0 (w+2) hw fun v s₂ hv hs₂ => ?_
    have hE4 := Env.cons_mem hs₂ (Env.cons_mem hv hE2)
    exact hM.sat_pushVal hE4 0 (s'+4) (w+4) hw fun t ht => hN.sat_consF (Env.cons_mem ht hE4) 0 2 4 hM.succ_mem hM.empty
  | 5 =>
    refine sat_and.trans (and_congr (hN.sat_numF hE hM.empty hM.succ_mem 5 τ) ?_)
    refine hM.sat_pop hE s w hw fun β s₁ hβ hs₁ => ?_
    have hE2 := Env.cons_mem hs₁ (Env.cons_mem hβ hE)
    refine hM.sat_pop hE2 0 (w+2) hw fun q s₂ hq hs₂ => ?_
    have hE4 := Env.cons_mem hs₂ (Env.cons_mem hq hE2)
    refine hM.sat_pop hE4 0 (w+4) hw fun p s₃ hp hs₃ => ?_
    have hE6 := Env.cons_mem hs₃ (Env.cons_mem hp hE4)
    refine sat_ex.trans (nn_congr ⟨fun ⟨A, hA, hs⟩ => ?_, fun ⟨A, hoA, k⟩ => ?_⟩)
    · have ⟨h1, h2⟩ := sat_and.1 hs
      have hE7 := Env.cons_mem hA hE6
      have h1' := (sat_at2 (e := Env.cons A (Env.cons s₃ (Env.cons p (Env.cons s₂ (Env.cons q (Env.cons s₁ (Env.cons β E)))))))
        (i := 6) (j := 0) (e' := E) bound_ordLevelF).1 h1
      refine ⟨A, (hM.sat_ordLevelF hβ hA hE).1 h1', ?_⟩
      exact (hM.sat_pushVal hE7 1 (s'+7) (w+7) hw fun y hy => hM.sat_valF (Env.cons_mem hy hE7) 0 1 5 3).1 h2
    · have hA := (hM.level_mem_class hoA.2).2
      have hE7 := Env.cons_mem hA hE6
      have h1' := (hM.sat_ordLevelF hβ hA hE).2 hoA
      have h1 := (sat_at2 (e := Env.cons A (Env.cons s₃ (Env.cons p (Env.cons s₂ (Env.cons q (Env.cons s₁ (Env.cons β E)))))))
        (i := 6) (j := 0) (e' := E) bound_ordLevelF).2 h1'
      exact ⟨A, hA, sat_and.2 ⟨h1, (hM.sat_pushVal hE7 1 (s'+7) (w+7) hw fun y hy => hM.sat_valF (Env.cons_mem hy hE7) 0 1 5 3).2 k⟩⟩
  | 9 =>
    refine sat_and.trans (and_congr ?_ (hM.sat_pushF hE s τ s' w hw))
    have h9 : M (ofNat 9) := TransClass.ofNat_mem hM.empty hM.succ_mem 9
    refine sat_ex.trans ⟨fun k hmem => ?_, fun h => nn_intro ⟨ofNat 9, h9, sat_and.2 ⟨?_, fun hmem => h hmem⟩⟩⟩
    · refine Stable.of_nn k fun ⟨n, hn, hs⟩ => ?_
      have ⟨h1, h2⟩ := sat_and.1 hs
      have en := (hN.sat_numF (Env.cons_mem hn hE) hM.empty hM.succ_mem 9 0).1 h1
      exact h2 ((mem_congr_right en).2 hmem)
    · exact (hN.sat_numF (Env.cons_mem h9 hE) hM.empty hM.succ_mem 9 0).2 (Equiv.refl _)

/-- **The step bridge.** -/
theorem sat_stepF (τ s s' w : Nat) (hw : E w ≈ PSet.omega) : Sat M (stepF τ s s' w) E ↔ Step M (E τ) (E s) (E s') := by
  have c : ∀ k, k < 10 → (Sat M (caseF k τ s s' w) E ↔ Tag (E τ) k ∧ Case M k (E τ) (E s) (E s')) :=
    fun k hk => hM.sat_caseF hE k hk τ s s' w hw
  constructor
  · intro h
    refine Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨0, by decide, (c 0 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨1, by decide, (c 1 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨2, by decide, (c 2 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨3, by decide, (c 3 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨4, by decide, (c 4 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨5, by decide, (c 5 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨6, by decide, (c 6 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨7, by decide, (c 7 (by decide)).1 h⟩
      | .inr h => Stable.of_nn (sat_or.1 h) fun
      | .inl h => nn_intro ⟨8, by decide, (c 8 (by decide)).1 h⟩
      | .inr h => nn_intro ⟨9, by decide, (c 9 (by decide)).1 h⟩
  · intro h
    refine Stable.of_nn h fun ⟨k, hk, ht, hc⟩ => ?_
    match k, ht, hc with
    | k+10, _, _ => exact (Nat.not_lt_zero k (Nat.lt_of_add_lt_add_right hk)).elim
    | 0, ht, hc => exact sat_or.2 (nn_intro (.inl ((c 0 (by decide)).2 ⟨ht, hc⟩)))
    | 1, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 1 (by decide)).2 ⟨ht, hc⟩))))))
    | 2, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 2 (by decide)).2 ⟨ht, hc⟩)))))))))
    | 3, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 3 (by decide)).2 ⟨ht, hc⟩))))))))))))
    | 4, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 4 (by decide)).2 ⟨ht, hc⟩)))))))))))))))
    | 5, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 5 (by decide)).2 ⟨ht, hc⟩))))))))))))))))))
    | 6, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 6 (by decide)).2 ⟨ht, hc⟩)))))))))))))))))))))
    | 7, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 7 (by decide)).2 ⟨ht, hc⟩))))))))))))))))))))))))
    | 8, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inl ((c 8 (by decide)).2 ⟨ht, hc⟩)))))))))))))))))))))))))))
    | 9, ht, hc => exact sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr (sat_or.2 (nn_intro (.inr ((c 9 (by decide)).2 ⟨ht, hc⟩)))))))))))))))))))))))))))


end SynZF

/-! ### Runs and denotations -/

/-- A run of `c` (of length `n`) from the stack `S₀` to the stack `S`: a pure history of stacks in
the class, stepping by the token at each position. -/
def Run (M : PSet.{u} → Prop) (c n S₀ S : PSet.{u}) : Prop :=
  ¬¬∃ h, M h ∧ IsMap h (succ n) ∧ pair empty S₀ ∈ h ∧
    (∀ i, i ∈ n → ∀ τ, pair i τ ∈ c → ∀ s s', pair i s ∈ h → pair (succ i) s' ∈ h → Step M τ s s') ∧ pair n S ∈ h

/-- The denotation: the top of the final stack of the run from the empty stack. -/
def Den (M : PSet.{u} → Prop) (c n y : PSet.{u}) : Prop := ¬¬∃ S, Run M c n empty S ∧ Top S y

instance {M : PSet.{u} → Prop} {c n S₀ S : PSet.{u}} : Stable (Run M c n S₀ S) := inferInstanceAs (Stable (¬_))
instance {M : PSet.{u} → Prop} {c n y : PSet.{u}} : Stable (Den M c n y) := inferInstanceAs (Stable (¬_))

theorem Run.congr {M : PSet.{u} → Prop} {c c' n n' S₀ S₀' S S' : PSet.{u}} (ec : c ≈ c') (en : n ≈ n') (e₀ : S₀ ≈ S₀') (e : S ≈ S')
    (h : Run M c n S₀ S) : Run M c' n' S₀' S' :=
  nn_map (fun ⟨h, hh, hmap, h0, hst, hn⟩ => ⟨h, hh, hmap.congr_dom (succ_congr en), (mem_congr_left (pair_congr (Equiv.refl _) e₀)).1 h0,
    fun i hi τ hτ s s' hs hs' => hst i ((mem_congr_right en).2 hi) τ ((mem_congr_right ec).2 hτ) s s' hs hs',
    (mem_congr_left (pair_congr en e)).1 hn⟩) h

theorem Den.congr {M : PSet.{u} → Prop} {c c' n n' y y' : PSet.{u}} (ec : c ≈ c') (en : n ≈ n') (ey : y ≈ y') (h : Den M c n y) :
    Den M c' n' y' :=
  nn_map (fun ⟨S, hr, ht⟩ => ⟨S, hr.congr ec en (Equiv.refl _) (Equiv.refl _), ht.congr (Equiv.refl _) ey⟩) h

namespace LF

/-- The run formula. Variables `c n s₀ sf w`. -/
def runF (c n s₀ sf w : Nat) : Fml :=
  ex (and (ex (and (succF 0 (n+2)) (mapF 1 0)))
    (and (ex (and (emptyF 0) (pairMemF 1 0 (s₀+2))))
      (and (all (imp (mem 0 (n+2)) (all (imp (pairMemF (c+3) 1 0) (all (all (imp (pairMemF 4 3 1)
          (all (imp (succF 0 4) (imp (pairMemF 5 0 1) (stepF 3 2 1 (w+6))))))))))))
        (pairMemF 0 (n+1) (sf+1)))))

/-- The denotation formula. Variables `c n y w`. -/
def denF (c n y w : Nat) : Fml :=
  ex (and (ex (and (emptyF 0) (runF (c+2) (n+2) 0 1 (w+2)))) (topF 0 (y+1)))

end LF

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hM hE

/-- **The run bridge.** -/
theorem sat_runF (c n s₀ sf w : Nat) (hw : E w ≈ PSet.omega) :
    Sat M (runF c n s₀ sf w) E ↔ Run M (E c) (E n) (E s₀) (E sf) := by
  have hN := hM.toTransClass
  refine sat_ex.trans (nn_congr ⟨fun ⟨h, hh, hs⟩ => ?_, fun ⟨h, hh, hmap, h0, hst, hn⟩ => ?_⟩)
  · have hE1 := Env.cons_mem hh hE
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h3, h4⟩ := sat_and.1 h2
    have ⟨h5, h6⟩ := sat_and.1 h4
    refine ⟨h, hh, ?_, ?_, fun i hi τ hτ s s' hs hs' => ?_, (hN.sat_pairMemF hE1 0 (n+1) (sf+1)).1 h6⟩
    · refine Stable.of_nn (sat_ex.1 h1) fun ⟨m, hm, hs⟩ => ?_
      have ⟨k1, k2⟩ := sat_and.1 hs
      have hE2 := Env.cons_mem hm hE1
      exact ((hN.sat_mapF hE2 1 0).1 k2).congr_dom ((hN.sat_succF hE2 0 (n+2)).1 k1)
    · refine Stable.of_nn (sat_ex.1 h3) fun ⟨z, hz, hs⟩ => ?_
      have ⟨k1, k2⟩ := sat_and.1 hs
      have hE2 := Env.cons_mem hz hE1
      exact (mem_congr_left (pair_congr ((hN.sat_emptyF hE2 0).1 k1) (Equiv.refl _))).1 ((hN.sat_pairMemF hE2 1 0 (s₀+2)).1 k2)
    · have hiM := hM.trans (hE n) hi
      have hτM := (hN.of_pair_mem (hE c) hτ).2
      have hsM := (hN.of_pair_mem hh hs).2
      have hs'M := (hN.of_pair_mem hh hs').2
      have hE2 := Env.cons_mem hiM hE1
      have hE3 := Env.cons_mem hτM hE2
      have hE5 := Env.cons_mem hs'M (Env.cons_mem hsM hE3)
      have hE6 := Env.cons_mem (hM.succ_mem hiM) hE5
      have k := h5 i hiM hi τ hτM ((hN.sat_pairMemF hE3 (c+3) 1 0).2 hτ) s hsM s' hs'M ((hN.sat_pairMemF hE5 4 3 1).2 hs)
        (succ i) (hM.succ_mem hiM) ((hN.sat_succF hE6 0 4).2 (Equiv.refl _)) ((hN.sat_pairMemF hE6 5 0 1).2 hs')
      exact (hM.sat_stepF hE6 3 2 1 (w+6) hw).1 k
  · have hE1 := Env.cons_mem hh hE
    refine ⟨h, hh, sat_and.2 ⟨?_, sat_and.2 ⟨?_, sat_and.2 ⟨?_, (hN.sat_pairMemF hE1 0 (n+1) (sf+1)).2 hn⟩⟩⟩⟩
    · have hE2 := Env.cons_mem (hM.succ_mem (hE n)) hE1
      exact sat_ex.2 (nn_intro ⟨succ (E n), hM.succ_mem (hE n), sat_and.2 ⟨(hN.sat_succF hE2 0 (n+2)).2 (Equiv.refl _),
        (hN.sat_mapF hE2 1 0).2 hmap⟩⟩)
    · have hE2 := Env.cons_mem hM.empty hE1
      exact sat_ex.2 (nn_intro ⟨PSet.empty, hM.empty, sat_and.2 ⟨(hN.sat_emptyF hE2 0).2 (Equiv.refl _),
        (hN.sat_pairMemF hE2 1 0 (s₀+2)).2 h0⟩⟩)
    · intro i hiM hi τ hτM hτ s hsM s' hs'M hs i' hi'M hi' hs'
      have hE2 := Env.cons_mem hiM hE1
      have hE3 := Env.cons_mem hτM hE2
      have hE5 := Env.cons_mem hs'M (Env.cons_mem hsM hE3)
      have hE6 := Env.cons_mem hi'M hE5
      have ei := (hN.sat_succF hE6 0 4).1 hi'
      have k := hst i hi τ ((hN.sat_pairMemF hE3 (c+3) 1 0).1 hτ) s s' ((hN.sat_pairMemF hE5 4 3 1).1 hs)
        ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 ((hN.sat_pairMemF hE6 5 0 1).1 hs'))
      exact (hM.sat_stepF hE6 3 2 1 (w+6) hw).2 k

/-- **The denotation bridge.** -/
theorem sat_denF (c n y w : Nat) (hw : E w ≈ PSet.omega) : Sat M (denF c n y w) E ↔ Den M (E c) (E n) (E y) := by
  have hN := hM.toTransClass
  refine sat_ex.trans (nn_congr ⟨fun ⟨S, hS, hs⟩ => ?_, fun ⟨S, hr, ht⟩ => ?_⟩)
  · have hE1 := Env.cons_mem hS hE
    have ⟨h1, h2⟩ := sat_and.1 hs
    refine ⟨S, ?_, (hM.sat_topF hE1 0 (y+1)).1 h2⟩
    refine Stable.of_nn (sat_ex.1 h1) fun ⟨z, hz, hs⟩ => ?_
    have ⟨k1, k2⟩ := sat_and.1 hs
    have hE2 := Env.cons_mem hz hE1
    exact ((hM.sat_runF hE2 (c+2) (n+2) 0 1 (w+2) hw).1 k2).congr (Equiv.refl _) (Equiv.refl _) ((hN.sat_emptyF hE2 0).1 k1) (Equiv.refl _)
  · have := hM.stable S
    have hS : M S := Stable.of_nn hr fun ⟨h, hh, _, _, _, hn⟩ => (hN.of_pair_mem hh hn).2
    have hE1 := Env.cons_mem hS hE
    have hE2 := Env.cons_mem hM.empty hE1
    exact ⟨S, hS, sat_and.2 ⟨sat_ex.2 (nn_intro ⟨PSet.empty, hM.empty, sat_and.2 ⟨(hN.sat_emptyF hE2 0).2 (Equiv.refl _),
      (hM.sat_runF hE2 (c+2) (n+2) 0 1 (w+2) hw).2 hr⟩⟩), (hM.sat_topF hE1 0 (y+1)).2 ht⟩⟩

omit hE in
/-- **Functionality of the denotation.** -/
theorem Den.unique {c y y' : PSet.{u}} {N : Nat} (hc : IsMap c (ofNat N)) (h : Den M c (ofNat N) y) (h' : Den M c (ofNat N) y') : y ≈ y' := by
  refine Stable.of_nn h fun ⟨S, hr, ht⟩ => Stable.of_nn h' fun ⟨S', hr', ht'⟩ => ?_
  refine Stable.of_nn hr fun ⟨g, _, gmap, g0, gst, gn⟩ => Stable.of_nn hr' fun ⟨g', _, gmap', g0', gst', gn'⟩ => ?_
  have agree : ∀ k, k ≤ N → ∀ s s', PSet.pair (ofNat k) s ∈ g → PSet.pair (ofNat k) s' ∈ g' → s ≈ s' := by
    intro k
    induction k with
    | zero => exact fun _ s s' hs hs' => (gmap.2.2 _ s _ hs g0).trans (gmap'.2.2 _ s' _ hs' g0').symm
    | succ k ih =>
      intro hk s s' hs hs'
      have hkN : ofNat k ∈ ofNat N := mem_ofNat.2 (nn_intro ⟨k, hk, Equiv.refl _⟩)
      have hkS : ofNat k ∈ succ (ofNat N) := mem_succ_of_mem hkN
      refine Stable.of_nn (gmap.2.1 _ hkS) fun ⟨u, hu⟩ => Stable.of_nn (gmap'.2.1 _ hkS) fun ⟨u', hu'⟩ => ?_
      have eu := ih (Nat.le_of_succ_le hk) u u' hu hu'
      refine Stable.of_nn (hc.2.1 _ hkN) fun ⟨τ, hτ⟩ => ?_
      have st := gst _ hkN τ hτ u s hu hs
      have st' := gst' _ hkN τ hτ u' s' hu' hs'
      exact SynZF.Step.det hM st (st'.congr (Equiv.refl _) eu.symm (Equiv.refl _))
  have eS : S ≈ S' := agree N (Nat.le_refl N) S S' gn gn'
  exact ht.unique (ht'.congr eS.symm (Equiv.refl _))

end SynZF

/-! ### Runs of native programs -/

theorem pack_congr {n : Nat} {e e' : Nat → PSet.{u}} (h : ∀ i, i < n → e i ≈ e' i) : pack n e ≈ pack n e' :=
  PSet.ext fun _ => mem_pack.trans (Iff.trans (nn_congr (exists_congr fun i => and_congr_right fun hi =>
    ⟨fun k => k.trans (pair_congr (Equiv.refl _) (h i hi)), fun k => k.trans (pair_congr (Equiv.refl _) (h i hi).symm)⟩)) mem_pack.symm)

/-- A pop from a packed stack. -/
theorem pop_pack (m : Nat) (vs : Nat → PSet.{u}) : Push (pack m vs) (vs m) (pack (m+1) vs) :=
  (push_pack m vs (vs m)).congr (Equiv.refl _) (Equiv.refl _) (pack_congr fun i hi => by
    rcases Nat.lt_or_ge i m with h | h
    · rw [snoc_lt h]; exact Equiv.refl _
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h
      rw [snoc_eq]; exact Equiv.refl _)

/-- Values of a stack of the class are in the class. -/
theorem SynZF.pack_mem' {M : PSet.{u} → Prop} (hM : SynZF M) {m : Nat} {vs : Nat → PSet.{u}} (h : ∀ i, i < m → M (vs i)) : M (pack m vs) :=
  hM.pack_mem m h

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem run_zero {e : Nat → PSet.{u}} {S : PSet.{u}} (hS : M S) : Run M (pack 0 e) (ofNat 0) S S := by
  have hh : M (singleton (PSet.pair PSet.empty S)) := hM.single (hM.pair hM.empty hS)
  refine nn_intro ⟨_, hh, ⟨fun q hq => nn_intro ⟨PSet.empty, S, self_mem_succ _, mem_singleton.1 hq⟩,
    fun i hi => Stable.of_nn (mem_succ.1 hi) fun
      | .inl h => (not_mem_empty i h).elim
      | .inr e => nn_intro ⟨S, mem_singleton.2 (pair_congr e (Equiv.refl _))⟩,
    fun i v v' h1 h2 => (pair_inj ((mem_singleton.1 h1).trans (mem_singleton.1 h2).symm)).2⟩,
    self_mem_singleton _, fun i hi => (not_mem_empty i hi).elim, self_mem_singleton _⟩

/-- Extending a run by one token. -/
theorem run_snoc {n : Nat} {e : Nat → PSet.{u}} {S₀ S₁ S₂ τ : PSet.{u}} (hS₂ : M S₂) (h : Run M (pack n e) (ofNat n) S₀ S₁)
    (hst : Step M τ S₁ S₂) : Run M (pack (n+1) (snoc n e τ)) (ofNat (n+1)) S₀ S₂ := by
  refine nn_map (fun ⟨g, hg, gmap, g0, gst, gn⟩ => ?_) h
  let g' := PSet.union g (singleton (PSet.pair (ofNat (n+1)) S₂))
  have hg' : M g' := hM.union hg (hM.single (hM.pair (hM.trans hM.omega (ofNat_mem_omega _)) hS₂))
  have memg' : ∀ q, q ∈ g' ↔ ¬¬(q ∈ g ∨ q ≈ PSet.pair (ofNat (n+1)) S₂) := fun q =>
    mem_union.trans (nn_congr (or_congr Iff.rfl mem_singleton))
  have hnn : ¬ ofNat (n+1) ∈ succ (ofNat n) := not_mem_self _
  refine ⟨g', hg', ⟨fun q hq => ?_, fun i hi => ?_, fun i v v' h1 h2 => ?_⟩, (memg' _).2 (nn_intro (.inl g0)),
    fun i hi τ' hτ' s s' hs hs' => ?_, (memg' _).2 (nn_intro (.inr (Equiv.refl _)))⟩
  · refine Stable.of_nn ((memg' q).1 hq) fun
      | .inl h => nn_map (fun ⟨i, v, hi, e'⟩ => ⟨i, v, mem_succ_of_mem hi, e'⟩) (gmap.1 q h)
      | .inr e' => nn_intro ⟨_, S₂, self_mem_succ _, e'⟩
  · refine Stable.of_nn (mem_succ.1 hi) fun
      | .inl h => nn_map (fun ⟨v, hv⟩ => ⟨v, (memg' _).2 (nn_intro (.inl hv))⟩) (gmap.2.1 i h)
      | .inr e' => nn_intro ⟨S₂, (memg' _).2 (nn_intro (.inr (pair_congr e' (Equiv.refl _))))⟩
  · refine Stable.of_nn ((memg' _).1 h1) fun k1 => Stable.of_nn ((memg' _).1 h2) fun k2 => ?_
    rcases k1 with k1 | k1 <;> rcases k2 with k2 | k2
    · exact gmap.2.2 i v v' k1 k2
    · exact (hnn (Stable.of_nn (gmap.1 _ k1) fun ⟨_, _, hi, e'⟩ => (mem_congr_left ((pair_inj k2).1.symm.trans (pair_inj e').1)).2 hi)).elim
    · exact (hnn (Stable.of_nn (gmap.1 _ k2) fun ⟨_, _, hi, e'⟩ => (mem_congr_left ((pair_inj k1).1.symm.trans (pair_inj e').1)).2 hi)).elim
    · exact (pair_inj k1).2.trans (pair_inj k2).2.symm
  · -- the step at position `i`
    refine Stable.of_nn (mem_succ.1 hi) fun
      | .inl hin => ?_
      | .inr ein => ?_
    · have hτ'g : PSet.pair i τ' ∈ pack n e := by
        refine Stable.of_nn (mem_pack.1 hτ') fun ⟨j, hj, e'⟩ => ?_
        have hjn : j < n := by
          have := (mem_congr_left (pair_inj e').1).1 hin
          exact Stable.of_nn (mem_ofNat.1 this) fun ⟨j', hj', e''⟩ => ofNat_inj e'' ▸ hj'
        rw [snoc_lt hjn] at e'
        exact mem_pack.2 (nn_intro ⟨j, hjn, e'⟩)
      have hsg : PSet.pair i s ∈ g := by
        refine Stable.of_nn ((memg' _).1 hs) fun
          | .inl h => h
          | .inr e' => (hnn ((mem_congr_left (pair_inj e').1).1 (mem_succ_of_mem hin))).elim
      have hs'g : PSet.pair (succ i) s' ∈ g := by
        refine Stable.of_nn ((memg' _).1 hs') fun
          | .inl h => h
          | .inr e' => ?_
        exact (not_mem_self (ofNat n) ((mem_congr_left (succ_inj (pair_inj e').1)).1 hin)).elim
      exact gst i hin τ' hτ'g s s' hsg hs'g
    · have eτ : τ' ≈ τ := by
        refine Stable.of_nn (mem_pack.1 hτ') fun ⟨j, hj, e'⟩ => ?_
        have ⟨ej, eτ'⟩ := pair_inj e'
        have : j = n := ofNat_inj (ej.symm.trans ein)
        subst this
        rw [snoc_eq] at eτ'
        exact eτ'
      have es : s ≈ S₁ := by
        refine Stable.of_nn ((memg' _).1 hs) fun
          | .inl h => gmap.2.2 _ s S₁ h ((mem_congr_left (pair_congr ein.symm (Equiv.refl _))).1 gn)
          | .inr e' => (hnn ((mem_congr_left (pair_inj e').1).1 (mem_succ_of_equiv ein))).elim
      have es' : s' ≈ S₂ := by
        refine Stable.of_nn ((memg' _).1 hs') fun
          | .inl h => ?_
          | .inr e' => (pair_inj e').2
        exact (hnn (Stable.of_nn (gmap.1 _ h) fun ⟨_, _, hi', e'⟩ =>
          (mem_congr_left ((succ_congr ein).symm.trans (pair_inj e').1)).2 hi')).elim
      exact hst.congr eτ.symm es.symm es'.symm

end SynZF

/-! ### Steps on packed stacks -/

theorem step_ord {M : PSet.{u} → Prop} {τ : PSet.{u}} (hτ : ¬ τ ∈ ofNat 9) (m : Nat) (vs : Nat → PSet.{u}) :
    Step M τ (pack m vs) (pack (m+1) (snoc m vs τ)) :=
  nn_intro ⟨9, by decide, hτ, push_pack m vs τ⟩

theorem step_empty {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 6) (pack m vs) (pack (m+1) (snoc m vs empty)) :=
  nn_intro ⟨6, by decide, Equiv.refl _, nn_intro ⟨empty, Equiv.refl _, push_pack m vs empty⟩⟩

theorem step_fls {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 2) (pack m vs) (pack (m+1) (snoc m vs (pair (ofNat 2) empty))) :=
  nn_intro ⟨2, by decide, Equiv.refl _, nn_intro ⟨_, Equiv.refl _, push_pack m vs _⟩⟩

theorem step_succ {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 7) (pack (m+1) vs) (pack (m+1) (snoc m vs (succ (vs m)))) :=
  nn_intro ⟨7, by decide, Equiv.refl _, nn_intro ⟨vs m, pack m vs, pop_pack m vs, nn_intro ⟨_, Equiv.refl _, push_pack m vs _⟩⟩⟩

theorem step_all {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 4) (pack (m+1) vs) (pack (m+1) (snoc m vs (pair (ofNat 4) (vs m)))) :=
  nn_intro ⟨4, by decide, Equiv.refl _, nn_intro ⟨vs m, pack m vs, pop_pack m vs, nn_intro ⟨_, Equiv.refl _, push_pack m vs _⟩⟩⟩

theorem caseBin_pack (t m : Nat) (vs : Nat → PSet.{u}) :
    CaseBin t (pack (m+2) vs) (pack (m+1) (snoc m vs (pair (ofNat t) (pair (vs m) (vs (m+1)))))) :=
  nn_intro ⟨vs (m+1), pack (m+1) vs, pop_pack (m+1) vs, nn_intro ⟨vs m, pack m vs, pop_pack m vs,
    nn_intro ⟨_, Equiv.refl _, push_pack m vs _⟩⟩⟩

theorem step_mem {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 0) (pack (m+2) vs) (pack (m+1) (snoc m vs (pair (ofNat 0) (pair (vs m) (vs (m+1)))))) :=
  nn_intro ⟨0, by decide, Equiv.refl _, caseBin_pack 0 m vs⟩

theorem step_eq {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 1) (pack (m+2) vs) (pack (m+1) (snoc m vs (pair (ofNat 1) (pair (vs m) (vs (m+1)))))) :=
  nn_intro ⟨1, by decide, Equiv.refl _, caseBin_pack 1 m vs⟩

theorem step_imp {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) :
    Step M (ofNat 3) (pack (m+2) vs) (pack (m+1) (snoc m vs (pair (ofNat 3) (pair (vs m) (vs (m+1)))))) :=
  nn_intro ⟨3, by decide, Equiv.refl _, caseBin_pack 3 m vs⟩

/-- Cons: the value below, the package on top. -/
theorem step_cons {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) {t : PSet.{u}} (ht : IsCons t (vs m) (vs (m+1))) :
    Step M (ofNat 8) (pack (m+2) vs) (pack (m+1) (snoc m vs t)) :=
  nn_intro ⟨8, by decide, Equiv.refl _, nn_intro ⟨vs (m+1), pack (m+1) vs, pop_pack (m+1) vs, nn_intro ⟨vs m, pack m vs, pop_pack m vs,
    nn_intro ⟨t, ht, push_pack m vs t⟩⟩⟩⟩

/-- Definition: the package below, the code above it, the stage on top. -/
theorem step_def {M : PSet.{u} → Prop} (m : Nat) (vs : Nat → PSet.{u}) {A : PSet.{u}} (hA : OrdLevel M (vs (m+2)) A) :
    Step M (ofNat 5) (pack (m+3) vs) (pack (m+1) (snoc m vs (SynZF.valueOf (M := M) setSatF A (vs (m+1)) (vs m)))) :=
  nn_intro ⟨5, by decide, Equiv.refl _, nn_intro ⟨vs (m+2), pack (m+2) vs, pop_pack (m+2) vs, nn_intro ⟨vs (m+1), pack (m+1) vs,
    pop_pack (m+1) vs, nn_intro ⟨vs m, pack m vs, pop_pack m vs, nn_intro ⟨A, hA, nn_intro ⟨_, Equiv.refl _, push_pack m vs _⟩⟩⟩⟩⟩⟩

/-! ### Native programs and their runs -/

/-- Concatenation of native words: the second word is appended token by token. -/
def cat (n₁ : Nat) (e₁ : Nat → PSet.{u}) : Nat → (Nat → PSet.{u}) → Nat → PSet.{u}
  | 0, _ => e₁
  | n₂+1, e₂ => snoc (n₁ + n₂) (cat n₁ e₁ n₂ e₂) (e₂ n₂)

theorem cat_lt (n₁ : Nat) (e₁ : Nat → PSet.{u}) : ∀ (n₂ : Nat) (e₂ : Nat → PSet.{u}) (i : Nat), i < n₁ → cat n₁ e₁ n₂ e₂ i = e₁ i
  | 0, _, _, _ => rfl
  | n₂+1, e₂, i, hi => by
    show snoc (n₁ + n₂) (cat n₁ e₁ n₂ e₂) (e₂ n₂) i = e₁ i
    rw [snoc_lt (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))]
    exact cat_lt n₁ e₁ n₂ e₂ i hi

theorem cat_zero (e₁ : Nat → PSet.{u}) : ∀ (n₂ : Nat) (e₂ : Nat → PSet.{u}) (i : Nat), i < n₂ → cat 0 e₁ n₂ e₂ i = e₂ i
  | 0, _, i, hi => (Nat.not_lt_zero i hi).elim
  | n₂+1, e₂, i, hi => by
    show snoc (0 + n₂) (cat 0 e₁ n₂ e₂) (e₂ n₂) i = e₂ i
    rw [Nat.zero_add]
    rcases Nat.lt_or_ge i n₂ with h | h
    · rw [snoc_lt h]; exact cat_zero e₁ n₂ e₂ i h
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h
      rw [snoc_eq]

theorem snoc_at {m : Nat} {vs : Nat → PSet.{u}} {v : PSet.{u}} {i : Nat} (h : i = m) : snoc m vs v i = v := by
  subst h; exact snoc_eq

theorem snoc_ext {m : Nat} {vs vs' : Nat → PSet.{u}} {v : PSet.{u}} (h : ∀ i, vs i = vs' i) (i : Nat) : snoc m vs v i = snoc m vs' v i := by
  show (if i < m then vs i else v) = (if i < m then vs' i else v)
  rw [h i]

theorem cat_congr (k : Nat) (f : Nat → PSet.{u}) : ∀ (n : Nat) (e e' : Nat → PSet.{u}), (∀ i, i < n → e i = e' i) →
    ∀ i, cat k f n e i = cat k f n e' i
  | 0, _, _, _, _ => rfl
  | n+1, e, e', h, i => by
    show snoc (k + n) (cat k f n e) (e n) i = snoc (k + n) (cat k f n e') (e' n) i
    rw [h n (Nat.lt_succ_self n)]
    exact snoc_ext (cat_congr k f n e e' fun i hi => h i (Nat.lt_succ_of_lt hi)) i

theorem cat_assoc (k n₁ : Nat) (f e₁ : Nat → PSet.{u}) : ∀ (n₂ : Nat) (e₂ : Nat → PSet.{u}) (i : Nat),
    cat (k + n₁) (cat k f n₁ e₁) n₂ e₂ i = cat k f (n₁ + n₂) (cat n₁ e₁ n₂ e₂) i
  | 0, _, _ => rfl
  | n₂+1, e₂, i => by
    show snoc (k + n₁ + n₂) (cat (k + n₁) (cat k f n₁ e₁) n₂ e₂) (e₂ n₂) i =
      snoc (k + (n₁ + n₂)) (cat k f (n₁ + n₂) (snoc (n₁ + n₂) (cat n₁ e₁ n₂ e₂) (e₂ n₂)))
        (snoc (n₁ + n₂) (cat n₁ e₁ n₂ e₂) (e₂ n₂) (n₁ + n₂)) i
    rw [snoc_eq, Nat.add_assoc]
    refine snoc_ext (fun j => ?_) i
    rw [cat_assoc k n₁ f e₁ n₂ e₂ j]
    exact cat_congr k f (n₁ + n₂) _ _ (fun i hi => (snoc_lt hi).symm) j

/-- **Program extension**: appending `e` (of length `n`) to any run ending in `S` yields a run
ending in `S'`. -/
def Ext (M : PSet.{u} → Prop) (n : Nat) (e : Nat → PSet.{u}) (S S' : PSet.{u}) : Prop :=
  ∀ (k : Nat) (f : Nat → PSet.{u}) (S₀ : PSet.{u}), Run M (pack k f) (ofNat k) S₀ S →
    Run M (pack (k + n) (cat k f n e)) (ofNat (k + n)) S₀ S'

theorem Run.congr_word {M : PSet.{u} → Prop} {n : Nat} {e e' : Nat → PSet.{u}} {S₀ S : PSet.{u}} (h : ∀ i, i < n → e i = e' i)
    (hr : Run M (pack n e) (ofNat n) S₀ S) : Run M (pack n e') (ofNat n) S₀ S :=
  hr.congr (pack_congr fun i hi => h i hi ▸ Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)

theorem Ext.append {M : PSet.{u} → Prop} {n₁ n₂ : Nat} {e₁ e₂ : Nat → PSet.{u}} {S S' S'' : PSet.{u}}
    (h₁ : Ext M n₁ e₁ S S') (h₂ : Ext M n₂ e₂ S' S'') : Ext M (n₁ + n₂) (cat n₁ e₁ n₂ e₂) S S'' := by
  intro k f S₀ hr
  have := h₂ (k + n₁) (cat k f n₁ e₁) S₀ (h₁ k f S₀ hr)
  rw [Nat.add_assoc] at this
  exact this.congr_word fun i _ => cat_assoc k n₁ f e₁ n₂ e₂ i

theorem SynZF.ext_tok {M : PSet.{u} → Prop} (hM : SynZF M) {τ S S' : PSet.{u}} (hS' : M S') (hst : Step M τ S S') :
    Ext M 1 (fun _ => τ) S S' := fun _ _ _ hr => hM.run_snoc hS' hr hst

/-- The extension property yields the denotation. -/
theorem SynZF.den_of_ext {M : PSet.{u} → Prop} (hM : SynZF M) {n : Nat} {e : Nat → PSet.{u}} {y : PSet.{u}}
    (h : Ext M n e (pack 0 (fun _ => PSet.empty)) (pack 1 (snoc 0 (fun _ => PSet.empty) y))) : Den M (pack n e) (ofNat n) y := by
  have hr := h 0 (fun _ => PSet.empty) PSet.empty (hM.run_zero hM.empty)
  rw [Nat.zero_add] at hr
  exact nn_intro ⟨_, hr.congr_word (fun i hi => cat_zero _ n e i hi), top_pack 0 _⟩


/-! ### Coverage -/

/-- A native program: a length and a token word. -/
structure Prog where
  len : Nat
  tok : Nat → PSet.{u}

namespace Prog

def tok1 (τ : PSet.{u}) : Prog := ⟨1, fun _ => τ⟩

def cat (p q : Prog.{u}) : Prog := ⟨p.len + q.len, PSet.cat p.len p.tok q.len q.tok⟩

/-- `[6, 7, …, 7]`: push the numeral `k`. -/
def pushNat : Nat → Prog.{u}
  | 0 => tok1 (ofNat 6)
  | k+1 => (pushNat k).cat (tok1 (ofNat 7))

/-- The postfix program building the code of a formula. -/
def code : Fml → Prog.{u}
  | .mem i j => ((pushNat i).cat (pushNat j)).cat (tok1 (ofNat 0))
  | .eq i j => ((pushNat i).cat (pushNat j)).cat (tok1 (ofNat 1))
  | .fls => tok1 (ofNat 2)
  | .imp φ ψ => ((code φ).cat (code ψ)).cat (tok1 (ofNat 3))
  | .all φ => (code φ).cat (tok1 (ofNat 4))

/-- The package builder: the parameter programs, `∅`, and `n` conses. -/
def pkg : Nat → (Nat → Prog.{u}) → Prog.{u}
  | 0, _ => tok1 (ofNat 6)
  | n+1, prs => (prs 0).cat ((pkg n fun i => prs (i+1)).cat (tok1 (ofNat 8)))

end Prog

/-- The tokens of a program are ordinals of the class. -/
def Toks (M : PSet.{u} → Prop) (p : Prog.{u}) : Prop := ∀ i, i < p.len → IsOrd (p.tok i) ∧ M (p.tok i)

/-- `p` pushes `v` onto any packed stack of the class. -/
def Pushes (M : PSet.{u} → Prop) (p : Prog.{u}) (v : PSet.{u}) : Prop :=
  ∀ (m : Nat) (vs : Nat → PSet.{u}), (∀ i, i < m → M (vs i)) → Ext M p.len p.tok (pack m vs) (pack (m+1) (snoc m vs v))

theorem Ext.congr_right {M : PSet.{u} → Prop} {n : Nat} {e : Nat → PSet.{u}} {S S' S'' : PSet.{u}} (es : S' ≈ S'')
    (h : Ext M n e S S') : Ext M n e S S'' := fun k f S₀ hr => (h k f S₀ hr).congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) es

theorem Pushes.congr {M : PSet.{u} → Prop} {p : Prog.{u}} {v v' : PSet.{u}} (e : v ≈ v') (h : Pushes M p v) : Pushes M p v' :=
  fun m vs hvs => (h m vs hvs).congr_right (pack_congr fun i hi => by
    rcases Nat.lt_or_ge i m with h' | h'
    · rw [snoc_lt h', snoc_lt h']; exact Equiv.refl _
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
      rw [snoc_eq, snoc_eq]; exact e)

theorem toks_cat {M : PSet.{u} → Prop} {n₁ : Nat} {e₁ : Nat → PSet.{u}} (h₁ : ∀ i, i < n₁ → IsOrd (e₁ i) ∧ M (e₁ i)) :
    ∀ (n₂ : Nat) (e₂ : Nat → PSet.{u}), (∀ i, i < n₂ → IsOrd (e₂ i) ∧ M (e₂ i)) →
      ∀ i, i < n₁ + n₂ → IsOrd (PSet.cat n₁ e₁ n₂ e₂ i) ∧ M (PSet.cat n₁ e₁ n₂ e₂ i)
  | 0, _, _, i, hi => h₁ i hi
  | n₂+1, e₂, h₂, i, hi => by
    show IsOrd (snoc (n₁ + n₂) (PSet.cat n₁ e₁ n₂ e₂) (e₂ n₂) i) ∧ M (snoc (n₁ + n₂) (PSet.cat n₁ e₁ n₂ e₂) (e₂ n₂) i)
    rcases Nat.lt_or_ge i (n₁ + n₂) with h | h
    · rw [snoc_lt h]; exact toks_cat h₁ n₂ e₂ (fun i hi => h₂ i (Nat.lt_succ_of_lt hi)) i h
    · have e : i = n₁ + n₂ := Nat.le_antisymm (Nat.le_of_lt_succ hi) h
      rw [snoc_at e]; exact h₂ n₂ (Nat.lt_succ_self n₂)

theorem Toks.cat {M : PSet.{u} → Prop} {p q : Prog.{u}} (hp : Toks M p) (hq : Toks M q) : Toks M (p.cat q) :=
  toks_cat hp q.len q.tok hq

theorem Toks.tok1 {M : PSet.{u} → Prop} {τ : PSet.{u}} (ho : IsOrd τ) (hτ : M τ) : Toks M (Prog.tok1 τ) := fun _ _ => ⟨ho, hτ⟩

theorem snoc_vals {M : PSet.{u} → Prop} {m : Nat} {vs : Nat → PSet.{u}} {v : PSet.{u}} (hvs : ∀ i, i < m → M (vs i)) (hv : M v) :
    ∀ i, i < m + 1 → M (snoc m vs v i) := fun i hi => by
  rcases Nat.lt_or_ge i m with h | h
  · rw [snoc_lt h]; exact hvs i h
  · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h
    rw [snoc_eq]; exact hv

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- A single token that pushes `v` from any packed stack. -/
theorem pushes_tok {τ v : PSet.{u}} (hv : M v)
    (hst : ∀ (m : Nat) (vs : Nat → PSet.{u}), Step M τ (pack m vs) (pack (m+1) (snoc m vs v))) : Pushes M (Prog.tok1 τ) v :=
  fun m vs hvs => hM.ext_tok (hM.pack_mem' (snoc_vals hvs hv)) (hst m vs)

/-- A unary opcode after one push: the pushed value is `g` of the popped value. -/
theorem pushes_un {p : Prog.{u}} {v : PSet.{u}} {τ : PSet.{u}} {g : PSet.{u} → PSet.{u}} (hv : M v) (hw : M (g v)) (hp : Pushes M p v)
    (hst : ∀ (m : Nat) (vs : Nat → PSet.{u}), Step M τ (pack (m+1) vs) (pack (m+1) (snoc m vs (g (vs m))))) :
    Pushes M (p.cat (Prog.tok1 τ)) (g v) := by
  intro m vs hvs
  refine Ext.append (n₂ := 1) (e₂ := fun _ => τ) (hp m vs hvs) ?_
  have hw' : M (g (snoc m vs v m)) := by rw [snoc_eq]; exact hw
  have := hM.ext_tok (hM.pack_mem' (snoc_vals (fun i hi => snoc_vals hvs hv i (Nat.lt_succ_of_lt hi)) hw')) (hst m (snoc m vs v))
  refine this.congr_right (pack_congr fun i hi => ?_)
  rcases Nat.lt_or_ge i m with h | h
  · rw [snoc_lt h, snoc_lt h, snoc_lt h]; exact Equiv.refl _
  · rw [snoc_at (Nat.le_antisymm (Nat.le_of_lt_succ hi) h), snoc_at (Nat.le_antisymm (Nat.le_of_lt_succ hi) h), snoc_eq]
    exact Equiv.refl _

theorem pushes_nat : ∀ k : Nat, Pushes M (Prog.pushNat k) (ofNat k)
  | 0 => hM.pushes_tok hM.empty fun m vs => step_empty m vs
  | k+1 => hM.pushes_un (g := succ) (hM.trans hM.omega (ofNat_mem_omega k)) (hM.trans hM.omega (ofNat_mem_omega (k+1)))
      (pushes_nat k) fun m vs => step_succ m vs

end SynZF


namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem toks_nat : ∀ k : Nat, Toks M (Prog.pushNat k)
  | 0 => Toks.tok1 (isOrd_ofNat 6) (hM.trans hM.omega (ofNat_mem_omega 6))
  | k+1 => (toks_nat k).cat (Toks.tok1 (isOrd_ofNat 7) (hM.trans hM.omega (ofNat_mem_omega 7)))

theorem toks_code : ∀ φ : Fml, Toks M (Prog.code φ)
  | .mem i j => ((hM.toks_nat i).cat (hM.toks_nat j)).cat (Toks.tok1 (isOrd_ofNat 0) (hM.trans hM.omega (ofNat_mem_omega 0)))
  | .eq i j => ((hM.toks_nat i).cat (hM.toks_nat j)).cat (Toks.tok1 (isOrd_ofNat 1) (hM.trans hM.omega (ofNat_mem_omega 1)))
  | .fls => Toks.tok1 (isOrd_ofNat 2) (hM.trans hM.omega (ofNat_mem_omega 2))
  | .imp φ ψ => ((toks_code φ).cat (toks_code ψ)).cat (Toks.tok1 (isOrd_ofNat 3) (hM.trans hM.omega (ofNat_mem_omega 3)))
  | .all φ => (toks_code φ).cat (Toks.tok1 (isOrd_ofNat 4) (hM.trans hM.omega (ofNat_mem_omega 4)))

omit hM in
/-- Push two values in sequence. -/
theorem pushes_cat {p q : Prog.{u}} {v w : PSet.{u}} (hv : M v) (hp : Pushes M p v) (hq : Pushes M q w) (m : Nat) (vs : Nat → PSet.{u})
    (hvs : ∀ i, i < m → M (vs i)) :
    Ext M (p.cat q).len (p.cat q).tok (pack m vs) (pack (m+2) (snoc (m+1) (snoc m vs v) w)) :=
  Ext.append (hp m vs hvs) (hq (m+1) (snoc m vs v) (snoc_vals hvs hv))

/-- A binary opcode after two pushes. -/
theorem pushes_bin {p q : Prog.{u}} {v w : PSet.{u}} (t : Nat) (hv : M v) (hw : M w) (hp : Pushes M p v) (hq : Pushes M q w)
    (hst : ∀ (m : Nat) (vs : Nat → PSet.{u}), Step M (ofNat t) (pack (m+2) vs) (pack (m+1) (snoc m vs (PSet.pair (ofNat t) (PSet.pair (vs m) (vs (m+1))))))) :
    Pushes M ((p.cat q).cat (Prog.tok1 (ofNat t))) (PSet.pair (ofNat t) (PSet.pair v w)) := by
  intro m vs hvs
  refine Ext.append (n₂ := 1) (e₂ := fun _ => ofNat t) (pushes_cat hv hp hq m vs hvs) ?_
  let vs' : Nat → PSet.{u} := snoc (m+1) (snoc m vs v) w
  have hvs' : ∀ i, i < m + 2 → M (vs' i) := snoc_vals (snoc_vals hvs hv) hw
  have hX : M (PSet.pair (ofNat t) (PSet.pair (vs' m) (vs' (m+1)))) :=
    hM.pair (hM.trans hM.omega (ofNat_mem_omega t)) (hM.pair (hvs' m (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_succ _)))
      (hvs' (m+1) (Nat.lt_succ_self _)))
  have hS' : M (pack (m+1) (snoc m vs' (PSet.pair (ofNat t) (PSet.pair (vs' m) (vs' (m+1)))))) :=
    hM.pack_mem' (snoc_vals (fun i hi => hvs' i (Nat.lt_of_lt_of_le hi (Nat.le_add_right m 2))) hX)
  have hext := hM.ext_tok hS' (hst m vs')
  have em : vs' m = v := by show snoc (m+1) (snoc m vs v) w m = v; rw [snoc_lt (Nat.lt_succ_self m), snoc_eq]
  have em1 : vs' (m+1) = w := by show snoc (m+1) (snoc m vs v) w (m+1) = w; rw [snoc_eq]
  refine hext.congr_right (pack_congr fun i hi => ?_)
  rcases Nat.lt_or_ge i m with h | h
  · have e1 : vs' i = vs i := by show snoc (m+1) (snoc m vs v) w i = vs i; rw [snoc_lt (Nat.lt_succ_of_lt h), snoc_lt h]
    rw [snoc_lt h, snoc_lt h, e1]; exact Equiv.refl _
  · have e : i = m := Nat.le_antisymm (Nat.le_of_lt_succ hi) h
    rw [snoc_at e, snoc_at e, em, em1]; exact Equiv.refl _

theorem pushes_code : ∀ φ : Fml, Pushes M (Prog.code φ) (enc φ)
  | .mem i j => hM.pushes_bin 0 (hM.trans hM.omega (ofNat_mem_omega i)) (hM.trans hM.omega (ofNat_mem_omega j))
      (hM.pushes_nat i) (hM.pushes_nat j) step_mem
  | .eq i j => hM.pushes_bin 1 (hM.trans hM.omega (ofNat_mem_omega i)) (hM.trans hM.omega (ofNat_mem_omega j))
      (hM.pushes_nat i) (hM.pushes_nat j) step_eq
  | .fls => hM.pushes_tok (hM.pair (hM.trans hM.omega (ofNat_mem_omega 2)) hM.empty) step_fls
  | .imp φ ψ => hM.pushes_bin 3 (hM.enc_mem φ) (hM.enc_mem ψ) (pushes_code φ) (pushes_code ψ) step_imp
  | .all φ => hM.pushes_un (g := fun x => PSet.pair (ofNat 4) x) (hM.enc_mem φ) (hM.enc_mem (.all φ)) (pushes_code φ)
      fun m vs => step_all m vs

end SynZF

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- Every ordinal of the class is pushed by some program. -/
theorem pushes_ord {β : PSet.{u}} (hβ : IsOrd β) (hβM : M β) : ¬¬∃ p : Prog.{u}, Toks M p ∧ Pushes M p β := by
  refine Stable.by_cases (β ∈ ofNat 9) (fun h => ?_) fun h => ?_
  · refine Stable.of_nn (mem_ofNat.1 h) fun ⟨k, _, ek⟩ => ?_
    exact nn_intro ⟨Prog.pushNat k, hM.toks_nat k, (hM.pushes_nat k).congr ek.symm⟩
  · exact nn_intro ⟨Prog.tok1 β, Toks.tok1 hβ hβM, hM.pushes_tok hβM fun m vs => step_ord h m vs⟩

/-- The package builder pushes the package of the pushed parameters. -/
theorem pushes_pkg : ∀ (n : Nat) (prs : Nat → Prog.{u}) (e : Nat → PSet.{u}),
    (∀ i, i < n → Toks M (prs i) ∧ Pushes M (prs i) (e i) ∧ M (e i)) →
    Toks M (Prog.pkg n prs) ∧ Pushes M (Prog.pkg n prs) (pack n e)
  | 0, _, _, _ => ⟨Toks.tok1 (isOrd_ofNat 6) (hM.trans hM.omega (ofNat_mem_omega 6)), hM.pushes_tok hM.empty fun m vs => step_empty m vs⟩
  | n+1, prs, e, h => by
    have ⟨ht0, hp0, he0⟩ := h 0 (Nat.succ_pos n)
    have ⟨htn, hpn⟩ := pushes_pkg n (fun i => prs (i+1)) (fun i => e (i+1)) fun i hi => h (i+1) (Nat.succ_lt_succ hi)
    have h8 : M (ofNat 8) := hM.trans hM.omega (ofNat_mem_omega 8)
    refine ⟨ht0.cat (htn.cat (Toks.tok1 (isOrd_ofNat 8) h8)), ?_⟩
    intro m vs hvs
    show Ext M ((prs 0).len + ((Prog.pkg n fun i => prs (i+1)).cat (Prog.tok1 (ofNat 8))).len) _ _ _
    refine Ext.append (n₂ := ((Prog.pkg n fun i => prs (i+1)).cat (Prog.tok1 (ofNat 8))).len)
      (e₂ := ((Prog.pkg n fun i => prs (i+1)).cat (Prog.tok1 (ofNat 8))).tok) (hp0 m vs hvs) ?_
    have hP : M (pack n fun i => e (i+1)) := hM.pack_mem n fun i hi => (h (i+1) (Nat.succ_lt_succ hi)).2.2
    refine Ext.append (n₂ := 1) (e₂ := fun _ => ofNat 8) (hpn (m+1) (snoc m vs (e 0)) (snoc_vals hvs he0)) ?_
    let vs' : Nat → PSet.{u} := snoc (m+1) (snoc m vs (e 0)) (pack n fun i => e (i+1))
    have hvs' : ∀ i, i < m + 2 → M (vs' i) := snoc_vals (snoc_vals hvs he0) hP
    have em : vs' m = e 0 := by show snoc (m+1) (snoc m vs (e 0)) _ m = e 0; rw [snoc_lt (Nat.lt_succ_self m), snoc_eq]
    have em1 : vs' (m+1) = pack n fun i => e (i+1) := by show snoc (m+1) (snoc m vs (e 0)) _ (m+1) = _; rw [snoc_eq]
    have hcons : IsCons (pack (n+1) (Env.cons (e 0) fun i => e (i+1))) (vs' m) (vs' (m+1)) := by
      rw [em, em1]; exact isCons_pack n
    have hT : M (pack (n+1) (Env.cons (e 0) fun i => e (i+1))) := hM.pack_mem (n+1) fun i hi => by
      rcases i with _ | i
      · exact he0
      · exact (h (i+1) hi).2.2
    have hS' : M (pack (m+1) (snoc m vs' (pack (n+1) (Env.cons (e 0) fun i => e (i+1))))) :=
      hM.pack_mem' (snoc_vals (fun i hi => hvs' i (Nat.lt_of_lt_of_le hi (Nat.le_add_right m 2))) hT)
    have hext := hM.ext_tok hS' (step_cons m vs' hcons)
    refine hext.congr_right (pack_congr fun i hi => ?_)
    rcases Nat.lt_or_ge i m with h' | h'
    · have e1 : vs' i = vs i := by show snoc (m+1) (snoc m vs (e 0)) _ i = vs i; rw [snoc_lt (Nat.lt_succ_of_lt h'), snoc_lt h']
      rw [snoc_lt h', snoc_lt h', e1]; exact Equiv.refl _
    · have e' : i = m := Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
      rw [snoc_at e', snoc_at e']
      exact pack_congr fun j _ => by
        rcases j with _ | j
        · exact Equiv.refl _
        · exact Equiv.refl _

/-- The definition instruction after the package, the code, and the stage. -/
theorem pushes_def {pk cd st : Prog.{u}} {P q β A : PSet.{u}} (hP : M P) (hq : M q) (hβ : M β) (hA : OrdLevel M β A)
    (hpk : Pushes M pk P) (hcd : Pushes M cd q) (hst : Pushes M st β) :
    Pushes M (((pk.cat cd).cat st).cat (Prog.tok1 (ofNat 5))) (valueOf (M := M) setSatF A q P) := by
  intro m vs hvs
  have hAM := (hM.level_mem_class hA.2).2
  have h1 := Ext.append (n₂ := st.len) (e₂ := st.tok) (pushes_cat hP hpk hcd m vs hvs)
    (hst (m+2) (snoc (m+1) (snoc m vs P) q) (snoc_vals (snoc_vals hvs hP) hq))
  refine Ext.append (n₂ := 1) (e₂ := fun _ => ofNat 5) h1 ?_
  let vs' : Nat → PSet.{u} := snoc (m+2) (snoc (m+1) (snoc m vs P) q) β
  have hvs' : ∀ i, i < m + 3 → M (vs' i) := snoc_vals (snoc_vals (snoc_vals hvs hP) hq) hβ
  have em : vs' m = P := by
    show snoc (m+2) (snoc (m+1) (snoc m vs P) q) β m = P
    rw [snoc_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_succ _)), snoc_lt (Nat.lt_succ_self m), snoc_eq]
  have em1 : vs' (m+1) = q := by show snoc (m+2) (snoc (m+1) (snoc m vs P) q) β (m+1) = q; rw [snoc_lt (Nat.lt_succ_self _), snoc_eq]
  have em2 : vs' (m+2) = β := by show snoc (m+2) (snoc (m+1) (snoc m vs P) q) β (m+2) = β; rw [snoc_eq]
  have hA' : OrdLevel M (vs' (m+2)) A := by rw [em2]; exact hA
  have hY : M (valueOf (M := M) setSatF A (vs' (m+1)) (vs' m)) := by rw [em, em1]; exact hM.valueOf_mem (S := setSatF) hAM hq hP
  have hS' : M (pack (m+1) (snoc m vs' (valueOf (M := M) setSatF A (vs' (m+1)) (vs' m)))) :=
    hM.pack_mem' (snoc_vals (fun i hi => hvs' i (Nat.lt_of_lt_of_le hi (Nat.le_add_right m 3))) hY)
  have hext := hM.ext_tok hS' (step_def m vs' hA')
  refine hext.congr_right (pack_congr fun i hi => ?_)
  rcases Nat.lt_or_ge i m with h' | h'
  · have e1 : vs' i = vs i := by
      show snoc (m+2) (snoc (m+1) (snoc m vs P) q) β i = vs i
      rw [snoc_lt (Nat.lt_of_lt_of_le h' (Nat.le_add_right m 2)), snoc_lt (Nat.lt_succ_of_lt h'), snoc_lt h']
    rw [snoc_lt h', snoc_lt h', e1]; exact Equiv.refl _
  · have e' : i = m := Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
    rw [snoc_at e', snoc_at e', em, em1]; exact Equiv.refl _

omit hM in
/-- Finitely many negatively supplied programs are supplied together. -/
theorem progs_of (e : Nat → PSet.{u}) : ∀ n : Nat, (∀ i, i < n → ¬¬∃ p : Prog.{u}, Toks M p ∧ Pushes M p (e i)) →
    ¬¬∃ prs : Nat → Prog.{u}, ∀ i, i < n → Toks M (prs i) ∧ Pushes M (prs i) (e i)
  | 0, _ => nn_intro ⟨fun _ => Prog.tok1 PSet.empty, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | n+1, h => by
    refine nn_bind (progs_of e n fun i hi => h i (Nat.lt_succ_of_lt hi)) fun ⟨prs, hprs⟩ =>
      nn_map (fun ⟨p, ht, hp⟩ => ⟨fun i => if i < n then prs i else p, fun i hi => ?_⟩) (h n (Nat.lt_succ_self n))
    show Toks M (if i < n then prs i else p) ∧ Pushes M (if i < n then prs i else p) (e i)
    split
    · exact hprs i ‹_›
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) (Nat.le_of_not_lt ‹_›)
      exact ⟨ht, hp⟩

/-- **Coverage**: every member of a level is pushed by a program of the class. -/
theorem coverage : ∀ α : PSet.{u}, IsOrd α → M α → ∀ A, Level M α A → ∀ y, y ∈ A →
    ¬¬∃ p : Prog.{u}, Toks M p ∧ Pushes M p y := by
  refine mem_induction (P := fun α => IsOrd α → M α → ∀ A, Level M α A → ∀ y, y ∈ A → ¬¬∃ p : Prog.{u}, Toks M p ∧ Pushes M p y)
    fun α ih hα hαM A hA y hy => ?_
  refine Stable.of_nn ((hM.level_rec hα hαM hA y).1 hy) fun ⟨γ, hγ, k⟩ => Stable.of_nn k fun ⟨B, hB, hyB⟩ => ?_
  have hγo := hα.mem hγ
  have hγM := hM.trans hαM hγ
  have hBM := (hM.level_mem_class hB).2
  refine Stable.of_nn (mem_defPow.1 hyB) fun ⟨n, φ, e, hb, he, ey⟩ => ?_
  have heM : ∀ i, i < n → M (e i) := fun i hi => hM.trans hBM (he i hi)
  refine Stable.of_nn (progs_of e n fun i hi => ih γ hγ hγo hγM B hB (e i) (he i hi)) fun ⟨prs, hprs⟩ => ?_
  refine Stable.of_nn (hM.pushes_ord hγo hγM) fun ⟨st, hst, hpst⟩ => ?_
  have ⟨hpkT, hpk⟩ := hM.pushes_pkg n prs e fun i hi => ⟨(hprs i hi).1, (hprs i hi).2, heM i hi⟩
  have hP : M (pack n e) := hM.pack_mem n heM
  have hval := hM.pushes_def hP (hM.enc_mem φ) hγM ⟨hγo, hB⟩ hpk (hM.pushes_code φ) hpst
  refine nn_intro ⟨_, ((hpkT.cat (hM.toks_code φ)).cat hst).cat (Toks.tok1 (isOrd_ofNat 5) (hM.trans hM.omega (ofNat_mem_omega 5))),
    hval.congr ?_⟩
  exact (hM.valueOf_pack hBM hb he).trans ey.symm

omit hM in
theorem isOWord_pack {n : Nat} {e : Nat → PSet.{u}} (h : ∀ i, i < n → IsOrd (e i)) : IsOWord (pack n e) (ofNat n) :=
  ⟨ofNat_mem_omega n, isMap_pack n e, fun _ _ hv => Stable.of_nn (mem_pack.1 hv) fun ⟨j, hj, e'⟩ =>
    (h j hj).resp (pair_inj e').2.symm⟩

/-- **Every constructible set of the class is the denotation of a program of the class.** -/
theorem program_of_constr {y : PSet.{u}} (hy : Constr M y) :
    ¬¬∃ (n : Nat) (e : Nat → PSet.{u}), M (pack n e) ∧ IsOWord (pack n e) (ofNat n) ∧ Den M (pack n e) (ofNat n) y := by
  refine Stable.of_nn hy fun ⟨α, A, hα, hA, hyA⟩ => ?_
  refine nn_map (fun ⟨p, ht, hp⟩ => ⟨p.len, p.tok, hM.pack_mem p.len fun i hi => (ht i hi).2, isOWord_pack fun i hi => (ht i hi).1, ?_⟩)
    (hM.coverage α hα (hM.level_mem_class hA).1 A hA y hyA)
  exact hM.den_of_ext (hp 0 (fun _ => PSet.empty) fun i hi => (Nat.not_lt_zero i hi).elim)

end SynZF

/-- info: 'PSet.SynZF.program_of_constr' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.program_of_constr
/-- info: 'PSet.SynZF.Den.unique' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.Den.unique
/-- info: 'PSet.SynZF.sat_denF' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.sat_denF

end PSet
