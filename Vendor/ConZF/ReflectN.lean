import Vendor.ConZF.Reflection
import Vendor.ConZF.Assign
import Vendor.ConZF.ConstrAx
/-!
The semantic half of the reflection compiler for the constructible class `N := Constr M`, with
`ell := constrF` and `level := ordLevelF`. Bounded capture for one request (`capture_bound`),
existence and uniqueness of the next good stage (`next_exists`, `NextStage.unique`), the ω-history
through the internal ω-recursion with a harmless default on non-ordinals (`stepN`), the supremum
of the history as a nonzero limit with the sequence cofinal in it, the finite fit of parameter
tuples into one sequence level, reflection at the supremum (`reflect_at_sup`), Separation in `N`
(`sepN`), and the assembly `SynZF (Constr M)`. Only `SynZF M` is assumed throughout.
-/
universe u

namespace PSet
open Fml CardF LF Reflection RecF AssignF CodeF

/-! ### Environments with a finite prefix -/

namespace Env

/-- The environment with the first `n` entries from `e'` and the rest from `E`. -/
def pre : Nat → (Nat → PSet.{u}) → (Nat → PSet.{u}) → Nat → PSet.{u}
  | 0, _, E => E
  | n+1, e', E => cons (e' 0) (pre n (fun i => e' (i+1)) E)

theorem pre_lt : ∀ {n : Nat} {e' E : Nat → PSet.{u}} {i : Nat}, i < n → pre n e' E i = e' i
  | 0, _, _, _, h => (Nat.not_lt_zero _ h).elim
  | _+1, _, _, 0, _ => rfl
  | n+1, e', E, _+1, h => pre_lt (n := n) (e' := fun i => e' (i+1)) (E := E) (Nat.lt_of_succ_lt_succ h)

theorem pre_ge : ∀ {n : Nat} {e' E : Nat → PSet.{u}} (j : Nat), pre n e' E (j + n) = E j
  | 0, _, _, _ => rfl
  | n+1, e', E, j => pre_ge (n := n) (e' := fun i => e' (i+1)) (E := E) j

theorem pre_cons : ∀ {n : Nat} {e : Nat → PSet.{u}} {E : Nat → PSet.{u}} (i : Nat),
    pre n e (cons (e n) E) i = pre (n+1) e E i
  | 0, _, _, _ => rfl
  | _+1, _, _, 0 => rfl
  | n+1, e, E, i+1 => pre_cons (n := n) (e := fun i => e (i+1)) (E := E) i

theorem pre_congr : ∀ {n : Nat} {e e' E : Nat → PSet.{u}}, (∀ i, i < n → e i ≈ e' i) →
    ∀ i, pre n e E i ≈ pre n e' E i
  | 0, _, _, _, _, _ => Equiv.refl _
  | _+1, _, _, _, h, 0 => h 0 (Nat.succ_pos _)
  | n+1, e, e', E, h, i+1 =>
    pre_congr (n := n) (e := fun i => e (i+1)) (e' := fun i => e' (i+1)) (E := E)
      (fun i hi => h (i+1) (Nat.succ_lt_succ hi)) i

theorem pre_mem {M : PSet.{u} → Prop} : ∀ {n : Nat} {e' E : Nat → PSet.{u}}, (∀ i, i < n → M (e' i)) →
    (∀ i, M (E i)) → ∀ i, M (pre n e' E i)
  | 0, _, _, _, hE, i => hE i
  | _+1, _, _, he, _, 0 => he 0 (Nat.succ_pos _)
  | n+1, e', _, he, hE, i+1 =>
    pre_mem (n := n) (e' := fun i => e' (i+1)) (fun i hi => he (i+1) (Nat.succ_lt_succ hi)) hE i

end Env

namespace Reflection
variable {M : PSet.{u} → Prop}

/-- Iterated universals read as quantification over a finite prefix of the environment. -/
theorem sat_allN_pre : ∀ {n : Nat} {p : Fml} {E : Nat → PSet.{u}},
    Sat M (allN n p) E ↔ ∀ e', (∀ i, i < n → M (e' i)) → Sat M p (Env.pre n e' E)
  | 0, p, E => ⟨fun h e' _ => h, fun h => h (fun _ => empty) fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | n+1, p, E => by
    show Sat M (all (allN n p)) E ↔ _
    constructor
    · intro h e'' he''
      have := (sat_allN_pre (n := n)).1 (h (e'' n) (he'' n (Nat.lt_succ_self n))) e''
        fun i hi => he'' i (Nat.lt_succ_of_lt hi)
      exact (Sat.resp_iff (fun _ => Iff.rfl) p fun i => (Env.pre_cons i) ▸ Equiv.refl _).1 this
    · intro h x hx
      refine (sat_allN_pre (n := n)).2 fun e' he' => ?_
      let e'' : Nat → PSet.{u} := fun i => if i < n then e' i else x
      have he'' : ∀ i, i < n+1 → M (e'' i) := fun i _ => by
        show M (if i < n then e' i else x)
        split
        · exact he' i ‹_›
        · exact hx
      have h1 := h e'' he''
      have h2 : ∀ i, Env.pre n e'' (Env.cons (e'' n) E) i ≈ Env.pre n e' (Env.cons x E) i := by
        intro i
        have hx' : e'' n = x := by
          show (if n < n then e' n else x) = x
          split
          · exact (Nat.lt_irrefl n ‹_›).elim
          · rfl
        rw [hx']
        exact Env.pre_congr (fun i hi => by
          show (if i < n then e' i else x) ≈ e' i
          split
          · exact Equiv.refl _
          · exact (‹¬ i < n› hi).elim) i
      exact (Sat.resp_iff (fun _ => Iff.rfl) p h2).1
        ((Sat.resp_iff (fun _ => Iff.rfl) p fun i => (Env.pre_cons i).symm ▸ Equiv.refl _).1 h1)

/-- Iterated existentials. -/
def exN : Nat → Fml → Fml
  | 0, p => p
  | n+1, p => ex (exN n p)

theorem sat_exN_pre : ∀ {n : Nat} {p : Fml} {E : Nat → PSet.{u}},
    Sat M (exN n p) E ↔ ¬¬∃ e', (∀ i, i < n → M (e' i)) ∧ Sat M p (Env.pre n e' E)
  | 0, p, E => ⟨fun h => nn_intro ⟨fun _ => empty, fun _ hi => (Nat.not_lt_zero _ hi).elim, h⟩,
      fun h => Stable.of_nn h fun ⟨_, _, hs⟩ => hs⟩
  | n+1, p, E => by
    show Sat M (ex (exN n p)) E ↔ _
    refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨x, hx, hs⟩ => nn_map (fun ⟨e', he', hs⟩ => ?_)
      ((sat_exN_pre (n := n)).1 hs), fun h => nn_map (fun ⟨e'', he'', hs⟩ => ?_) h⟩
    · let e'' : Nat → PSet.{u} := fun i => if i < n then e' i else x
      refine ⟨e'', fun i _ => ?_, ?_⟩
      · show M (if i < n then e' i else x)
        split
        · exact he' i ‹_›
        · exact hx
      · have hx' : e'' n = x := by
          show (if n < n then e' n else x) = x
          split
          · exact (Nat.lt_irrefl n ‹_›).elim
          · rfl
        have h2 : ∀ i, Env.pre n e' (Env.cons x E) i ≈ Env.pre n e'' (Env.cons (e'' n) E) i := by
          intro i
          rw [hx']
          exact Env.pre_congr (fun i hi => by
            show e' i ≈ (if i < n then e' i else x)
            split
            · exact Equiv.refl _
            · exact (‹¬ i < n› hi).elim) i
        exact (Sat.resp_iff (fun _ => Iff.rfl) p fun i => (Env.pre_cons i) ▸ Equiv.refl _).1
          ((Sat.resp_iff (fun _ => Iff.rfl) p h2).1 hs)
    · refine ⟨e'' n, he'' n (Nat.lt_succ_self n), (sat_exN_pre (n := n)).2 (nn_intro ⟨e'', fun i hi => he'' i (Nat.lt_succ_of_lt hi), ?_⟩)⟩
      exact (Sat.resp_iff (fun _ => Iff.rfl) p fun i => (Env.pre_cons i).symm ▸ Equiv.refl _).1 hs

end Reflection

/-! ### Reading parameters from a package -/

namespace LF

/-- `⟨ī, v_i⟩ ∈ p` for `i < k`, with `v_i` at index `i` and the package at index `p`. -/
def readsF (p : Nat) : Nat → Fml
  | 0 => trueF
  | k+1 => and (ex (and (numF k 0) (pairMemF (p+1) 0 (k+1)))) (readsF p k)

/-- `body(z, v₀, …, v_{n-1})` with the `v_i` read from the package at index `p` and the witness at
index `z`; under the `n` binders `z, p` sit at `z + n, p + n`. -/
def withPackF (n : Nat) (body : Fml) (z p : Nat) : Fml :=
  exN n (and (readsF (p+n) n) (rename (fun k => if k = 0 then z + n else k - 1) body))

/-- `∃ C, ordLevelF μ C ∧ ∃ z ∈ C, N z ∧ body^N(z, reads p)`; indices `p, μ` given. -/
def witAtF (n : Nat) (body : Fml) (p μ : Nat) : Fml :=
  ex (and (at2 ordLevelF (μ+1) 0) (ex (and (mem 0 1) (and constrF
    (withPackF n (restrictClass constrF body) 0 (p+2))))))

/-- `μ` is the least stage with a witness for the request at the package `p`. Variables `p = 0`,
`μ = 1`. -/
def leastWitF (n : Nat) (body : Fml) : Fml :=
  and (witAtF n body 0 1) (all (imp (mem 0 2) (neg (witAtF n body 1 0))))

end LF

instance {e : PSet.{u}} {i : Nat} {v : PSet.{u}} : Stable (Reads e i v) := inferInstanceAs (Stable (_ ∈ _))

/-- The ambient reading of `witAtF` at an arbitrary package `P`. -/
def WitAtP (M : PSet.{u} → Prop) (n : Nat) (body : Fml) (P μ : PSet.{u}) : Prop :=
  ¬¬∃ C, OrdLevel M μ C ∧ ¬¬∃ z, z ∈ C ∧ Constr M z ∧
    ¬¬∃ e' : Nat → PSet.{u}, (∀ i, i < n → M (e' i)) ∧ (∀ i, i < n → Reads P i (e' i)) ∧
      Sat (Constr M) body (Env.cons z e')

/-- The reading at the package of a native environment. -/
def WitAt (M : PSet.{u} → Prop) (body : Fml) (e : Nat → PSet.{u}) (μ : PSet.{u}) : Prop :=
  ¬¬∃ C, OrdLevel M μ C ∧ ¬¬∃ z, z ∈ C ∧ Constr M z ∧ Sat (Constr M) body (Env.cons z e)

instance {M : PSet.{u} → Prop} {n body P μ} : Stable (WitAtP M n body P μ) := inferInstanceAs (Stable (¬_))
instance {M : PSet.{u} → Prop} {body e μ} : Stable (WitAt M body e μ) := inferInstanceAs (Stable (¬_))

theorem WitAt.congr {M : PSet.{u} → Prop} {body : Fml} {e : Nat → PSet.{u}} {μ μ' : PSet.{u}} (h : μ ≈ μ')
    (w : WitAt M body e μ) : WitAt M body e μ' :=
  nn_map (fun ⟨C, ⟨ho, hC⟩, k⟩ => ⟨C, ⟨ho.resp h, SynZF.level_congr h hC⟩, k⟩) w

theorem WitAt.isOrd {M : PSet.{u} → Prop} {body : Fml} {e : Nat → PSet.{u}} {μ : PSet.{u}} (w : WitAt M body e μ) : IsOrd μ :=
  Stable.of_nn w fun ⟨_, ho, _⟩ => ho.1

theorem WitAtP.isOrd {M : PSet.{u} → Prop} {n : Nat} {body : Fml} {P μ : PSet.{u}} (w : WitAtP M n body P μ) : IsOrd μ :=
  Stable.of_nn w fun ⟨_, ho, _⟩ => ho.1

/-- Least stages for a fixed package. -/
def LeastWitP (M : PSet.{u} → Prop) (n : Nat) (body : Fml) (P μ : PSet.{u}) : Prop :=
  WitAtP M n body P μ ∧ ∀ ν, ν ∈ μ → ¬ WitAtP M n body P ν

theorem LeastWitP.unique {M : PSet.{u} → Prop} {n : Nat} {body : Fml} {P μ μ' : PSet.{u}}
    (h : LeastWitP M n body P μ) (h' : LeastWitP M n body P μ') : μ ≈ μ' :=
  Stable.of_nn (h.1.isOrd.trichotomy h'.1.isOrd) fun
    | .inl k => (h'.2 μ k h.1).elim
    | .inr (.inl e) => e
    | .inr (.inr k) => (h.2 μ' k h'.1).elim

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem sat_readsF {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (p k : Nat) :
    Sat M (readsF p k) E ↔ ∀ i, i < k → Reads (E p) i (E i) := by
  have hT := hM.toTransClass
  induction k with
  | zero => exact ⟨fun _ i hi => (Nat.not_lt_zero _ hi).elim, fun _ => sat_trueF⟩
  | succ k ih =>
    refine sat_and.trans ⟨fun ⟨h1, h2⟩ i hi => ?_, fun h => ⟨?_, ih.2 fun i hi => h i (Nat.lt_succ_of_lt hi)⟩⟩
    · rcases Nat.lt_or_ge i k with h' | h'
      · exact ih.1 h2 i h'
      · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
        refine Stable.of_nn (sat_ex.1 h1) fun ⟨w, hw, hs⟩ => ?_
        have ⟨hn, hp⟩ := sat_and.1 hs
        have hE' := Env.cons_mem hw hE
        have ew := (hT.sat_numF hE' hM.empty hM.succ_mem k 0).1 hn
        exact (mem_congr_left (pair_congr ew (Equiv.refl _))).1 ((hT.sat_pairMemF hE' (p+1) 0 (k+1)).1 hp)
    · have hw : M (ofNat k) := TransClass.ofNat_mem hM.empty hM.succ_mem k
      have hE' := Env.cons_mem hw hE
      exact sat_ex.2 (nn_intro ⟨ofNat k, hw, sat_and.2 ⟨(hT.sat_numF hE' hM.empty hM.succ_mem k 0).2 (Equiv.refl _),
        (hT.sat_pairMemF hE' (p+1) 0 (k+1)).2 (h k (Nat.lt_succ_self k))⟩⟩)

/-- **The package bridge**: the reads determine the first `n` entries. -/
theorem sat_withPackF {n : Nat} {body : Fml} (hb : Bound (n+1) body) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (z p : Nat) :
    Sat M (withPackF n body z p) E ↔
      ¬¬∃ e' : Nat → PSet.{u}, (∀ i, i < n → M (e' i)) ∧ (∀ i, i < n → Reads (E p) i (e' i)) ∧ Sat M body (Env.cons (E z) e') := by
  refine sat_exN_pre.trans (nn_congr (exists_congr fun e' => and_congr_right fun he' => ?_))
  have hE' : ∀ i, M (Env.pre n e' E i) := Env.pre_mem he' hE
  refine sat_and.trans (and_congr ?_ ?_)
  · refine (hM.sat_readsF hE' (p+n) n).trans (forall_congr' fun i => imp_congr_right fun hi => ?_)
    rw [Env.pre_ge, Env.pre_lt hi]
  · refine (sat_rename _ _ _).trans (sat_bound hb fun i hi => ?_)
    rcases i with _ | i
    · show Env.pre n e' E (z + n) ≈ E z
      rw [Env.pre_ge]; exact Equiv.refl _
    · show Env.pre n e' E i ≈ e' i
      rw [Env.pre_lt (Nat.lt_of_succ_lt_succ hi)]; exact Equiv.refl _

theorem sat_witAtF {n : Nat} {body : Fml} (hb : Bound (n+1) body) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) (p μ : Nat) :
    Sat M (witAtF n body p μ) E ↔ WitAtP M n body (E p) (E μ) := by
  refine sat_ex.trans (nn_congr ⟨fun ⟨C, hC, hs⟩ => ?_, fun ⟨C, hoC, k⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    have hE1 := Env.cons_mem hC hE
    have h1' := (sat_at2 (e' := E) bound_ordLevelF).1 h1
    refine ⟨C, (hM.sat_ordLevelF (hE μ) hC hE).1 h1', ?_⟩
    refine nn_map (fun ⟨z, hz, hs⟩ => ?_) (sat_ex.1 h2)
    have ⟨h3, h4⟩ := sat_and.1 hs
    have ⟨h5, h6⟩ := sat_and.1 h4
    have hE2 := Env.cons_mem hz hE1
    have h5' := (hM.sat_constrF hz hE1).1 h5
    have h6' := (hM.sat_withPackF (bound_restrictClass bound_constrF hb) hE2 0 (p+2)).1 h6
    refine ⟨z, h3, h5', ?_⟩
    exact nn_map (fun ⟨e', he', hr, hs⟩ => ⟨e', he', hr, (hM.sat_constr_iff body _).2 hs⟩) h6'
  · have hC := (hM.level_mem_class hoC.2).2
    have hE1 := Env.cons_mem hC hE
    have h1' := (hM.sat_ordLevelF (hE μ) hC hE).2 hoC
    have h1 := (sat_at2 (e := Env.cons C E) (i := μ+1) (j := 0) (e' := E) bound_ordLevelF).2 h1'
    refine ⟨C, hC, sat_and.2 ⟨h1, ?_⟩⟩
    refine sat_ex.2 (nn_map (fun ⟨z, hz, hcz, k⟩ => ?_) k)
    have hzM := hM.trans hC hz
    have hE2 := Env.cons_mem hzM hE1
    have h5 := (hM.sat_constrF hzM hE1).2 hcz
    have h6 := (hM.sat_withPackF (bound_restrictClass bound_constrF hb) hE2 0 (p+2)).2
      (nn_map (fun ⟨e', he', hr, hs⟩ => ⟨e', he', hr, (hM.sat_constr_iff body _).1 hs⟩) k)
    exact ⟨z, hzM, sat_and.2 ⟨hz, sat_and.2 ⟨h5, h6⟩⟩⟩

theorem sat_leastWitF {n : Nat} {body : Fml} (hb : Bound (n+1) body) {P μ : PSet.{u}} {E : Nat → PSet.{u}}
    (hP : M P) (hμ : M μ) (hE : ∀ i, M (E i)) :
    Sat M (leastWitF n body) (Env.cons P (Env.cons μ E)) ↔ LeastWitP M n body P μ := by
  have hE1 := Env.cons_mem hP (Env.cons_mem hμ hE)
  refine sat_and.trans (and_congr (hM.sat_witAtF hb hE1 0 1) ⟨fun h ν hν k => ?_, fun h ν _ hν k => ?_⟩)
  · exact h ν (hM.trans hμ hν) hν ((hM.sat_witAtF hb (Env.cons_mem (hM.trans hμ hν) hE1) 1 0).2 k)
  · exact h ν hν ((hM.sat_witAtF hb (Env.cons_mem (hM.trans hμ hν) hE1) 1 0).1 k)

omit hM in
/-- At a package of a native environment, the reading is the reading at that environment. -/
theorem witAtP_pack {n : Nat} {body : Fml} (hb : Bound (n+1) body) {e : Nat → PSet.{u}} (he : ∀ i, i < n → M (e i)) {μ : PSet.{u}} :
    WitAtP M n body (pack n e) μ ↔ WitAt M body e μ := by
  refine nn_congr (exists_congr fun C => and_congr_right fun _ => nn_congr (exists_congr fun z =>
    and_congr_right fun _ => and_congr_right fun _ => ⟨fun k => Stable.of_nn k fun ⟨e', _, hr, hs⟩ => ?_, fun hs => ?_⟩))
  · refine (sat_bound hb fun i hi => ?_).1 hs
    rcases i with _ | i
    · exact Equiv.refl _
    · exact (reads_pack (Nat.lt_of_succ_lt_succ hi)).1 (hr i (Nat.lt_of_succ_lt_succ hi))
  · exact nn_intro ⟨e, he, fun i hi => (reads_pack hi).2 (Equiv.refl _), hs⟩

end SynZF

/-! ### Capture, good stages, and the next stage -/

theorem mem_map_elim {α β : Type} {f : α → β} : ∀ {l : List α} {q : β}, q ∈ l.map f → ∃ a, a ∈ l ∧ f a = q
  | [], _, h => nomatch h
  | a :: l, q, h => by
    cases h with
    | head => exact ⟨a, .head _, rfl⟩
    | tail _ h => have ⟨a', h1, h2⟩ := mem_map_elim (l := l) h; exact ⟨a', .tail _ h1, h2⟩

theorem mem_map_intro {α β : Type} {f : α → β} : ∀ {l : List α} {a : α}, a ∈ l → f a ∈ l.map f
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ h => .tail _ (mem_map_intro h)

theorem mem_append_left {α : Type} {a : α} : ∀ {s : List α} (t : List α), a ∈ s → a ∈ s ++ t
  | _ :: _, _, .head _ => .head _
  | _ :: _, t, .tail _ h => .tail _ (mem_append_left t h)

theorem mem_append_right {α : Type} {a : α} : ∀ (s : List α) {t : List α}, a ∈ t → a ∈ s ++ t
  | [], _, h => h
  | _ :: s, _, h => .tail _ (mem_append_right s h)

theorem Reflection.mem_matrices {p : Fml} {m : Matrix} : ∀ {Δ : List Fml}, p ∈ Δ → m ∈ requests p → m ∈ matrices Δ
  | _ :: Δ, .head _, hm => mem_append_left (matrices Δ) hm
  | q :: _, .tail _ hp, hm => mem_append_right (requests q) (mem_matrices hp hm)

/-- **Capture** of a request between two sets: parameters in `A` with a constructible witness in
the class have a constructible witness in `B`. -/
def Captures (M : PSet.{u} → Prop) (m : Matrix) (A B : PSet.{u}) : Prop :=
  ∀ e : Nat → PSet.{u}, (∀ i, i < m.arity → M (e i)) → (∀ i, i < m.arity → e i ∈ A) →
    (¬¬∃ z, Constr M z ∧ Sat (Constr M) m.body (Env.cons z e)) →
    ¬¬∃ z, z ∈ B ∧ Constr M z ∧ Sat (Constr M) m.body (Env.cons z e)

/-- Capture with the witnesses in the level at `β`. -/
def CapturesAt (M : PSet.{u} → Prop) (m : Matrix) (A β : PSet.{u}) : Prop :=
  ∀ e : Nat → PSet.{u}, (∀ i, i < m.arity → M (e i)) → (∀ i, i < m.arity → e i ∈ A) →
    (¬¬∃ z, Constr M z ∧ Sat (Constr M) m.body (Env.cons z e)) →
    ¬¬∃ z, InLevel M z β ∧ Constr M z ∧ Sat (Constr M) m.body (Env.cons z e)

/-- A good pair of stages: `α ∈ β` ordinals whose levels capture every request of `Δ`. -/
def GoodStage (M : PSet.{u} → Prop) (Δ : List Fml) (α β : PSet.{u}) : Prop :=
  IsOrd α ∧ IsOrd β ∧ α ∈ β ∧ ¬¬∃ A B, SynZF.Level M α A ∧ SynZF.Level M β B ∧ ∀ m, m ∈ matrices Δ → Captures M m A B

instance {M : PSet.{u} → Prop} {Δ α β} : Stable (GoodStage M Δ α β) := inferInstanceAs (Stable (_ ∧ _ ∧ _ ∧ ¬_))

theorem GoodStage.congr_right {M : PSet.{u} → Prop} {Δ : List Fml} {α β β' : PSet.{u}} (e : β ≈ β') (h : GoodStage M Δ α β) : GoodStage M Δ α β' :=
  ⟨h.1, h.2.1.resp e, (mem_congr_right e).1 h.2.2.1,
    nn_map (fun ⟨A, B, hA, hB, hc⟩ => ⟨A, B, hA, SynZF.level_congr e hB, hc⟩) h.2.2.2⟩

/-- The least good stage above `α`. -/
def NextStage (M : PSet.{u} → Prop) (Δ : List Fml) (α β : PSet.{u}) : Prop :=
  GoodStage M Δ α β ∧ ∀ γ, γ ∈ β → ¬ GoodStage M Δ α γ

instance {M : PSet.{u} → Prop} {Δ α β} : Stable (NextStage M Δ α β) := inferInstanceAs (Stable (_ ∧ _))

theorem NextStage.lt {M : PSet.{u} → Prop} {Δ : List Fml} {α β : PSet.{u}} (h : NextStage M Δ α β) : α ∈ β := h.1.2.2.1
theorem NextStage.isOrd {M : PSet.{u} → Prop} {Δ : List Fml} {α β : PSet.{u}} (h : NextStage M Δ α β) : IsOrd β := h.1.2.1

theorem NextStage.unique {M : PSet.{u} → Prop} {Δ : List Fml} {α β β' : PSet.{u}} (h : NextStage M Δ α β) (h' : NextStage M Δ α β') : β ≈ β' :=
  Stable.of_nn (h.isOrd.trichotomy h'.isOrd) fun
    | .inl k => (h'.2 β k h.1).elim
    | .inr (.inl e) => e
    | .inr (.inr k) => (h.2 β' k h'.1).elim

theorem IsOrd.union {a b : PSet.{u}} (ha : IsOrd a) (hb : IsOrd b) : IsOrd (union a b) :=
  ⟨fun y hy z hz => Stable.of_nn (mem_union.1 hy) fun
      | .inl h => mem_union.2 (nn_intro (.inl (ha.trans y h z hz)))
      | .inr h => mem_union.2 (nn_intro (.inr (hb.trans y h z hz))),
   fun y hy => Stable.of_nn (mem_union.1 hy) fun
      | .inl h => ha.mem_trans y h
      | .inr h => hb.mem_trans y h⟩

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- **The capture bridge.** -/
theorem sat_capture {m : Matrix} (hm : Bound (m.arity + 1) m.body) {A B : PSet.{u}} {E : Nat → PSet.{u}} :
    Sat M (capture constrF m) (Env.cons A (Env.cons B E)) ↔ Captures M m A B := by
  refine sat_allN_pre.trans (forall_congr' fun e' => imp_congr_right fun he' => ?_)
  have hA : Env.pre m.arity e' (Env.cons A (Env.cons B E)) m.arity = A := by
    have := Env.pre_ge (n := m.arity) (e' := e') (E := Env.cons A (Env.cons B E)) 0
    rwa [Nat.zero_add] at this
  have hB : Env.pre m.arity e' (Env.cons A (Env.cons B E)) (m.arity + 1) = B := by
    have := Env.pre_ge (n := m.arity) (e' := e') (E := Env.cons A (Env.cons B E)) 1
    rwa [Nat.add_comm] at this
  have key : ∀ z, Sat (definedClass M constrF) m.body (Env.cons z (Env.pre m.arity e' (Env.cons A (Env.cons B E)))) ↔
      Sat (Constr M) m.body (Env.cons z e') := fun z =>
    (Sat.resp_iff (fun x => (hM.constr_iff_definedClass x).symm) m.body fun _ => Equiv.refl _).trans
      (sat_bound hm fun i hi => by
        rcases i with _ | i
        · exact Equiv.refl _
        · show Env.pre m.arity e' _ i ≈ e' i
          rw [Env.pre_lt (Nat.lt_of_succ_lt_succ hi)]; exact Equiv.refl _)
  refine (sat_capture_body bound_constrF).trans ?_
  rw [hA, hB]
  refine imp_congr (forall_congr' fun i => imp_congr_right fun hi => by rw [Env.pre_lt hi]) (imp_congr ?_ ?_)
  · exact nn_congr (exists_congr fun z => and_congr (hM.constr_iff_definedClass z).symm (key z))
  · exact nn_congr (exists_congr fun z => and_congr_right fun _ => and_congr (hM.constr_iff_definedClass z).symm (key z))

theorem sat_closes (Δ : List Fml) {A B : PSet.{u}} {E : Nat → PSet.{u}} :
    Sat M (closes constrF Δ) (Env.cons A (Env.cons B E)) ↔ ∀ m, m ∈ matrices Δ → Captures M m A B := by
  refine sat_conjoin.trans ⟨fun h m hm => ?_, fun h q hq => ?_⟩
  · exact (hM.sat_capture (matrices_valid Δ m hm)).1 (h _ (mem_map_intro hm))
  · have ⟨m, hm, e⟩ := mem_map_elim hq
    exact e ▸ (hM.sat_capture (matrices_valid Δ m hm)).2 (h m hm)

/-- **The good-stage bridge.** -/
theorem sat_goodF (Δ : List Fml) {α β : PSet.{u}} {E : Nat → PSet.{u}} (hα : M α) (hβ : M β) (hE : ∀ i, M (E i)) :
    Sat M (goodF constrF ordLevelF Δ) (Env.cons α (Env.cons β E)) ↔ GoodStage M Δ α β := by
  have hT := hM.toTransClass
  have hE1 : ∀ i, M (Env.cons α (Env.cons β E) i) := Env.cons_mem hα (Env.cons_mem hβ hE)
  have split : Sat M (goodF constrF ordLevelF Δ) (Env.cons α (Env.cons β E)) ↔
      IsOrd α ∧ IsOrd β ∧ α ∈ β ∧ Sat M (ex (ex (conjoin [at2 ordLevelF 2 1, at2 ordLevelF 3 0, at2 (closes constrF Δ) 1 0])))
        (Env.cons α (Env.cons β E)) :=
    sat_and.trans (and_congr (hT.sat_ordF hE1 0) (sat_and.trans (and_congr (hT.sat_ordF hE1 1)
      (sat_and.trans (and_congr Iff.rfl (sat_and.trans ⟨fun h => h.1, fun h => ⟨h, sat_trueF⟩⟩))))))
  refine split.trans ⟨fun ⟨h1, h2, h3, h⟩ => ⟨h1, h2, h3, ?_⟩, fun ⟨h1, h2, h3, h⟩ => ⟨h1, h2, h3, ?_⟩⟩
  · refine nn_bind (sat_ex.1 h) fun ⟨A', hA', hs⟩ => nn_map (fun ⟨B', hB', hs⟩ => ?_) (sat_ex.1 hs)
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h3, h4⟩ := sat_and.1 h2
    have ⟨h5, _⟩ := sat_and.1 h4
    have h1' := (sat_at2 (e := Env.cons B' (Env.cons A' (Env.cons α (Env.cons β E)))) (i := 2) (j := 1) (e' := E) bound_ordLevelF).1 h1
    have h3' := (sat_at2 (e := Env.cons B' (Env.cons A' (Env.cons α (Env.cons β E)))) (i := 3) (j := 0) (e' := E) bound_ordLevelF).1 h3
    have h5' := (sat_at2 (e := Env.cons B' (Env.cons A' (Env.cons α (Env.cons β E)))) (i := 1) (j := 0) (e' := E) (bound_closes bound_constrF Δ)).1 h5
    exact ⟨A', B', ((hM.sat_ordLevelF hα hA' hE).1 h1').2, ((hM.sat_ordLevelF hβ hB' hE).1 h3').2, (hM.sat_closes Δ).1 h5'⟩
  · refine sat_ex.2 (nn_map (fun ⟨A', B', hA', hB', hc⟩ => ?_) h)
    have hA'M := (hM.level_mem_class hA').2
    have hB'M := (hM.level_mem_class hB').2
    have k1 := (sat_at2 (e := Env.cons B' (Env.cons A' (Env.cons α (Env.cons β E)))) (i := 2) (j := 1) (e' := E) bound_ordLevelF).2
      ((hM.sat_ordLevelF hα hA'M hE).2 ⟨h1, hA'⟩)
    have k3 := (sat_at2 (e := Env.cons B' (Env.cons A' (Env.cons α (Env.cons β E)))) (i := 3) (j := 0) (e' := E) bound_ordLevelF).2
      ((hM.sat_ordLevelF hβ hB'M hE).2 ⟨h2, hB'⟩)
    have k5 := (sat_at2 (e := Env.cons B' (Env.cons A' (Env.cons α (Env.cons β E)))) (i := 1) (j := 0) (e' := E)
      (bound_closes bound_constrF Δ)).2 ((hM.sat_closes Δ).2 hc)
    exact ⟨A', hA'M, sat_ex.2 (nn_intro ⟨B', hB'M, sat_and.2 ⟨k1, sat_and.2 ⟨k3, sat_and.2 ⟨k5, sat_trueF⟩⟩⟩⟩)⟩

/-- **The next-stage bridge.** -/
theorem sat_nextF (Δ : List Fml) {α β : PSet.{u}} {E : Nat → PSet.{u}} (hα : M α) (hβ : M β) (hE : ∀ i, M (E i)) :
    Sat M (nextF constrF ordLevelF Δ) (Env.cons α (Env.cons β E)) ↔ NextStage M Δ α β := by
  refine sat_and.trans (and_congr (hM.sat_goodF Δ hα hβ hE) ⟨fun h γ hγ k => ?_, fun h γ hγM hγ k => ?_⟩)
  · have hγM := hM.trans hβ hγ
    refine h γ hγM hγ ((sat_at2 (e := Env.cons γ (Env.cons α (Env.cons β E))) (i := 1) (j := 0) (e' := E)
      (bound_goodF bound_constrF bound_ordLevelF Δ)).2 ((hM.sat_goodF Δ hα hγM hE).2 k))
  · exact h γ hγ ((hM.sat_goodF Δ hα hγM hE).1 ((sat_at2 (e := Env.cons γ (Env.cons α (Env.cons β E))) (i := 1) (j := 0) (e' := E)
      (bound_goodF bound_constrF bound_ordLevelF Δ)).1 k))

/-! ### Bounded capture -/

/-- Membership in a level is monotone along inclusion of ordinals. -/
theorem inLevel_mono {z β β' : PSet.{u}} (hβ' : IsOrd β') (hβ'M : M β') (hsub : ∀ x, x ∈ β → x ∈ β') (h : InLevel M z β) :
    InLevel M z β' := by
  refine Stable.of_nn h fun ⟨B, ⟨hβ, hB⟩, hz⟩ => nn_map (fun ⟨B', _, hB'⟩ => ⟨B', ⟨hβ', hB'⟩, ?_⟩) (hM.level_exists hβ' hβ'M)
  refine Stable.of_nn (mem_succ.1 (hβ.mem_succ_of_subset hβ' hsub)) fun
    | .inl k => hM.level_mono hβ' hβ'M k hB' hB z hz
    | .inr e => (mem_congr_right (level_unique hβ' (level_congr e hB) hB')).1 hz

theorem capturesAt_mono {m : Matrix} {A β β' : PSet.{u}} (hβ' : IsOrd β') (hβ'M : M β') (hsub : ∀ x, x ∈ β → x ∈ β')
    (h : CapturesAt M m A β) : CapturesAt M m A β' := fun e he heA hact =>
  nn_map (fun ⟨z, hz, hcz, hs⟩ => ⟨z, hM.inLevel_mono hβ' hβ'M hsub hz, hcz, hs⟩) (h e he heA hact)

theorem captures_of_at {m : Matrix} {A β β' B' : PSet.{u}} (hβ' : IsOrd β') (hβ'M : M β') (hsub : ∀ x, x ∈ β → x ∈ β')
    (hB' : Level M β' B') (h : CapturesAt M m A β) : Captures M m A B' := fun e he heA hact =>
  nn_bind (h e he heA hact) fun ⟨z, hz, hcz, hs⟩ =>
    nn_map (fun ⟨_, ⟨_, hB''⟩, hzB⟩ => ⟨z, (mem_congr_right (level_unique hβ' hB'' hB')).1 hzB, hcz, hs⟩)
      (hM.inLevel_mono hβ' hβ'M hsub hz)

/-- A least witness stage exists for every active parameter tuple. -/
theorem leastWit_exists {body : Fml} {e : Nat → PSet.{u}}
    (hact : ¬¬∃ z, Constr M z ∧ Sat (Constr M) body (Env.cons z e)) :
    ¬¬∃ μ, M μ ∧ WitAt M body e μ ∧ ∀ ν, ν ∈ μ → ¬ WitAt M body e ν := by
  refine Stable.of_nn hact fun ⟨z, hcz, hs⟩ => Stable.of_nn hcz fun ⟨α', C, hα', hC, hz⟩ => ?_
  have hα'M := (hM.level_mem_class hC).1
  let S := PSet.sep (fun δ => WitAt M body e δ) (succ α')
  have hS : ∀ δ, δ ∈ S ↔ δ ∈ succ α' ∧ WitAt M body e δ := fun δ => mem_sep fun _ _ e k => k.congr e
  have hαS : α' ∈ S := (hS α').2 ⟨self_mem_succ α', nn_intro ⟨C, ⟨hα', hC⟩, nn_intro ⟨z, hz, hcz, hs⟩⟩⟩
  refine nn_map (fun ⟨μ, hμS, hmin⟩ => ?_) (exists_minimal S α' hαS)
  have ⟨hμs, hμ⟩ := (hS μ).1 hμS
  exact ⟨μ, hM.trans (hM.succ_mem hα'M) hμs, hμ, fun ν hν k => hmin ν hν ((hS ν).2 ⟨hα'.succ.trans μ hμs ν hν, k⟩)⟩

/-- **Bounded capture for one request**: some stage captures the request for all parameter
tuples from `A`. -/
theorem capture_bound {m : Matrix} (hm : Bound (m.arity + 1) m.body) {A : PSet.{u}} (hA : M A) :
    ¬¬∃ β, M β ∧ IsOrd β ∧ CapturesAt M m A β := by
  refine nn_bind (hM.assignSet_exists hA) fun ⟨V, hV, hVs⟩ => ?_
  have he : ∀ i, M (Env.cons V envω i) := Env.cons_mem hV hM.envω_mem
  have hf : ∀ P μ μ', P ∈ Env.cons V envω 0 → M μ → M μ' →
      Sat M (leastWitF m.arity m.body) (Env.cons P (Env.cons μ (Env.cons V envω))) →
      Sat M (leastWitF m.arity m.body) (Env.cons P (Env.cons μ' (Env.cons V envω))) → μ ≈ μ' :=
    fun P μ μ' hP hμ hμ' h1 h2 =>
      LeastWitP.unique ((hM.sat_leastWitF hm (hM.trans hV hP) hμ he).1 h1) ((hM.sat_leastWitF hm (hM.trans hV hP) hμ' he).1 h2)
  refine nn_bind (hM.replM (leastWitF m.arity m.body) he hf) fun ⟨b, hb, hcol⟩ => ?_
  have he' : ∀ i, M (Env.cons b envω i) := Env.cons_mem hb hM.envω_mem
  let S := PSet.sep (fun z => Sat M (ordF 0) (Env.cons z (Env.cons b envω))) b
  have hSM : M S := hM.sepM (ordF 0) he'
  have hS : ∀ z, z ∈ S ↔ z ∈ b ∧ IsOrd z := fun z =>
    (mem_sep fun _ _ e k => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k).trans
      (and_congr_right fun hz => hM.toTransClass.sat_ordF (Env.cons_mem (hM.trans hb hz) he') 0)
  have hU : IsOrd (PSet.sUnion S) := isOrd_sUnion fun γ hγ => ((hS γ).1 hγ).2
  have hUM : M (succ (PSet.sUnion S)) := hM.succ_mem (hM.sUnion hSM)
  refine nn_intro ⟨succ (PSet.sUnion S), hUM, hU.succ, fun e heM heA hact => ?_⟩
  refine Stable.of_nn (hM.leastWit_exists hact) fun ⟨μ, hμM, hw, hmin⟩ => ?_
  have hPM : M (pack m.arity e) := hM.pack_mem m.arity heM
  have hPV : pack m.arity e ∈ V := (hVs _).2 ⟨hPM, nn_intro ⟨ofNat m.arity, isAssign_pack m.arity heA⟩⟩
  have hsat : Sat M (leastWitF m.arity m.body) (Env.cons (pack m.arity e) (Env.cons μ (Env.cons V envω))) :=
    (hM.sat_leastWitF hm hPM hμM he).2 ⟨(witAtP_pack hm heM).2 hw, fun ν hν k => hmin ν hν ((witAtP_pack hm heM).1 k)⟩
  have hμb : μ ∈ b := hcol _ μ hPV hμM hsat
  have hμS : μ ∈ S := (hS μ).2 ⟨hμb, hw.isOrd⟩
  have hμU : μ ∈ succ (PSet.sUnion S) :=
    hw.isOrd.mem_succ_of_subset hU fun z hz => mem_sUnion.2 (nn_intro ⟨μ, hμS, hz⟩)
  refine Stable.of_nn hw fun ⟨C, ⟨_, hC⟩, k⟩ => Stable.of_nn k fun ⟨z, hz, hcz, hs⟩ => ?_
  refine nn_map (fun ⟨B, _, hB⟩ => ⟨z, nn_intro ⟨B, ⟨hU.succ, hB⟩, hM.level_mono hU.succ hUM hμU hB hC z hz⟩, hcz, hs⟩)
    (hM.level_exists hU.succ hUM)

/-- Bounded capture for a finite list of requests. -/
theorem captures_list {A : PSet.{u}} (hA : M A) (l : List Matrix) (hl : ∀ m, m ∈ l → Bound (m.arity + 1) m.body) :
    ¬¬∃ β, M β ∧ IsOrd β ∧ ∀ m, m ∈ l → CapturesAt M m A β := by
  induction l with
  | nil => exact nn_intro ⟨PSet.empty, hM.empty, isOrd_empty, fun _ h => nomatch h⟩
  | cons m l ih =>
    refine nn_bind (hM.capture_bound (hl m (.head _)) hA) fun ⟨β₁, hβ₁M, hβ₁, hc₁⟩ => ?_
    refine nn_map (fun ⟨β₂, hβ₂M, hβ₂, hc₂⟩ => ?_) (ih fun m' hm' => hl m' (.tail _ hm'))
    have hβ := hβ₁.union hβ₂
    have hβM := hM.union hβ₁M hβ₂M
    refine ⟨PSet.union β₁ β₂, hβM, hβ, fun m' hm' => ?_⟩
    cases hm' with
    | head => exact hM.capturesAt_mono hβ hβM (fun x hx => mem_union.2 (nn_intro (.inl hx))) hc₁
    | tail _ h => exact hM.capturesAt_mono hβ hβM (fun x hx => mem_union.2 (nn_intro (.inr hx))) (hc₂ m' h)

/-- **Existence of the next stage.** -/
theorem next_exists (Δ : List Fml) {α : PSet.{u}} (hα : IsOrd α) (hαM : M α) : ¬¬∃ β, M β ∧ NextStage M Δ α β := by
  refine nn_bind (hM.level_exists hα hαM) fun ⟨A, hAM, hA⟩ => ?_
  refine nn_bind (hM.captures_list hAM (matrices Δ) (matrices_valid Δ)) fun ⟨β₁, hβ₁M, hβ₁, hc⟩ => ?_
  have hu := hα.union hβ₁
  have huM := hM.union hαM hβ₁M
  have hβ₀ := hu.succ
  have hβ₀M := hM.succ_mem huM
  have hαβ₀ : α ∈ succ (PSet.union α β₁) := hα.mem_succ_of_subset hu fun x hx => mem_union.2 (nn_intro (.inl hx))
  have hβ₁β₀ : ∀ x, x ∈ β₁ → x ∈ succ (PSet.union α β₁) := fun x hx =>
    hβ₀.trans _ (hβ₁.mem_succ_of_subset hu fun y hy => mem_union.2 (nn_intro (.inr hy))) x hx
  have good₀ : GoodStage M Δ α (succ (PSet.union α β₁)) :=
    ⟨hα, hβ₀, hαβ₀, nn_map (fun ⟨B₀, _, hB₀⟩ => ⟨A, B₀, hA, hB₀, fun m hm =>
      hM.captures_of_at hβ₀ hβ₀M hβ₁β₀ hB₀ (hc m hm)⟩) (hM.level_exists hβ₀ hβ₀M)⟩
  let S := PSet.sep (fun γ => GoodStage M Δ α γ) (succ (succ (PSet.union α β₁)))
  have hS : ∀ γ, γ ∈ S ↔ γ ∈ succ (succ (PSet.union α β₁)) ∧ GoodStage M Δ α γ := fun γ =>
    mem_sep fun _ _ e k => k.congr_right e
  refine nn_map (fun ⟨γ, hγS, hmin⟩ => ?_) (exists_minimal S _ ((hS _).2 ⟨self_mem_succ _, good₀⟩))
  have ⟨hγs, hγ⟩ := (hS γ).1 hγS
  exact ⟨γ, hM.trans (hM.succ_mem hβ₀M) hγs, hγ, fun δ hδ k => hmin δ hδ ((hS δ).2 ⟨hβ₀.succ.trans γ hγs δ hδ, k⟩)⟩

end SynZF

/-! ### The ω-history of next stages -/

namespace LF

/-- The totalized step: `Ord x ∧ nextF x y`, or `¬ Ord x ∧ y = x`. Input `0`, output `1`. -/
def stepN (Δ : List Fml) : Fml :=
  or (and (ordF 0) (at2 (nextF constrF ordLevelF Δ) 0 1)) (and (neg (ordF 0)) (eq 1 0))

/-- The history: the ω-sequence of the totalized step. Variables `0` the history, `1` the start,
`2` `ω`. -/
def histF (Δ : List Fml) : Fml := seqF (stepN Δ)

end LF

/-- The ambient reading of the step. -/
def StepN (M : PSet.{u} → Prop) (Δ : List Fml) (x y : PSet.{u}) : Prop :=
  ¬¬((IsOrd x ∧ NextStage M Δ x y) ∨ (¬ IsOrd x ∧ y ≈ x))

/-- `s` is the history of `Δ` from `lam`. -/
def HistN (M : PSet.{u} → Prop) (Δ : List Fml) (lam s : PSet.{u}) : Prop :=
  Sat M (histF Δ) (Env.cons s (Env.cons lam (Env.cons PSet.omega envω)))

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem sat_stepN (Δ : List Fml) {x y : PSet.{u}} {E : Nat → PSet.{u}} (hx : M x) (hy : M y) (hE : ∀ i, M (E i)) :
    Sat M (stepN Δ) (Env.cons x (Env.cons y E)) ↔ StepN M Δ x y := by
  have hE1 : ∀ i, M (Env.cons x (Env.cons y E) i) := Env.cons_mem hx (Env.cons_mem hy hE)
  have hn : Sat M (at2 (nextF constrF ordLevelF Δ) 0 1) (Env.cons x (Env.cons y E)) ↔ NextStage M Δ x y :=
    (sat_at2 (e := Env.cons x (Env.cons y E)) (i := 0) (j := 1) (e' := E) (bound_nextF bound_constrF bound_ordLevelF Δ)).trans
      (hM.sat_nextF Δ hx hy hE)
  exact sat_or.trans (nn_congr (or_congr (sat_and.trans (and_congr (hM.toTransClass.sat_ordF hE1 0) hn))
    (sat_and.trans (and_congr (not_congr (hM.toTransClass.sat_ordF hE1 0)) Iff.rfl))))

theorem stepN_fun (Δ : List Fml) : ∀ x y y', M x → M y → M y' → Sat M (stepN Δ) (Env.cons x (Env.cons y envω)) →
    Sat M (stepN Δ) (Env.cons x (Env.cons y' envω)) → y ≈ y' := by
  intro x y y' hx hy hy' h1 h2
  have k1 := (hM.sat_stepN Δ hx hy hM.envω_mem).1 h1
  have k2 := (hM.sat_stepN Δ hx hy' hM.envω_mem).1 h2
  refine Stable.of_nn k1 fun
    | .inl ⟨ho, hn⟩ => Stable.of_nn k2 fun
      | .inl ⟨_, hn'⟩ => hn.unique hn'
      | .inr ⟨ho', _⟩ => (ho' ho).elim
    | .inr ⟨ho, e⟩ => Stable.of_nn k2 fun
      | .inl ⟨ho', _⟩ => (ho ho').elim
      | .inr ⟨_, e'⟩ => e.trans e'.symm

theorem stepN_tot (Δ : List Fml) : ∀ x, M x → ¬¬∃ y, M y ∧ Sat M (stepN Δ) (Env.cons x (Env.cons y envω)) := by
  intro x hx
  refine Stable.by_cases (IsOrd x) (fun ho => ?_) fun ho => ?_
  · exact nn_map (fun ⟨y, hy, hn⟩ => ⟨y, hy, (hM.sat_stepN Δ hx hy hM.envω_mem).2 (nn_intro (.inl ⟨ho, hn⟩))⟩)
      (hM.next_exists Δ ho hx)
  · exact nn_intro ⟨x, hx, (hM.sat_stepN Δ hx hx hM.envω_mem).2 (nn_intro (.inr ⟨ho, Equiv.refl _⟩))⟩

/-- **Existence of the history.** -/
theorem hist_exists (Δ : List Fml) {lam : PSet.{u}} (hlam : M lam) : ¬¬∃ s, M s ∧ HistN M Δ lam s :=
  hM.seq_exists (stepN Δ) hM.envω_mem (hM.stepN_fun Δ) hlam

/-- **Uniqueness of the history.** -/
theorem hist_unique (Δ : List Fml) {lam s s' : PSet.{u}} (hlam : M lam) (hs : M s) (hs' : M s')
    (h : HistN M Δ lam s) (h' : HistN M Δ lam s') : s ≈ s' :=
  hM.seq_unique (stepN Δ) hM.envω_mem hlam hs hs' h h'

/-- The recursion equations of the history: a pure graph on `ω`, functional, total, starting at
`lam`, with consecutive rows related by the step. -/
theorem hist_spec (Δ : List Fml) {lam s : PSet.{u}} (hlam : M lam) (hs : M s) (h : HistN M Δ lam s) :
    (∀ q, q ∈ s → ¬¬∃ n v, n ∈ PSet.omega ∧ q ≈ PSet.pair n v) ∧
    PSet.pair PSet.empty lam ∈ s ∧
    (∀ n v v', PSet.pair n v ∈ s → PSet.pair n v' ∈ s → v ≈ v') ∧
    (∀ n, n ∈ PSet.omega → ¬¬∃ v, PSet.pair n v ∈ s) ∧
    (∀ n v w, PSet.pair n v ∈ s → PSet.pair (succ n) w ∈ s → StepN M Δ v w) := by
  have k := hM.seq_spec (stepN Δ) hM.envω_mem (hM.stepN_fun Δ) (hM.stepN_tot Δ) hlam hs h
  refine ⟨k.1, k.2.1, k.2.2.1, k.2.2.2.1, fun n v w hv hw => ?_⟩
  have hvM := (hM.toTransClass.of_pair_mem hs hv).2
  have hwM := (hM.toTransClass.of_pair_mem hs hw).2
  exact (hM.sat_stepN Δ hvM hwM hM.envω_mem).1 (k.2.2.2.2 n v w hv hw)

section History
variable (Δ : List Fml) {lam s : PSet.{u}} (hlamo : IsOrd lam) (hlam : M lam) (hs : M s) (h : HistN M Δ lam s)
include hlamo hlam hs h

omit hlamo in
theorem hist_zero {v : PSet.{u}} (hv : PSet.pair PSet.empty v ∈ s) : v ≈ lam :=
  (hM.hist_spec Δ hlam hs h).2.2.1 _ v lam hv (hM.hist_spec Δ hlam hs h).2.1

omit hlamo in
theorem hist_total (k : Nat) : ¬¬∃ v, PSet.pair (ofNat k) v ∈ s :=
  (hM.hist_spec Δ hlam hs h).2.2.2.1 _ (ofNat_mem_omega k)

/-- The orbit from an ordinal stays ordinal. -/
theorem hist_ord : ∀ (k : Nat) (v : PSet.{u}), PSet.pair (ofNat k) v ∈ s → IsOrd v
  | 0, v, hv => hlamo.resp (hM.hist_zero Δ hlam hs h hv).symm
  | k+1, w, hw => by
    refine Stable.of_nn (hM.hist_total Δ hlam hs h k) fun ⟨v, hv⟩ => ?_
    have hvo := hist_ord k v hv
    refine Stable.of_nn ((hM.hist_spec Δ hlam hs h).2.2.2.2 _ v w hv hw) fun
      | .inl ⟨_, hn⟩ => hn.isOrd
      | .inr ⟨ho, _⟩ => (ho hvo).elim

theorem hist_next {k : Nat} {v w : PSet.{u}} (hv : PSet.pair (ofNat k) v ∈ s) (hw : PSet.pair (ofNat (k+1)) w ∈ s) :
    NextStage M Δ v w :=
  Stable.of_nn ((hM.hist_spec Δ hlam hs h).2.2.2.2 _ v w hv hw) fun
    | .inl ⟨_, hn⟩ => hn
    | .inr ⟨ho, _⟩ => (ho (hM.hist_ord Δ hlamo hlam hs h k v hv)).elim

omit hlamo hlam h in
theorem hist_mem_class {n v : PSet.{u}} (hv : PSet.pair n v ∈ s) : M v := (hM.toTransClass.of_pair_mem hs hv).2

/-- Rows are included along the order of the indices. -/
theorem hist_le : ∀ (d m : Nat) {v w : PSet.{u}}, PSet.pair (ofNat m) v ∈ s → PSet.pair (ofNat (m + d)) w ∈ s →
    ∀ x, x ∈ v → x ∈ w
  | 0, _, v, w, hv, hw, x, hx => (mem_congr_right ((hM.hist_spec Δ hlam hs h).2.2.1 _ v w hv hw)).1 hx
  | d+1, m, v, w, hv, hw, x, hx => by
    refine Stable.of_nn (hM.hist_total Δ hlam hs h (m + d)) fun ⟨u, hu⟩ => ?_
    have hxu := hist_le d m hv hu x hx
    have hn := hM.hist_next Δ hlamo hlam hs h hu hw
    exact hn.isOrd.trans u hn.lt x hxu

omit hlamo in
/-- Every row index of the history is, negatively, a numeral. -/
theorem hist_row_nat {n v : PSet.{u}} (hv : PSet.pair n v ∈ s) : ¬¬∃ k, PSet.pair (ofNat k) v ∈ s := by
  refine nn_bind ((hM.hist_spec Δ hlam hs h).1 _ hv) fun ⟨n', v', hn', e⟩ => ?_
  have ⟨en, _⟩ := pair_inj e
  refine nn_map (fun ⟨k, ek⟩ => ⟨k, ?_⟩) (mem_omega.1 ((mem_congr_left en).2 hn'))
  exact (mem_congr_left (pair_congr ek (Equiv.refl _))).1 hv

/-- **The supremum of the history**: a nonzero limit above `lam`, with the rows cofinal in it. -/
theorem sup_spec : ∃ θ, M θ ∧ IsLimit θ ∧ lam ∈ θ ∧ (∀ k v, PSet.pair (ofNat k) v ∈ s → v ∈ θ) ∧
    (∀ x, x ∈ θ → ¬¬∃ k v, PSet.pair (ofNat k) v ∈ s ∧ x ∈ v) := by
  have hT := hM.toTransClass
  let U := PSet.sUnion (PSet.sUnion s)
  have hUM : M U := hM.sUnion (hM.sUnion hs)
  have he : ∀ i, M (Env.cons U (Env.cons s envω) i) := Env.cons_mem hUM (Env.cons_mem hs hM.envω_mem)
  let R := PSet.sep (fun v => Sat M (ex (pairMemF 3 0 1)) (Env.cons v (Env.cons U (Env.cons s envω)))) U
  have hRM : M R := hM.sepM (ex (pairMemF 3 0 1)) he
  have hR : ∀ v, v ∈ R ↔ ¬¬∃ n, PSet.pair n v ∈ s := by
    intro v
    refine (mem_sep fun _ _ e k => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k).trans ⟨fun ⟨hvU, hs'⟩ => ?_, fun k => ?_⟩
    · have hvM := hM.trans hUM hvU
      refine nn_map (fun ⟨n, hn, hp⟩ => ⟨n, ?_⟩) (sat_ex.1 hs')
      exact (hT.sat_pairMemF (Env.cons_mem hn (Env.cons_mem hvM he)) 3 0 1).1 hp
    · have hvU : v ∈ U := Stable.of_nn k fun ⟨n, hp⟩ =>
        mem_sUnion.2 (nn_intro ⟨PSet.upair n v, mem_sUnion.2 (nn_intro ⟨PSet.pair n v, hp, mem_upair_right _ _⟩), mem_upair_right _ _⟩)
      have hvM := hM.trans hUM hvU
      refine ⟨hvU, sat_ex.2 (nn_map (fun ⟨n, hp⟩ => ?_) k)⟩
      have hnM := (hT.of_pair_mem hs hp).1
      exact ⟨n, hnM, (hT.sat_pairMemF (Env.cons_mem hnM (Env.cons_mem hvM he)) 3 0 1).2 hp⟩
  have hRo : ∀ v, v ∈ R → IsOrd v := fun v hv => Stable.of_nn ((hR v).1 hv) fun ⟨n, hp⟩ =>
    Stable.of_nn (hM.hist_row_nat Δ hlam hs h hp) fun ⟨k, hk⟩ => hM.hist_ord Δ hlamo hlam hs h k v hk
  have hθo : IsOrd (PSet.sUnion R) := isOrd_sUnion hRo
  have rows : ∀ k v, PSet.pair (ofNat k) v ∈ s → v ∈ PSet.sUnion R := fun k v hv =>
    Stable.of_nn (hM.hist_total Δ hlam hs h (k+1)) fun ⟨w, hw⟩ =>
      mem_sUnion.2 (nn_intro ⟨w, (hR w).2 (nn_intro ⟨_, hw⟩), (hM.hist_next Δ hlamo hlam hs h hv hw).lt⟩)
  have fit : ∀ x, x ∈ PSet.sUnion R → ¬¬∃ k v, PSet.pair (ofNat k) v ∈ s ∧ x ∈ v := fun x hx =>
    nn_bind (mem_sUnion.1 hx) fun ⟨v, hvR, hxv⟩ => nn_bind ((hR v).1 hvR) fun ⟨n, hp⟩ =>
      nn_map (fun ⟨k, hk⟩ => ⟨k, v, hk, hxv⟩) (hM.hist_row_nat Δ hlam hs h hp)
  have hlamθ : lam ∈ PSet.sUnion R := rows 0 lam (hM.hist_spec Δ hlam hs h).2.1
  refine ⟨PSet.sUnion R, hM.sUnion hRM, ⟨hθo, nn_intro ⟨lam, hlamθ⟩, fun x hx => ?_⟩, hlamθ, rows, fit⟩
  refine Stable.of_nn (fit x hx) fun ⟨k, v, hv, hxv⟩ => Stable.of_nn (hM.hist_total Δ hlam hs h (k+1)) fun ⟨w, hw⟩ => ?_
  have hvo := hM.hist_ord Δ hlamo hlam hs h k v hv
  have hn := hM.hist_next Δ hlamo hlam hs h hv hw
  have hsx : succ x ∈ succ v := (hvo.mem hxv).succ.mem_succ_of_subset hvo fun y hy =>
    Stable.of_nn (mem_succ.1 hy) fun
      | .inl k => hvo.trans x hxv y k
      | .inr e => (mem_congr_left e).2 hxv
  have hsxw : succ x ∈ w := Stable.of_nn (mem_succ.1 hsx) fun
    | .inl k => hn.isOrd.trans v hn.lt _ k
    | .inr e => (mem_congr_left e).2 hn.lt
  exact mem_sUnion.2 (nn_intro ⟨w, (hR w).2 (nn_intro ⟨_, hw⟩), hsxw⟩)

end History

end SynZF

/-! ### Reflection at the supremum -/

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

omit hM in
theorem constr_of_mem_level {θ B x : PSet.{u}} (hθ : IsOrd θ) (hB : Level M θ B) (hx : x ∈ B) : Constr M x :=
  nn_intro ⟨θ, B, hθ, hB, hx⟩

section Sup
variable (Δ : List Fml) {lam s θ B : PSet.{u}} (hlamo : IsOrd lam) (hlam : M lam) (hs : M s) (h : HistN M Δ lam s)
  (hθ : IsLimit θ) (hθM : M θ) (rows : ∀ k v, PSet.pair (ofNat k) v ∈ s → v ∈ θ)
  (fit : ∀ x, x ∈ θ → ¬¬∃ k v, PSet.pair (ofNat k) v ∈ s ∧ x ∈ v) (hB : Level M θ B)
include hlamo hlam hs h hθ hθM rows fit hB

omit rows in
/-- Every member of the level at the supremum lies in the level of some row. -/
theorem sup_fit {x : PSet.{u}} (hx : x ∈ B) : ¬¬∃ k v, PSet.pair (ofNat k) v ∈ s ∧ InLevel M x v := by
  refine nn_bind ((hM.level_limit hθ hθM hB x).1 hx) fun ⟨β, hβ, k⟩ => nn_bind k fun ⟨B', hB', hxB'⟩ =>
    nn_bind (fit β hβ) fun ⟨k, v, hv, hβv⟩ => ?_
  have hvo := hM.hist_ord Δ hlamo hlam hs h k v hv
  have hvM := hM.hist_mem_class hs hv
  exact nn_map (fun ⟨Bv, _, hBv⟩ => ⟨k, v, hv, nn_intro ⟨Bv, ⟨hvo, hBv⟩, hM.level_mono hvo hvM hβv hBv hB' x hxB'⟩⟩)
    (hM.level_exists hvo hvM)

omit rows in
/-- **Finite fit**: finitely many members of the level at the supremum lie in one row level. -/
theorem sup_fit_finite : ∀ (n : Nat) (e : Nat → PSet.{u}), (∀ i, i < n → e i ∈ B) →
    ¬¬∃ k v, PSet.pair (ofNat k) v ∈ s ∧ ∀ i, i < n → InLevel M (e i) v
  | 0, _, _ => nn_map (fun ⟨v, hv⟩ => ⟨0, v, hv, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩) (hM.hist_total Δ hlam hs h 0)
  | n+1, e, he => by
    refine nn_bind (sup_fit_finite n e fun i hi => he i (Nat.lt_succ_of_lt hi)) fun ⟨k₁, v₁, hv₁, hf₁⟩ =>
      nn_bind (hM.sup_fit Δ hlamo hlam hs h hθ hθM fit hB (he n (Nat.lt_succ_self n))) fun ⟨k₂, v₂, hv₂, hf₂⟩ =>
      nn_map (fun ⟨v, hv⟩ => ?_) (hM.hist_total Δ hlam hs h (k₁ + k₂))
    have hvo := hM.hist_ord Δ hlamo hlam hs h _ v hv
    have hvM := hM.hist_mem_class hs hv
    have h1 : ∀ x, x ∈ v₁ → x ∈ v := hM.hist_le Δ hlamo hlam hs h k₂ k₁ hv₁ hv
    have hv' : PSet.pair (ofNat (k₂ + k₁)) v ∈ s := Nat.add_comm k₁ k₂ ▸ hv
    have h2 : ∀ x, x ∈ v₂ → x ∈ v := hM.hist_le Δ hlamo hlam hs h k₁ k₂ hv₂ hv'
    refine ⟨k₁ + k₂, v, hv, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i n with h' | h'
    · exact hM.inLevel_mono hvo hvM h1 (hf₁ i h')
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
      exact hM.inLevel_mono hvo hvM h2 hf₂

/-- **Reflection at the supremum**: for a formula whose requests are among those of `Δ`, with
its relevant parameters in the level at the supremum, satisfaction in that level agrees with
satisfaction in `N`. -/
theorem reflect_at_sup : ∀ (p : Fml), (∀ m, m ∈ requests p → m ∈ matrices Δ) → ∀ (e : Nat → PSet.{u}),
    (∀ i, i < fv p → e i ∈ B) → (Sat (fun z => z ∈ B) p e ↔ Sat (Constr M) p e)
  | .mem _ _, _, _, _ => Iff.rfl
  | .eq _ _, _, _, _ => Iff.rfl
  | .fls, _, _, _ => Iff.rfl
  | .imp p q, hr, e, he =>
    imp_congr (reflect_at_sup p (fun m hm => hr m (mem_append_left _ hm)) e
        fun i hi => he i (Nat.lt_of_lt_of_le hi (le_nmax_left _ _)))
      (reflect_at_sup q (fun m hm => hr m (mem_append_right _ hm)) e
        fun i hi => he i (Nat.lt_of_lt_of_le hi (le_nmax_right _ _)))
  | .all q, hr, e, he => by
    have hθo := hθ.1
    have htB : Trans B := hM.level_trans hθo hθM hB
    have ext : ∀ x, x ∈ B → ∀ i, i < fv q → Env.cons x e i ∈ B := fun x hx i hi => by
      rcases i with _ | i
      · exact hx
      · exact he i (Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hi (le_pred_succ _)))
    have ih : ∀ x, x ∈ B → (Sat (fun z => z ∈ B) q (Env.cons x e) ↔ Sat (Constr M) q (Env.cons x e)) := fun x hx =>
      reflect_at_sup q (fun m hm => hr m (.tail _ hm)) (Env.cons x e) (ext x hx)
    constructor
    · intro hall x hx
      refine (Sat.stable q _).dne fun hn => ?_
      have hm : (⟨(fv q).pred, neg q⟩ : Matrix) ∈ matrices Δ := hr _ (.head _)
      refine Stable.of_nn (hM.sup_fit_finite Δ hlamo hlam hs h hθ hθM fit hB (fv q).pred e he) fun ⟨k, v, hv, hf⟩ => ?_
      refine Stable.of_nn (hM.hist_total Δ hlam hs h (k+1)) fun ⟨w, hw⟩ => ?_
      have hn' := hM.hist_next Δ hlamo hlam hs h hv hw
      have hvo := hn'.1.1
      refine Stable.of_nn hn'.1.2.2.2 fun ⟨A', B', hA', hB', hc⟩ => ?_
      have heA' : ∀ i, i < (fv q).pred → e i ∈ A' := fun i hi =>
        Stable.of_nn (hf i hi) fun ⟨Bv, ⟨_, hBv⟩, hi'⟩ => (mem_congr_right (level_unique hvo hBv hA')).1 hi'
      have heM : ∀ i, i < (fv q).pred → M (e i) := fun i hi => hM.trans (hM.level_mem_class hB).2 (he i hi)
      have cap := hc _ hm e heM heA' (nn_intro ⟨x, hx, hn⟩)
      refine Stable.of_nn cap fun ⟨z, hzB', _, hz⟩ => ?_
      have hzB : z ∈ B := hM.level_mono hθo hθM (rows (k+1) w hw) hB hB' z hzB'
      exact hz ((ih z hzB).1 (hall z hzB))
    · intro hall x hx
      exact (ih x hx).2 (hall x (constr_of_mem_level hθo hB hx))

end Sup

/-- **The reflection theorem**: above any ordinal of the class there is a limit `θ` whose level
reflects every formula of `Δ` for parameters in the level. -/
theorem reflection (Δ : List Fml) {lam : PSet.{u}} (hlamo : IsOrd lam) (hlam : M lam) :
    ¬¬∃ θ B, M θ ∧ IsLimit θ ∧ lam ∈ θ ∧ Level M θ B ∧ ∀ p, p ∈ Δ → ∀ e : Nat → PSet.{u},
      (∀ i, i < fv p → e i ∈ B) → (Sat (fun z => z ∈ B) p e ↔ Sat (Constr M) p e) := by
  refine nn_bind (hM.hist_exists Δ hlam) fun ⟨s, hs, h⟩ => ?_
  have ⟨θ, hθM, hθ, hlamθ, rows, fit⟩ := hM.sup_spec Δ hlamo hlam hs h
  refine nn_map (fun ⟨B, _, hB⟩ => ⟨θ, B, hθM, hθ, hlamθ, hB, fun p hp e he => ?_⟩) (hM.level_exists hθ.1 hθM)
  exact hM.reflect_at_sup Δ hlamo hlam hs h hθ hθM rows fit hB p (fun m hm => mem_matrices hp hm) e he

/-! ### Separation in `N` and the assembly -/

/-- Finitely many constructible parameters lie in one level. -/
theorem params_bound (e : Nat → PSet.{u}) : ∀ n, (∀ i, i < n → Constr M (e i)) →
    ¬¬∃ lam, IsOrd lam ∧ M lam ∧ ∀ i, i < n → InLevel M (e i) lam
  | 0, _ => nn_intro ⟨PSet.empty, isOrd_empty, hM.empty, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩
  | n+1, he => by
    refine nn_bind (params_bound e n fun i hi => he i (Nat.lt_succ_of_lt hi)) fun ⟨lam₁, ho₁, hM₁, hf₁⟩ =>
      nn_map (fun ⟨α, A, hα, hA, hx⟩ => ?_) (he n (Nat.lt_succ_self n))
    have hαM := (hM.level_mem_class hA).1
    have hu := ho₁.union hα
    have huM := hM.union hM₁ hαM
    refine ⟨PSet.union lam₁ α, hu, huM, fun i hi => ?_⟩
    rcases Nat.lt_or_ge i n with h' | h'
    · exact hM.inLevel_mono hu huM (fun x hx => mem_union.2 (nn_intro (.inl hx))) (hf₁ i h')
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) h'
      exact hM.inLevel_mono hu huM (fun x hx => mem_union.2 (nn_intro (.inr hx))) (nn_intro ⟨A, ⟨hα, hA⟩, hx⟩)

/-- **Separation in `N`**, uniformly over native formulas. -/
theorem sepN (ψ : Fml) : Valid (Constr M) (ZFAx.sep ψ) := by
  intro e he
  let n := nmax (fv ψ) 2
  refine Stable.of_nn (hM.params_bound e n fun i _ => he i) fun ⟨lam, hlamo, hlam, hf⟩ => ?_
  refine Stable.of_nn (hM.reflection [ψ] hlamo hlam) fun ⟨θ, B, hθM, hθ, hlamθ, hB, hrefl⟩ => ?_
  have hθo := hθ.1
  have htB : Trans B := hM.level_trans hθo hθM hB
  have heB : ∀ i, i < n → e i ∈ B := fun i hi =>
    Stable.of_nn (hf i hi) fun ⟨Bl, ⟨_, hBl⟩, hi'⟩ => hM.level_mono hθo hθM hlamθ hB hBl _ hi'
  have h0 : e 0 ∈ B := heB 0 (Nat.lt_of_lt_of_le (by decide) (le_nmax_right _ _))
  let P : PSet.{u} → Prop := fun z => Sat (Constr M) ψ (Env.cons z e)
  let φ : Fml := and (mem 0 1) ψ
  let y := dval B φ e
  have hy : ∀ z, z ∈ y ↔ z ∈ e 0 ∧ P z := by
    intro z
    refine mem_dval.trans ⟨fun ⟨hzB, hs⟩ => ?_, fun ⟨hz0, hz⟩ => ?_⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      refine ⟨h1, (hrefl ψ (.head _) (Env.cons z e) fun i hi => ?_).1 h2⟩
      rcases i with _ | i
      · exact hzB
      · exact heB i (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hi (le_pred_succ _)))
          (Nat.le_trans (Nat.pred_le _) (le_nmax_left _ _)))
    · have hzB : z ∈ B := htB _ h0 z hz0
      refine ⟨hzB, sat_and.2 ⟨hz0, (hrefl ψ (.head _) (Env.cons z e) fun i hi => ?_).2 hz⟩⟩
      rcases i with _ | i
      · exact hzB
      · exact heB i (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt_succ (Nat.lt_of_lt_of_le hi (le_pred_succ _)))
          (Nat.le_trans (Nat.pred_le _) (le_nmax_left _ _)))
  have hyN : Constr M y := hM.constr_of_definable ⟨hθo, hB⟩ (nn_intro ⟨n, φ, e,
    Bound.and ⟨Nat.succ_pos _, Nat.lt_of_lt_of_le (by decide) (Nat.succ_le_succ (le_nmax_right _ _))⟩
      ((bound_fv ψ).mono (Nat.le_trans (le_nmax_left _ _) (Nat.le_succ _))), heB, Equiv.refl _⟩)
  refine sat_ex.2 (nn_intro ⟨y, hyN, fun z _ => sat_iff.2 ?_⟩)
  have hPz : P z ↔ Sat (Constr M) (rename ZFAx.sepR ψ) (Env.cons z (Env.cons y e)) :=
    .trans (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by cases i <;> exact Equiv.refl _)
      (sat_rename ψ ZFAx.sepR _).symm
  refine (hy z).trans ⟨fun ⟨a, b⟩ => sat_and.2 ⟨a, hPz.1 b⟩, fun h => ?_⟩
  have ⟨a, b⟩ := sat_and.1 h
  exact ⟨a, hPz.2 b⟩

/-- **The constructible class is a syntactic model of `ZF`.** -/
theorem synZF_constr : SynZF (Constr M) :=
  ⟨fun _ => inferInstance, fun e h => Constr.congr e h, fun hx hz => SynZF.Constr.trans hM hx hz, hM.omegaN,
    hM.valid_of_sep hM.sepN⟩

end SynZF

/-- info: 'PSet.SynZF.next_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.next_exists
/-- info: 'PSet.SynZF.hist_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.hist_exists
/-- info: 'PSet.SynZF.reflection' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.reflection
/-- info: 'PSet.SynZF.sepN' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.sepN
/-- info: 'PSet.SynZF.synZF_constr' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.synZF_constr

end PSet
