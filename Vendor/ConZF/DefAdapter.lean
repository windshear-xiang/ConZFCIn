import Vendor.ConZF.Reflection
import Vendor.ConZF.Assign
/-!
The generic guarded `Def` adapter (gate 3, con28 §3–4). For supplied formulas `S` (`A, q, e`;
`Bound 3`) and `C` (`q, r`; `Bound 2`), the evaluation `evalF S` (`A, q, p, x`) says some cons
of `x` onto `p` satisfies `S` at `A, q`; a member of the definable family (`dmemberF S C`; `A, z`)
is a set `z` for which there are a pure function `p : n → A`, `m = succ n`, a code `q` scoped at
`m` by `C`, with `z = {x ∈ A : evalF S A q p x}`; and `defF S C` (`A, B`) says `B` is the family.
Scope lemmas by bounded renaming. **Generic internal existence and uniqueness**
(`defF_exists`, `defF_unique`) use only two Separations and the internal powerset, for any `S, C`
of the stated bounds: nothing about correctness of `S` or `C` enters, and if `C` is always false
the output is empty. The exact model-relative membership law (`mem_of_defF`) describes the
output through the first Separation values `valueOf`.
-/
universe u

namespace PSet
open Fml CardF RecF AssignF

namespace DefAdapter

def slot : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: xs, n+1 => slot xs n

/-- Instantiate a formula at the listed slots. -/
def inst (f : Fml) (args : List Nat) : Fml := rename (slot args) f

/-- `A, q, p, x`: some cons of `x` onto `p` satisfies `S` at `A, q`. -/
def evalF (S : Fml) : Fml := ex (and (consF 0 4 3) (inst S [1, 2, 0]))

/-- `A, z`: `z` is a definable subset. Binders `n, q, p, m`, environment `[m, p, q, n, A, z]`;
the final universal gives `[x, m, p, q, n, A, z]`. -/
def dmemberF (S C : Fml) : Fml :=
  ex (ex (ex (ex (and (funF 1 3 4) (and (succF 0 3) (and (inst C [2, 0])
    (all (iff (mem 0 6) (and (mem 0 5) (inst (evalF S) [5, 3, 2, 0]))))))))))

/-- `A, B`: `B` is the definable family of `A`. -/
def defF (S C : Fml) : Fml := all (iff (mem 0 2) (inst (dmemberF S C) [1, 0]))

/-- The first Separation matrix: base environment `[A, q, p, …]`, candidate `[x, A, q, p, …]`. -/
def valueSepF (S : Fml) : Fml := inst (evalF S) [1, 2, 3, 0]

/-- The second Separation matrix: base environment `[P, A, …]`, candidate `[z, P, A, …]`. -/
def outerSepF (S C : Fml) : Fml := inst (dmemberF S C) [2, 0]

end DefAdapter

open DefAdapter

/-! ### Scope -/

theorem bound_inst {f : Fml} {k : Nat} (hf : Bound k f) {args : List Nat} {m : Nat}
    (h : ∀ i, i < k → slot args i < m) : Bound m (inst f args) := bound_rename hf h

theorem slot_lt {args : List Nat} {m : Nat} (h : ∀ a, a ∈ args → a < m) (hm : 0 < m) :
    ∀ i, slot args i < m := by
  intro i
  induction args generalizing i with
  | nil => exact hm
  | cons a xs ih =>
    cases i with
    | zero => exact h a (.head _)
    | succ i => exact ih (fun b hb => h b (.tail _ hb)) i

/-! ### Semantics -/

/-- The ambient reading of the evaluation: some cons in the class satisfies `S`. -/
def EvalP (M : PSet.{u} → Prop) (S : Fml) (A q p x : PSet.{u}) : Prop :=
  ¬¬∃ t, M t ∧ IsCons t x p ∧ Sat M S (Env.cons A (Env.cons q (Env.cons t envω)))

/-- The ambient reading of a definable member: a package and a scoped code whose value is `z`. -/
def MemberP (M : PSet.{u} → Prop) (S C : Fml) (A z : PSet.{u}) : Prop :=
  ¬¬∃ n q p m, M n ∧ M q ∧ M p ∧ M m ∧ IsPureFun A p n ∧ m ≈ succ n ∧
    Sat M C (Env.cons q (Env.cons m envω)) ∧ ∀ x, M x → (x ∈ z ↔ x ∈ A ∧ EvalP M S A q p x)

instance {M : PSet.{u} → Prop} {S : Fml} {A q p x : PSet.{u}} : Stable (EvalP M S A q p x) := inferInstanceAs (Stable (¬_))
instance {M : PSet.{u} → Prop} {S C : Fml} {A z : PSet.{u}} : Stable (MemberP M S C A z) := inferInstanceAs (Stable (¬_))

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M) {S C : Fml} (hS : Bound 3 S) (hC : Bound 2 C)
include hM

omit hM in
include hS in
/-- `S` at the environment of the evaluation reads at the three slots. -/
theorem sat_inst_S {t A q p x : PSet.{u}} {E : Nat → PSet.{u}} :
    Sat M (inst S [1, 2, 0]) (Env.cons t (Env.cons A (Env.cons q (Env.cons p (Env.cons x E))))) ↔
      Sat M S (Env.cons A (Env.cons q (Env.cons t envω))) :=
  (sat_rename _ _ _).trans (sat_bound hS fun i hi => by
    rcases i with _ | _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi)))).elim)

include hS in
theorem sat_evalF {A q p x : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) (hq : M q) (hp : M p) (hx : M x) (hE : ∀ i, M (E i)) :
    Sat M (evalF S) (Env.cons A (Env.cons q (Env.cons p (Env.cons x E)))) ↔ EvalP M S A q p x := by
  have hT := hM.toTransClass
  have hE4 : ∀ i, M (Env.cons A (Env.cons q (Env.cons p (Env.cons x E))) i) :=
    Env.cons_mem hA (Env.cons_mem hq (Env.cons_mem hp (Env.cons_mem hx hE)))
  refine sat_ex.trans (nn_congr ⟨fun ⟨t, ht, h⟩ => ?_, fun ⟨t, ht, hc, hs⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 h
    exact ⟨t, ht, (hT.sat_consF (Env.cons_mem ht hE4) 0 4 3 hM.succ_mem hM.empty).1 h1, (sat_inst_S hS).1 h2⟩
  · exact ⟨t, ht, sat_and.2 ⟨(hT.sat_consF (Env.cons_mem ht hE4) 0 4 3 hM.succ_mem hM.empty).2 hc, (sat_inst_S hS).2 hs⟩⟩

omit hM in
include hC in
theorem sat_inst_C {m p q n A z : PSet.{u}} {E : Nat → PSet.{u}} :
    Sat M (inst C [2, 0]) (Env.cons m (Env.cons p (Env.cons q (Env.cons n (Env.cons A (Env.cons z E)))))) ↔
      Sat M C (Env.cons q (Env.cons m envω)) :=
  (sat_rename _ _ _).trans (sat_bound hC fun i hi => by
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim)

include hS in
theorem sat_inst_eval {x m p q n A z : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) (hq : M q) (hp : M p) (hx : M x) :
    Sat M (inst (evalF S) [5, 3, 2, 0]) (Env.cons x (Env.cons m (Env.cons p (Env.cons q (Env.cons n (Env.cons A (Env.cons z E))))))) ↔
      EvalP M S A q p x := by
  refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_evalF hS hA hq hp hx (E := fun _ => x) fun _ => hx))
  refine Sat.resp_iff (fun _ => Iff.rfl) _ fun i => ?_
  rcases i with _ | _ | _ | _ | i
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _

include hS hC in
/-- **The member bridge.** -/
theorem sat_dmemberF {A z : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) (hz : M z) (hE : ∀ i, M (E i)) :
    Sat M (dmemberF S C) (Env.cons A (Env.cons z E)) ↔ MemberP M S C A z := by
  have hT := hM.toTransClass
  have hE2 : ∀ i, M (Env.cons A (Env.cons z E) i) := Env.cons_mem hA (Env.cons_mem hz hE)
  refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨n, hn, h⟩ => nn_bind (sat_ex.1 h) fun ⟨q, hq, h⟩ =>
    nn_bind (sat_ex.1 h) fun ⟨p, hp, h⟩ => nn_map (fun ⟨m, hm, h⟩ => ?_) (sat_ex.1 h),
    fun h => nn_map (fun ⟨n, q, p, m, hn, hq, hp, hm, hf, hsm, hc, hv⟩ => ?_) h⟩
  · have hE6 := Env.cons_mem hm (Env.cons_mem hp (Env.cons_mem hq (Env.cons_mem hn hE2)))
    have ⟨h1, h⟩ := sat_and.1 h
    have ⟨h2, h⟩ := sat_and.1 h
    have ⟨h3, h4⟩ := sat_and.1 h
    refine ⟨n, q, p, m, hn, hq, hp, hm, (hT.sat_funF_iff hE6 1 3 4).1 h1, (hT.sat_succF hE6 0 3).1 h2,
      (sat_inst_C hC).1 h3, fun x hx => ?_⟩
    exact (sat_iff.1 (h4 x hx)).trans (sat_and.trans (and_congr Iff.rfl (hM.sat_inst_eval hS hA hq hp hx)))
  · have hE6 := Env.cons_mem hm (Env.cons_mem hp (Env.cons_mem hq (Env.cons_mem hn hE2)))
    refine ⟨n, hn, sat_ex.2 (nn_intro ⟨q, hq, sat_ex.2 (nn_intro ⟨p, hp, sat_ex.2 (nn_intro ⟨m, hm, sat_and.2
      ⟨(hT.sat_funF_iff hE6 1 3 4).2 hf, sat_and.2 ⟨(hT.sat_succF hE6 0 3).2 hsm, sat_and.2 ⟨(sat_inst_C hC).2 hc,
        fun x hx => sat_iff.2 ((hv x hx).trans (sat_and (φ := mem 0 5) (ψ := DefAdapter.inst (evalF S) [5, 3, 2, 0])
          (e := Env.cons x (Env.cons m (Env.cons p (Env.cons q (Env.cons n (Env.cons A (Env.cons z E))))))) |>.trans
          (and_congr Iff.rfl (hM.sat_inst_eval hS hA hq hp hx))).symm)⟩⟩⟩⟩)⟩)⟩)⟩

include hS hC in
/-- **The family bridge.** -/
theorem sat_defF {A B : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) :
    Sat M (defF S C) (Env.cons A (Env.cons B E)) ↔ ∀ z, M z → (z ∈ B ↔ MemberP M S C A z) := by
  refine forall_congr' fun z => forall_congr' fun hz => ?_
  have key : Sat M (inst (dmemberF S C) [1, 0]) (Env.cons z (Env.cons A (Env.cons B E))) ↔ MemberP M S C A z := by
    refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_dmemberF hS hC hA hz (E := fun _ => z) fun _ => hz))
    refine Sat.resp_iff (fun _ => Iff.rfl) _ fun i => ?_
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
  exact sat_iff.trans ⟨fun h => h.trans key, fun h => h.trans key.symm⟩

/-- The value of a package: the first Separation. -/
def valueOf (S : Fml) (A q p : PSet.{u}) : PSet.{u} :=
  sep (fun x => Sat M (valueSepF S) (Env.cons x (Env.cons A (Env.cons q (Env.cons p envω))))) A

omit hC in
theorem valueOf_mem {A q p : PSet.{u}} (hA : M A) (hq : M q) (hp : M p) : M (valueOf (M := M) S A q p) :=
  hM.sepM (valueSepF S) (Env.cons_mem hA (Env.cons_mem hq (Env.cons_mem hp hM.envω_mem)))

omit hC in
include hS in
/-- The first Separation matrix at a member reads as the evaluation. -/
theorem sat_valueSepF {A q p x : PSet.{u}} (hA : M A) (hq : M q) (hp : M p) (hx : M x) :
    Sat M (valueSepF S) (Env.cons x (Env.cons A (Env.cons q (Env.cons p envω)))) ↔ EvalP M S A q p x := by
  refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_evalF hS hA hq hp hx (E := fun _ => x) fun _ => hx))
  refine Sat.resp_iff (fun _ => Iff.rfl) _ fun i => ?_
  rcases i with _ | _ | _ | _ | i
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _
  · exact Equiv.refl _

omit hC in
include hS in
/-- The members of a value. -/
theorem mem_valueOf {A q p x : PSet.{u}} (hA : M A) (hq : M q) (hp : M p) :
    x ∈ valueOf (M := M) S A q p ↔ x ∈ A ∧ EvalP M S A q p x := by
  have hψ : ∀ x x' : PSet.{u}, x ≈ x' → Sat M (valueSepF S) (Env.cons x (Env.cons A (Env.cons q (Env.cons p envω)))) →
      Sat M (valueSepF S) (Env.cons x' (Env.cons A (Env.cons q (Env.cons p envω)))) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine (mem_sep hψ).trans ⟨fun ⟨hxA, h⟩ => ⟨hxA, (hM.sat_valueSepF hS hA hq hp (hM.trans hA hxA)).1 h⟩,
    fun ⟨hxA, h⟩ => ⟨hxA, (hM.sat_valueSepF hS hA hq hp (hM.trans hA hxA)).2 h⟩⟩

include hS hC in
/-- **Generic internal existence** of the definable family, for any `S, C` of the stated bounds:
the outer Separation of an internal powerset of `A`. -/
theorem defF_exists {A : PSet.{u}} (hA : M A) :
    ¬¬∃ B, M B ∧ ∀ E : Nat → PSet.{u}, (∀ i, M (E i)) → Sat M (defF S C) (Env.cons A (Env.cons B E)) := by
  refine nn_map (fun ⟨P, hP, hPm⟩ => ?_) (hM.powM hA)
  let E0 : Nat → PSet.{u} := Env.cons P (Env.cons A envω)
  have hE0 : ∀ i, M (E0 i) := Env.cons_mem hP (Env.cons_mem hA hM.envω_mem)
  have key : ∀ z, M z → (Sat M (outerSepF S C) (Env.cons z E0) ↔ MemberP M S C A z) := by
    intro z hz
    refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_dmemberF hS hC hA hz (E := fun _ => z) fun _ => hz))
    refine Sat.resp_iff (fun _ => Iff.rfl) _ fun i => ?_
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
  have hψ : ∀ z z' : PSet.{u}, z ≈ z' → Sat M (outerSepF S C) (Env.cons z E0) → Sat M (outerSepF S C) (Env.cons z' E0) :=
    fun _ _ e h => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine ⟨_, hM.sepM (outerSepF S C) hE0, fun E hE => (hM.sat_defF hS hC hA).2 fun z hz => ?_⟩
  refine (mem_sep hψ).trans ⟨fun ⟨_, h⟩ => (key z hz).1 h, fun h => ⟨?_, (key z hz).2 h⟩⟩
  -- a definable member is a subset of `A`, hence in the internal powerset
  refine (hPm z hz).2 fun x hx => ?_
  refine Stable.of_nn h fun ⟨_, _, _, _, _, _, _, _, _, _, _, hv⟩ => ?_
  exact ((hv x (hM.trans hz hx)).1 hx).1

include hS hC in
/-- **Generic uniqueness** of the family. -/
theorem defF_unique {A B B' : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) (hB : M B) (hB' : M B')
    (h : Sat M (defF S C) (Env.cons A (Env.cons B E))) (h' : Sat M (defF S C) (Env.cons A (Env.cons B' E))) :
    B ≈ B' :=
  have k := (hM.sat_defF hS hC hA).1 h
  have k' := (hM.sat_defF hS hC hA).1 h'
  ext fun z => ⟨fun hz => (k' z (hM.trans hB hz)).2 ((k z (hM.trans hB hz)).1 hz),
    fun hz => (k z (hM.trans hB' hz)).2 ((k' z (hM.trans hB' hz)).1 hz)⟩

include hS in
/-- A member of the class is a definable member exactly when it is the value of an admissible
package. -/
theorem memberP_iff {A z : PSet.{u}} (hA : M A) (hz : M z) :
    MemberP M S C A z ↔ ¬¬∃ n q p m, M n ∧ M q ∧ M p ∧ M m ∧ IsPureFun A p n ∧ m ≈ succ n ∧
      Sat M C (Env.cons q (Env.cons m envω)) ∧ z ≈ valueOf (M := M) S A q p := by
  constructor
  · intro h
    refine nn_map (fun ⟨n, q, p, m, hn, hq, hp, hm, hf, hsm, hc, hv⟩ => ⟨n, q, p, m, hn, hq, hp, hm, hf, hsm, hc, ?_⟩) h
    refine ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact (hM.mem_valueOf hS hA hq hp).2 ((hv x (hM.trans hz hx)).1 hx)
    · have ⟨hxA, hev⟩ := (hM.mem_valueOf hS hA hq hp).1 hx
      exact (hv x (hM.trans hA hxA)).2 ⟨hxA, hev⟩
  · intro h
    refine nn_map (fun ⟨n, q, p, m, hn, hq, hp, hm, hf, hsm, hc, ev⟩ => ⟨n, q, p, m, hn, hq, hp, hm, hf, hsm, hc, fun x _ => ?_⟩) h
    exact (mem_congr_right ev).trans (hM.mem_valueOf hS hA hq hp)

include hS hC in
/-- **The exact model-relative membership law**: for every ambient `z`, `z` is in the family
exactly when it is the value of some admissible package. -/
theorem mem_of_defF {A B : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) (hB : M B)
    (h : Sat M (defF S C) (Env.cons A (Env.cons B E))) (z : PSet.{u}) :
    z ∈ B ↔ ¬¬∃ n q p m, M n ∧ M q ∧ M p ∧ M m ∧ IsPureFun A p n ∧ m ≈ succ n ∧
      Sat M C (Env.cons q (Env.cons m envω)) ∧ z ≈ valueOf (M := M) S A q p := by
  have k := (hM.sat_defF hS hC hA).1 h
  constructor
  · intro hz
    exact (hM.memberP_iff hS hA (hM.trans hB hz)).1 ((k z (hM.trans hB hz)).1 hz)
  · intro hz
    have hzM : M z := (hM.stable z).dne (nn_map (fun ⟨_, q, p, _, _, hq, hp, _, _, _, _, ev⟩ =>
      hM.resp ev.symm (hM.valueOf_mem hA hq hp)) hz)
    exact (k z hzM).2 ((hM.memberP_iff hS hA hzM).2 hz)

end SynZF

/-- info: 'PSet.SynZF.defF_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.defF_exists
/-- info: 'PSet.SynZF.mem_of_defF' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.mem_of_defF

end PSet
