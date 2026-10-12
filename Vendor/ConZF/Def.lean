import Vendor.ConZF.DefAdapter
import Vendor.ConZF.ScopedCode
/-!
The definable powerset (gate 3 closed). The generic adapter is instantiated with the checked
set-satisfaction and scoped-code formulas: `defPowF := defF setSatF scopedCodeF` (`A, B`;
`Bound 2`). Ambiently, `Definable A z` says `z` is, negatively, `{x ∈ A : φ(x, e)}` for a native
formula `φ` bounded by `n + 1` and an environment with its first `n` entries in `A`, and the
native value `defPow A := sep (Definable A) (powerset A)` has exactly these members.

**Exact correspondence** (`sat_defPowF`): for members `A, B` of a `SynZF` class, `B` satisfies
`defPowF` at `A` exactly when its members are the definable subsets of `A`; hence `defPow A`
is in the class (`defPow_mem`) and is the unique such `B` up to bisimulation. Consequences:
congruence in `A` (`defPow_congr`), absoluteness between classes containing `A` and `B`
(`defPowF_absolute`), `defPow ∅ ≈ {∅}` (`defPow_empty`), `A ∈ defPow A`, `∅ ∈ defPow A`, and for
transitive `A`, `A ⊆ defPow A` and `defPow A` is transitive (`defPow_trans`). Monotonicity of
`defPow` in `A` is not claimed: satisfaction changes with the domain.
-/
universe u

namespace PSet
open Fml CardF RecF AssignF SetSatF DefAdapter

/-- The definable subset `{x ∈ A : φ(x, e)}`. -/
def dval (A : PSet.{u}) (φ : Fml) (e : Nat → PSet.{u}) : PSet.{u} :=
  sep (fun x => Sat (fun z => z ∈ A) φ (Env.cons x e)) A

theorem mem_dval {A x : PSet.{u}} {φ : Fml} {e : Nat → PSet.{u}} :
    x ∈ dval A φ e ↔ x ∈ A ∧ Sat (fun z => z ∈ A) φ (Env.cons x e) :=
  mem_sep fun _ _ e' h => Sat.resp φ (Env.cons_resp e' fun _ => Equiv.refl _) h

/-- **Definable subsets** of `A`. -/
def Definable (A z : PSet.{u}) : Prop :=
  ¬¬∃ (n : Nat) (φ : Fml) (e : Nat → PSet.{u}), Bound (n+1) φ ∧ (∀ i, i < n → e i ∈ A) ∧ z ≈ dval A φ e

instance {A z : PSet.{u}} : Stable (Definable A z) := inferInstanceAs (Stable (¬_))

theorem Definable.congr {A z z' : PSet.{u}} (e : z ≈ z') (h : Definable A z) : Definable A z' :=
  nn_map (fun ⟨n, φ, en, hb, he, ez⟩ => ⟨n, φ, en, hb, he, e.symm.trans ez⟩) h

theorem Definable.subset {A z : PSet.{u}} (h : Definable A z) : ∀ x, x ∈ z → x ∈ A := fun _x hx =>
  Stable.of_nn h fun ⟨_, _, _, _, _, ez⟩ => (mem_dval.1 ((mem_congr_right ez).1 hx)).1

/-- **The native definable powerset.** -/
def defPow (A : PSet.{u}) : PSet.{u} := sep (Definable A) (powerset A)

theorem mem_defPow {A z : PSet.{u}} : z ∈ defPow A ↔ Definable A z :=
  (mem_sep fun _ _ e h => h.congr e).trans ⟨fun h => h.2, fun h => ⟨mem_powerset.2 h.subset, h⟩⟩

theorem IsPureFun.congr_dom {A p n n' : PSet.{u}} (en : n ≈ n') (h : IsPureFun A p n) : IsPureFun A p n' :=
  ⟨fun q hq => nn_map (fun ⟨i, v, hi, hv, e⟩ => ⟨i, v, (mem_congr_right en).1 hi, hv, e⟩) (h.1 q hq),
   fun i hi => h.2.1 i ((mem_congr_right en).2 hi), h.2.2⟩

/-- The instantiated family formula. -/
def defPowF : Fml := defF setSatF scopedCodeF

set_option maxRecDepth 200000 in
theorem bound_defPowF : Bound 2 defPowF := by decide

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem enc_mem (φ : Fml) : M (enc φ) := by
  have hn : ∀ k, M (ofNat k) := TransClass.ofNat_mem hM.empty hM.succ_mem
  induction φ with
  | mem i j => exact hM.pair (hn _) (hM.pair (hn i) (hn j))
  | eq i j => exact hM.pair (hn _) (hM.pair (hn i) (hn j))
  | fls => exact hM.pair (hn _) hM.empty
  | imp _ _ ih1 ih2 => exact hM.pair (hn _) (hM.pair ih1 ih2)
  | all _ ih => exact hM.pair (hn _) ih

/-- The value of a native package is the definable subset. -/
theorem valueOf_pack {A : PSet.{u}} (hA : M A) {φ : Fml} {n : Nat} {e : Nat → PSet.{u}} (hb : Bound (n+1) φ)
    (he : ∀ i, i < n → e i ∈ A) :
    valueOf (M := M) setSatF A (enc φ) (pack n e) ≈ dval A φ e := by
  have hq := hM.enc_mem φ
  have hp := hM.pack_mem n fun i hi => hM.trans hA (he i hi)
  refine ext fun x => (hM.mem_valueOf bound_setSatF hA hq hp).trans (Iff.trans ?_ mem_dval.symm)
  refine and_congr_right fun hxA => ?_
  have he' : ∀ i, i < n + 1 → Env.cons x e i ∈ A := fun i hi => by
    cases i with
    | zero => exact hxA
    | succ i => exact he i (Nat.lt_of_succ_lt_succ hi)
  constructor
  · intro h
    refine Stable.of_nn h fun ⟨t, _, hc, hs⟩ => ?_
    have et : t ≈ pack (n+1) (Env.cons x e) := hc.unique (isCons_pack n)
    have hs' := Sat.resp setSatF (Env.cons_resp (Equiv.refl _) (Env.cons_resp (Equiv.refl _) (Env.cons_resp et fun _ => Equiv.refl _))) hs
    exact ((hM.setSat_correct hA φ (n+1) (Env.cons x e) he').1 hs').2
  · intro h
    exact nn_intro ⟨pack (n+1) (Env.cons x e), hM.pack_mem (n+1) fun i hi => hM.trans hA (he' i hi), isCons_pack n,
      (hM.setSat_correct hA φ (n+1) (Env.cons x e) he').2 ⟨hb, h⟩⟩

/-- Values respect bisimulation of the code and the package. -/
theorem valueOf_congr {A q q' p p' : PSet.{u}} (hA : M A) (hq : M q) (hq' : M q') (hp : M p) (hp' : M p')
    (eqq : q ≈ q') (ep : p ≈ p') : valueOf (M := M) setSatF A q p ≈ valueOf (M := M) setSatF A q' p' := by
  have key : ∀ {q q' p p' : PSet.{u}}, q ≈ q' → p ≈ p' → ∀ x, EvalP M setSatF A q p x → EvalP M setSatF A q' p' x :=
    fun eqq ep x h => nn_map (fun ⟨t, ht, hc, hs⟩ => ⟨t, ht, hc.congr_tail ep,
      Sat.resp setSatF (Env.cons_resp (Equiv.refl _) (Env.cons_resp eqq fun _ => Equiv.refl _)) hs⟩) h
  refine ext fun x => (hM.mem_valueOf bound_setSatF hA hq hp).trans (Iff.trans ?_ (hM.mem_valueOf bound_setSatF hA hq' hp').symm)
  exact and_congr Iff.rfl ⟨key eqq ep x, key eqq.symm ep.symm x⟩

/-- An admissible package denotes a definable subset, and conversely. -/
theorem package_iff_definable {A z : PSet.{u}} (hA : M A) :
    (¬¬∃ n q p m, M n ∧ M q ∧ M p ∧ M m ∧ IsPureFun A p n ∧ m ≈ succ n ∧
      Sat M scopedCodeF (Env.cons q (Env.cons m envω)) ∧ z ≈ valueOf (M := M) setSatF A q p) ↔ Definable A z := by
  constructor
  · intro h
    refine nn_bind h fun ⟨n, q, p, m, hn, hq, hp, hm, hf, hsm, hc, ez⟩ => ?_
    refine nn_bind ((hM.scopedCode_correct hq hm hM.envω_mem).1 hc) fun ⟨k, φ, em, eqq, hb⟩ => ?_
    cases k with
    | zero => exact (not_mem_empty n ((mem_congr_right (hsm.symm.trans em)).1 (self_mem_succ n))).elim
    | succ k =>
      have en : n ≈ ofNat k := succ_inj (hsm.symm.trans em)
      have ha : IsAssign A p (ofNat k) := ⟨ofNat_mem_omega k, hf.congr_dom en⟩
      refine nn_map (fun ⟨e, ep, he⟩ => ⟨k, φ, e, hb, he, ?_⟩) (exists_pack ha)
      have hpk := hM.pack_mem k fun i hi => hM.trans hA (he i hi)
      exact ez.trans ((hM.valueOf_congr hA hq (hM.enc_mem φ) hp hpk eqq ep).trans (hM.valueOf_pack hA hb he))
  · intro h
    refine nn_map (fun ⟨n, φ, e, hb, he, ez⟩ => ?_) h
    have hq := hM.enc_mem φ
    have hp := hM.pack_mem n fun i hi => hM.trans hA (he i hi)
    have hn : M (ofNat n) := hM.trans hM.omega (ofNat_mem_omega n)
    have hm : M (ofNat (n+1)) := hM.trans hM.omega (ofNat_mem_omega (n+1))
    exact ⟨ofNat n, enc φ, pack n e, ofNat (n+1), hn, hq, hp, hm, (isAssign_pack n he).2, Equiv.refl _,
      (hM.scopedCode_correct hq hm hM.envω_mem).2 (nn_intro ⟨n+1, φ, Equiv.refl _, Equiv.refl _, hb⟩),
      ez.trans (hM.valueOf_pack hA hb he).symm⟩

/-- **Exact correspondence**: `B` is the definable family of `A` in the class exactly when its
members are the definable subsets of `A`. -/
theorem sat_defPowF {A B : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) (hB : M B) :
    Sat M defPowF (Env.cons A (Env.cons B E)) ↔ ∀ z, z ∈ B ↔ Definable A z := by
  constructor
  · intro h z
    exact (hM.mem_of_defF bound_setSatF bound_scopedCodeF hA hB h z).trans (hM.package_iff_definable hA)
  · intro h
    refine (hM.sat_defF bound_setSatF bound_scopedCodeF hA).2 fun z hz => ?_
    exact (h z).trans ((hM.package_iff_definable hA).symm.trans (hM.memberP_iff bound_setSatF hA hz).symm)

/-- **Internal closure**: the native definable powerset of a member is a member. -/
theorem defPow_mem {A : PSet.{u}} (hA : M A) : M (defPow A) := by
  refine (hM.stable _).dne (nn_map (fun ⟨B, hB, hs⟩ => ?_) (hM.defF_exists bound_setSatF bound_scopedCodeF hA))
  have h := (hM.sat_defPowF hA hB).1 (hs envω hM.envω_mem)
  exact hM.resp (ext fun z => (h z).trans mem_defPow.symm) hB

/-- The definable powerset satisfies the family formula. -/
theorem sat_defPowF_defPow {A : PSet.{u}} {E : Nat → PSet.{u}} (hA : M A) :
    Sat M defPowF (Env.cons A (Env.cons (defPow A) E)) :=
  (hM.sat_defPowF hA (hM.defPow_mem hA)).2 fun _ => mem_defPow

end SynZF

/-! ### Structural laws -/

theorem Definable.congr_dom {A A' z : PSet.{u}} (e : A ≈ A') (h : Definable A z) : Definable A' z := by
  refine nn_map (fun ⟨n, φ, en, hb, he, ez⟩ => ⟨n, φ, en, hb, fun i hi => (mem_congr_right e).1 (he i hi), ez.trans ?_⟩) h
  refine ext fun x => mem_dval.trans (Iff.trans ?_ mem_dval.symm)
  exact and_congr (mem_congr_right e) (Sat.resp_iff (fun _ => mem_congr_right e) φ fun _ => Equiv.refl _)

theorem defPow_congr {A A' : PSet.{u}} (e : A ≈ A') : defPow A ≈ defPow A' :=
  ext fun _ => mem_defPow.trans ⟨Definable.congr_dom e, Definable.congr_dom e.symm⟩ |>.trans mem_defPow.symm

/-- **Absoluteness**: classes containing `A` and `B` agree on the family formula. -/
theorem SynZF.defPowF_absolute {M M' : PSet.{u} → Prop} (hM : SynZF M) (hM' : SynZF M') {A B : PSet.{u}}
    {E E' : Nat → PSet.{u}} (hA : M A) (hB : M B) (hA' : M' A) (hB' : M' B) :
    Sat M defPowF (Env.cons A (Env.cons B E)) ↔ Sat M' defPowF (Env.cons A (Env.cons B E')) :=
  (hM.sat_defPowF hA hB).trans (hM'.sat_defPowF hA' hB').symm

theorem empty_mem_defPow (A : PSet.{u}) : empty ∈ defPow A :=
  mem_defPow.2 (nn_intro ⟨0, .fls, fun _ => empty, trivial, fun _ h => (Nat.not_lt_zero _ h).elim,
    ext fun x => ⟨fun h => (not_mem_empty x h).elim, fun h => (mem_dval.1 h).2.elim⟩⟩)

theorem self_mem_defPow (A : PSet.{u}) : A ∈ defPow A :=
  mem_defPow.2 (nn_intro ⟨0, .eq 0 0, fun _ => empty, ⟨Nat.one_pos, Nat.one_pos⟩, fun _ h => (Nat.not_lt_zero _ h).elim,
    ext fun x => ⟨fun h => mem_dval.2 ⟨h, Equiv.refl x⟩, fun h => (mem_dval.1 h).1⟩⟩)

/-- `defPow ∅ ≈ {∅}`. -/
theorem defPow_empty : defPow empty.{u} ≈ singleton empty :=
  ext fun _z => ⟨fun h => mem_singleton.2 (ext fun x => ⟨fun hx => (not_mem_empty x ((mem_defPow.1 h).subset x hx)).elim,
      fun hx => (not_mem_empty x hx).elim⟩),
    fun h => (mem_congr_left (mem_singleton.1 h)).2 (empty_mem_defPow _)⟩

/-- For a transitive `A`, every member of `A` is definable with itself as parameter. -/
theorem mem_defPow_of_trans {A y : PSet.{u}} (hA : Trans A) (hy : y ∈ A) : y ∈ defPow A :=
  mem_defPow.2 (nn_intro ⟨1, .mem 0 1, fun _ => y, ⟨Nat.zero_lt_succ _, Nat.lt_succ_self _⟩,
    fun _ _ => hy, ext fun x => ⟨fun hx => mem_dval.2 ⟨hA y hy x hx, hx⟩, fun hx => (mem_dval.1 hx).2⟩⟩)

/-- For a transitive `A`, `defPow A` is transitive. -/
theorem defPow_trans {A : PSet.{u}} (hA : Trans A) : Trans (defPow A) := fun _y hy z hz =>
  mem_defPow_of_trans hA ((mem_defPow.1 hy).subset z hz)

/-- info: 'PSet.SynZF.sat_defPowF' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.sat_defPowF
/-- info: 'PSet.SynZF.defPow_mem' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.defPow_mem
/-- info: 'PSet.bound_defPowF' does not depend on any axioms -/
#guard_msgs in #print axioms bound_defPowF

end PSet
