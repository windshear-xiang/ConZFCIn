import Vendor.ConZF.Relativize
import Vendor.ConZF.Constr
/-!
The constructible class `N := Constr M` as a model of the axioms of `ZF` other than the
Separation schema, under `SynZF M`. Every construction below uses Separation and Collection
*in `M`*; the corresponding axioms of `N` are conclusions.

The central reusable lemma is the level bound (`level_bound`): a member of `M` all of whose
elements are constructible is included in one level. Its proof sends each element to its least
stage (a fixed native formula `leastF`, functional by ordinal comparison, total by
`exists_minimal` below a supplied successful stage), collects the stages with `M`'s
Collection, keeps the ordinals among them, and takes the successor of their union. The lemma
bounds the elements; it does not say the set itself is constructible, and Power Set
(`powN`) adds the definability step `{y ∈ L_γ : y ⊆ a}`. Replacement (`replN`) relativizes the
native formula to `N`, collects in `M`, separates the constructible outputs, and uses the
bounding level itself as the witness.
-/
universe u

namespace PSet
open Fml CardF LF

/-- `Constr M` is the class defined by `constrF` over `M`. -/
theorem SynZF.constr_iff_definedClass {M : PSet.{u} → Prop} (hM : SynZF M) (x : PSet.{u}) :
    Constr M x ↔ definedClass M constrF x :=
  ⟨fun h => ⟨SynZF.Constr.mem_class hM h, (hM.sat_constrF (SynZF.Constr.mem_class hM h) fun _ => hM.empty).2 h⟩,
   fun ⟨hx, hs⟩ => (hM.sat_constrF hx fun _ => hM.empty).1 hs⟩

namespace LF

/-- `x` lies in the level at `γ`: `∃ A, ordLevelF γ A ∧ x ∈ A`. -/
def inLevelF (x γ : Nat) : Fml :=
  ex (and (rename (fun k => if k = 0 then γ+1 else if k = 1 then 0 else k) ordLevelF) (mem (x+1) 0))

/-- `γ` is the least stage containing `x`. Variables `x = 0, γ = 1`. -/
def leastF : Fml := and (inLevelF 0 1) (all (imp (mem 0 2) (neg (inLevelF 1 0))))

end LF

/-- `x` lies in the level at `γ`. -/
def InLevel (M : PSet.{u} → Prop) (x γ : PSet.{u}) : Prop := ¬¬∃ A, OrdLevel M γ A ∧ x ∈ A

instance {M : PSet.{u} → Prop} {x γ : PSet.{u}} : Stable (InLevel M x γ) := inferInstanceAs (Stable (¬_))

theorem InLevel.congr {M : PSet.{u} → Prop} {x γ γ' : PSet.{u}} (e : γ ≈ γ') (h : InLevel M x γ) : InLevel M x γ' :=
  nn_map (fun ⟨A, ⟨ho, hA⟩, hx⟩ => ⟨A, ⟨ho.resp e, SynZF.level_congr e hA⟩, hx⟩) h

/-- `γ` is the least stage containing `x`. -/
def LeastStage (M : PSet.{u} → Prop) (x γ : PSet.{u}) : Prop := InLevel M x γ ∧ ∀ δ, δ ∈ γ → ¬ InLevel M x δ

/-- The union of a set of ordinals is an ordinal. -/
theorem isOrd_sUnion {S : PSet.{u}} (h : ∀ γ, γ ∈ S → IsOrd γ) : IsOrd (sUnion S) :=
  ⟨fun y hy z hz => Stable.of_nn (mem_sUnion.1 hy) fun ⟨γ, hγ, hyγ⟩ =>
      mem_sUnion.2 (nn_intro ⟨γ, hγ, (h γ hγ).trans y hyγ z hz⟩),
   fun y hy => Stable.of_nn (mem_sUnion.1 hy) fun ⟨γ, hγ, hyγ⟩ => (h γ hγ).mem_trans y hyγ⟩

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem sat_inLevelF (x γ : Nat) {e : Nat → PSet.{u}} (he : ∀ i, M (e i)) :
    Sat M (inLevelF x γ) e ↔ InLevel M (e x) (e γ) := by
  refine sat_ex.trans (nn_congr ⟨fun ⟨A, hA, hs⟩ => ?_, fun ⟨A, hA, hx⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    refine ⟨A, (hM.sat_ordLevelF (he γ) hA (E := fun _ => A) fun _ => hA).1 ?_, h2⟩
    refine (sat_bound bound_ordLevelF fun i hi => ?_).1 ((sat_rename _ _ _).1 h1)
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim
  · have hAM := (hM.level_mem_class hA.2).2
    refine ⟨A, hAM, sat_and.2 ⟨(sat_rename _ _ _).2 ((sat_bound bound_ordLevelF fun i hi => ?_).1
      ((hM.sat_ordLevelF (he γ) hAM (E := fun _ => A) fun _ => hAM).2 hA)), hx⟩⟩
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim

theorem sat_leastF {x γ : PSet.{u}} {e : Nat → PSet.{u}} (hx : M x) (hγ : M γ) (he : ∀ i, M (e i)) :
    Sat M leastF (Env.cons x (Env.cons γ e)) ↔ LeastStage M x γ := by
  have hE := Env.cons_mem hx (Env.cons_mem hγ he)
  refine sat_and.trans (and_congr (hM.sat_inLevelF 0 1 hE) ⟨fun h δ hδ k => ?_, fun h δ _ hδ k => ?_⟩)
  · exact h δ (hM.trans hγ hδ) hδ ((hM.sat_inLevelF 1 0 (Env.cons_mem (hM.trans hγ hδ) hE)).2 k)
  · exact h δ hδ ((hM.sat_inLevelF 1 0 (Env.cons_mem (hM.trans hγ hδ) hE)).1 k)

omit hM in
/-- Least stages are unique, by ordinal comparison. -/
theorem LeastStage.unique {x γ γ' : PSet.{u}} (h : LeastStage M x γ) (h' : LeastStage M x γ') : γ ≈ γ' := by
  have hγ : IsOrd γ := Stable.of_nn h.1 fun ⟨_, ho, _⟩ => ho.1
  have hγ' : IsOrd γ' := Stable.of_nn h'.1 fun ⟨_, ho, _⟩ => ho.1
  refine Stable.of_nn (hγ.trichotomy hγ') fun
    | .inl k => (h'.2 γ k h.1).elim
    | .inr (.inl e) => e
    | .inr (.inr k) => (h.2 γ' k h'.1).elim

/-- Every constructible set has a least stage in the class. -/
theorem leastStage_exists {x : PSet.{u}} (h : Constr M x) : ¬¬∃ γ, M γ ∧ LeastStage M x γ := by
  refine Stable.of_nn h fun ⟨α, A, hα, hA, hx⟩ => ?_
  have hαM := (hM.level_mem_class hA).1
  let S := PSet.sep (fun δ => InLevel M x δ) (succ α)
  have hS : ∀ δ, δ ∈ S ↔ δ ∈ succ α ∧ InLevel M x δ := fun δ => mem_sep fun _ _ e k => k.congr e
  have hαS : α ∈ S := (hS α).2 ⟨self_mem_succ α, nn_intro ⟨A, ⟨hα, hA⟩, hx⟩⟩
  refine nn_map (fun ⟨γ, hγS, hmin⟩ => ?_) (exists_minimal S α hαS)
  have ⟨hγs, hγ⟩ := (hS γ).1 hγS
  exact ⟨γ, hM.trans (hM.succ_mem hαM) hγs, hγ, fun δ hδ k => hmin δ hδ ((hS δ).2 ⟨hα.succ.trans γ hγs δ hδ, k⟩)⟩

/-- **The level bound**: a member of `M` whose elements are all constructible is included in one
level. The set itself need not be constructible. -/
theorem level_bound {B : PSet.{u}} (hB : M B) (hc : ∀ x, x ∈ B → Constr M x) :
    ¬¬∃ γ A, OrdLevel M γ A ∧ ∀ x, x ∈ B → x ∈ A := by
  have he : ∀ i, M (Env.cons B envω i) := Env.cons_mem hB hM.envω_mem
  have hf : ∀ x γ γ', x ∈ Env.cons B envω 0 → M γ → M γ' → Sat M leastF (Env.cons x (Env.cons γ (Env.cons B envω))) →
      Sat M leastF (Env.cons x (Env.cons γ' (Env.cons B envω))) → γ ≈ γ' := fun x γ γ' hx hγ hγ' h1 h2 =>
    LeastStage.unique ((hM.sat_leastF (hM.trans hB hx) hγ he).1 h1) ((hM.sat_leastF (hM.trans hB hx) hγ' he).1 h2)
  refine nn_bind (hM.replM leastF he hf) fun ⟨b, hb, hcol⟩ => ?_
  -- the ordinals among the collected stages
  have he' : ∀ i, M (Env.cons b envω i) := Env.cons_mem hb hM.envω_mem
  let S := PSet.sep (fun z => Sat M (ordF 0) (Env.cons z (Env.cons b envω))) b
  have hSM : M S := hM.sepM (ordF 0) he'
  have hS : ∀ z, z ∈ S ↔ z ∈ b ∧ IsOrd z := fun z =>
    (mem_sep fun _ _ e k => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k).trans
      (and_congr_right fun hz => hM.toTransClass.sat_ordF (Env.cons_mem (hM.trans hb hz) he') 0)
  have hU : IsOrd (PSet.sUnion S) := isOrd_sUnion fun γ hγ => ((hS γ).1 hγ).2
  have hUM : M (succ (PSet.sUnion S)) := hM.succ_mem (hM.sUnion hSM)
  refine nn_map (fun ⟨A, _, hA⟩ => ⟨succ (PSet.sUnion S), A, ⟨hU.succ, hA⟩, fun x hx => ?_⟩) (hM.level_exists hU.succ hUM)
  refine Stable.of_nn (hM.leastStage_exists (hc x hx)) fun ⟨γ, hγM, hl⟩ => ?_
  have hγb : γ ∈ b := hcol x γ hx hγM ((hM.sat_leastF (hM.trans hB hx) hγM he).2 hl)
  have hγo : IsOrd γ := Stable.of_nn hl.1 fun ⟨_, ho, _⟩ => ho.1
  have hγS : γ ∈ S := (hS γ).2 ⟨hγb, hγo⟩
  have hγU : γ ∈ succ (PSet.sUnion S) :=
    hγo.mem_succ_of_subset hU fun z hz => mem_sUnion.2 (nn_intro ⟨γ, hγS, hz⟩)
  exact Stable.of_nn hl.1 fun ⟨C, ⟨_, hC⟩, hxC⟩ => hM.level_mono hU.succ hUM hγU hA hC x hxC

/-- Constructibility of the members of a level definable subset. -/
theorem constr_of_definable {γ A z : PSet.{u}} (hA : OrdLevel M γ A) (hz : Definable A z) : Constr M z :=
  have hγM := (hM.level_mem_class hA.2).1
  nn_map (fun ⟨B, _, hB⟩ => ⟨succ γ, B, hA.1.succ, hB,
      hM.defPow_level_sub hA.1.succ (hM.succ_mem hγM) (self_mem_succ γ) hB hA.2 z (mem_defPow.2 hz)⟩)
    (hM.level_exists hA.1.succ (hM.succ_mem hγM))

/-! ### The axioms of `N` other than Separation -/

/-- Pairing in `N`. -/
theorem upairN {x y : PSet.{u}} (hx : Constr M x) (hy : Constr M y) : Constr M (PSet.upair x y) := by
  have hB : M (PSet.upair x y) := hM.upair (SynZF.Constr.mem_class hM hx) (SynZF.Constr.mem_class hM hy)
  refine Stable.of_nn (hM.level_bound hB fun z hz => Stable.of_nn (mem_upair.1 hz) fun
    | .inl e => hx.congr e.symm
    | .inr e => hy.congr e.symm) fun ⟨γ, A, hA, hsub⟩ => ?_
  refine hM.constr_of_definable hA (nn_intro ⟨2, or (eq 0 1) (eq 0 2), fun i => if i = 0 then x else y,
    by decide, fun i hi => ?_, ext fun z => ?_⟩)
  · rcases i with _ | _ | i
    · exact hsub x (mem_upair_left x y)
    · exact hsub y (mem_upair_right x y)
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim
  · refine ⟨fun hz => mem_dval.2 ⟨hsub z hz, sat_or.2 (mem_upair.1 hz)⟩, fun hz => ?_⟩
    exact mem_upair.2 (sat_or.1 (mem_dval.1 hz).2)

/-- Union in `N`. -/
theorem sUnionN {x : PSet.{u}} (hx : Constr M x) : Constr M (PSet.sUnion x) := by
  refine Stable.of_nn hx fun ⟨γ, A, hγ, hA, hxA⟩ => ?_
  have htA : Trans A := hM.level_trans hγ (hM.level_mem_class hA).1 hA
  refine hM.constr_of_definable ⟨hγ, hA⟩ (nn_intro ⟨1, ex (and (mem 0 2) (mem 1 0)), fun _ => x,
    by decide, fun _ _ => hxA, ext fun z => ?_⟩)
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · refine Stable.of_nn (mem_sUnion.1 hz) fun ⟨y, hyx, hzy⟩ => ?_
    have hyA := htA x hxA y hyx
    exact mem_dval.2 ⟨htA y hyA z hzy, sat_ex.2 (nn_intro ⟨y, hyA, sat_and.2 ⟨hyx, hzy⟩⟩)⟩
  · have ⟨_, hs⟩ := mem_dval.1 hz
    exact mem_sUnion.2 (nn_map (fun ⟨y, _, hs⟩ => ⟨y, (sat_and.1 hs).1, (sat_and.1 hs).2⟩) (sat_ex.1 hs))

/-- Power Set in `N`: the exact internal powerset law. -/
theorem powN {a : PSet.{u}} (ha : Constr M a) :
    ¬¬∃ P, Constr M P ∧ ∀ y, Constr M y → (y ∈ P ↔ ∀ z, z ∈ y → z ∈ a) := by
  have haM := SynZF.Constr.mem_class hM ha
  refine nn_bind (hM.powM haM) fun ⟨Q, hQ, hQs⟩ => ?_
  have he : ∀ i, M (Env.cons Q envω i) := Env.cons_mem hQ hM.envω_mem
  let B := PSet.sep (fun y => Sat M constrF (Env.cons y (Env.cons Q envω))) Q
  have hBM : M B := hM.sepM constrF he
  have hB : ∀ y, y ∈ B ↔ y ∈ Q ∧ Constr M y := fun y =>
    (mem_sep fun _ _ e k => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k).trans
      (and_congr_right fun hy => hM.sat_constrF (hM.trans hQ hy) (Env.cons_mem hQ hM.envω_mem))
  refine nn_map (fun ⟨γ, A, hA, hsub⟩ => ?_) (hM.level_bound hBM fun y hy => ((hB y).1 hy).2)
  have haA : a ∈ A := hsub a ((hB a).2 ⟨(hQs a haM).2 fun _ hz => hz, ha⟩)
  let P := dval A (all (imp (mem 0 1) (mem 0 2))) (fun _ => a)
  have hP : ∀ y, y ∈ P ↔ y ∈ A ∧ ∀ z, z ∈ y → z ∈ a := fun y =>
    mem_dval.trans (and_congr_right fun hy => ⟨fun h z hz => h z (hM.level_trans hA.1 (hM.level_mem_class hA.2).1 hA.2 y hy z hz) hz,
      fun h z _ hz => h z hz⟩)
  refine ⟨P, hM.constr_of_definable hA (nn_intro ⟨1, _, fun _ => a, by decide, fun _ _ => haA, Equiv.refl _⟩),
    fun y hy => (hP y).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩⟩
  exact hsub y ((hB y).2 ⟨(hQs y (SynZF.Constr.mem_class hM hy)).2 h, hy⟩)

/-- Satisfaction in `N` of a native formula is satisfaction in `M` of its relativization. -/
theorem sat_constr_iff (φ : Fml) (e : Nat → PSet.{u}) :
    Sat (Constr M) φ e ↔ Sat M (restrictClass constrF φ) e :=
  (Sat.resp_iff hM.constr_iff_definedClass φ fun _ => Equiv.refl _).trans (sat_restrictClass constrF bound_constrF φ e).symm

/-- Collection in `N`, for a native formula with constructible parameters: a functional relation on
a constructible `a` has all its constructible outputs inside one level. -/
theorem replN (ψ : Fml) {e : Nat → PSet.{u}} (he : ∀ i, Constr M (e i)) {a : PSet.{u}} (ha : Constr M a)
    (hf : ∀ x y y', x ∈ a → Constr M y → Constr M y' → Sat (Constr M) ψ (Env.cons x (Env.cons y e)) →
      Sat (Constr M) ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :
    ¬¬∃ b, Constr M b ∧ ∀ x y, x ∈ a → Constr M y → Sat (Constr M) ψ (Env.cons x (Env.cons y e)) → y ∈ b := by
  have heM : ∀ i, M (e i) := fun i => SynZF.Constr.mem_class hM (he i)
  have haM := SynZF.Constr.mem_class hM ha
  -- the relation in `M`: `y` constructible and `ψ` in `N`; the parameters shift past `a`
  let ψ' : Fml := and (rename Nat.succ constrF) (rename ZFAx.r3 (restrictClass constrF ψ))
  have he' : ∀ i, M (Env.cons a e i) := Env.cons_mem haM heM
  have key : ∀ x y, M y → (Sat M ψ' (Env.cons x (Env.cons y (Env.cons a e))) ↔
      Constr M y ∧ Sat (Constr M) ψ (Env.cons x (Env.cons y e))) := fun x y hy =>
    sat_and.trans (and_congr ((sat_rename _ _ _).trans (hM.sat_constrF hy he'))
      ((sat_rename _ _ _).trans ((Sat.resp_iff (fun _ => Iff.rfl) _ fun i => by
        rcases i with _ | _ | i <;> exact Equiv.refl _).trans (hM.sat_constr_iff ψ _).symm)))
  have hf' : ∀ x y y', x ∈ Env.cons a e 0 → M y → M y' → Sat M ψ' (Env.cons x (Env.cons y (Env.cons a e))) →
      Sat M ψ' (Env.cons x (Env.cons y' (Env.cons a e))) → y ≈ y' := by
    intro x y y' hx hy hy' h1 h2
    have ⟨hcy, hs⟩ := (key x y hy).1 h1
    have ⟨hcy', hs'⟩ := (key x y' hy').1 h2
    exact hf x y y' hx hcy hcy' hs hs'
  refine nn_bind (hM.replM ψ' he' hf') fun ⟨b, hb, hcol⟩ => ?_
  -- separate the constructible outputs and bound them in a level
  let b' := PSet.sep (fun y => Sat M constrF (Env.cons y (Env.cons b envω))) b
  have hb'M : M b' := hM.sepM constrF (Env.cons_mem hb hM.envω_mem)
  have hb' : ∀ y, y ∈ b' ↔ y ∈ b ∧ Constr M y := fun y =>
    (mem_sep fun _ _ e k => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k).trans
      (and_congr_right fun hy => hM.sat_constrF (hM.trans hb hy) (Env.cons_mem hb hM.envω_mem))
  refine nn_map (fun ⟨γ, A, hA, hsub⟩ => ⟨A, hM.constr_of_level hA.1 hA.2, fun x y hx hy hs => ?_⟩)
    (hM.level_bound hb'M fun y hy => ((hb' y).1 hy).2)
  exact hsub y ((hb' y).2 ⟨hcol x y hx (SynZF.Constr.mem_class hM hy) ((key x y (SynZF.Constr.mem_class hM hy)).2 ⟨hy, hs⟩), hy⟩)

/-- `ω` is constructible. -/
theorem omegaN : Constr M PSet.omega := hM.constr_of_ord isOrd_omega hM.omega

/-- The case analysis: every axiom of `ZF` is valid in `N`, given Separation for the instances
that are Separation. -/
theorem valid_cases : ∀ φ, ZF φ → (∀ ψ, φ = ZFAx.sep ψ → Valid (Constr M) φ) → Valid (Constr M) φ := by
  intro φ h hsep e he
  have htr : ∀ {x z : PSet.{u}}, Constr M x → z ∈ x → Constr M z := fun hx hz => SynZF.Constr.trans hM hx hz
  cases h with
  | ext =>
    intro h
    exact ext fun z =>
      ⟨fun hz => (sat_iff.1 (h z (htr (he 0) hz))).1 hz,
       fun hz => (sat_iff.1 (h z (htr (he 1) hz))).2 hz⟩
  | found =>
    intro h
    refine Stable.of_nn (sat_ex.1 h) fun ⟨z, _, hz⟩ => ?_
    refine Stable.of_nn (exists_minimal (e 0) z hz) fun ⟨y, hy, hmin⟩ => ?_
    exact sat_ex.2 (nn_intro ⟨y, htr (he 0) hy, sat_and.2 ⟨hy, fun w _ hw hwx => hmin w hw hwx⟩⟩)
  | pair =>
    exact sat_ex.2 (nn_intro ⟨PSet.upair (e 0) (e 1), hM.upairN (he 0) (he 1),
      sat_and.2 ⟨mem_upair_left _ _, mem_upair_right _ _⟩⟩)
  | union =>
    exact sat_ex.2 (nn_intro ⟨PSet.sUnion (e 0), hM.sUnionN (he 0),
      fun y _ z _ hz hy => mem_sUnion.2 (nn_intro ⟨y, hy, hz⟩)⟩)
  | power =>
    refine Stable.of_nn (hM.powN (he 0)) fun ⟨P, hP, hPs⟩ => ?_
    exact sat_ex.2 (nn_intro ⟨P, hP, fun y hy h => (hPs y hy).2 fun z hz => h z (htr hy hz) hz⟩)
  | inf =>
    refine sat_ex.2 (nn_intro ⟨PSet.omega, hM.omegaN, sat_and.2 ⟨?_, fun y _ hy => ?_⟩⟩)
    · exact sat_ex.2 (nn_intro ⟨PSet.empty, hM.constr_of_ord isOrd_empty hM.empty,
        sat_and.2 ⟨ofNat_mem_omega 0, fun z _ hz => not_mem_empty z hz⟩⟩)
    · refine Stable.of_nn (mem_omega.1 hy) fun ⟨n, e'⟩ => ?_
      refine sat_ex.2 (nn_intro ⟨ofNat (n+1), htr hM.omegaN (ofNat_mem_omega (n+1)),
        sat_and.2 ⟨ofNat_mem_omega (n+1), fun z _ => sat_iff.2 ?_⟩⟩)
      refine mem_succ.trans <| .trans (nn_congr ?_) sat_or.symm
      exact or_congr (mem_congr_right e').symm ⟨fun h => h.trans e'.symm, fun h => h.trans e'⟩
  | sep ψ => exact hsep ψ rfl e he
  | repl ψ =>
    intro hf
    have R2 : ∀ {x y y'}, Sat (Constr M) ψ (Env.cons x (Env.cons y' e)) →
        Sat (Constr M) (rename ZFAx.r2 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) := fun h =>
      (sat_rename ψ ZFAx.r2 _).2
        (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
    have R1' : ∀ {x y y'}, Sat (Constr M) ψ (Env.cons x (Env.cons y e)) →
        Sat (Constr M) (rename ZFAx.r1 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) := fun h =>
      (sat_rename ψ ZFAx.r1 _).2
        (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
    refine Stable.of_nn (hM.replN ψ he (he 0) fun x y y' hx hy hy' h1 h2 =>
      hf x (htr (he 0) hx) hx y hy y' hy' (R1' (y' := y') h1) (R2 (y := y) h2))
      fun ⟨b, hb, hb'⟩ => ?_
    refine sat_ex.2 (nn_intro ⟨b, hb, fun y hy h => ?_⟩)
    refine Stable.of_nn (sat_ex.1 h) fun ⟨x, _, hx⟩ => ?_
    have ⟨hxa, hs⟩ := sat_and.1 hx
    exact hb' x y hxa hy (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _)
      ((sat_rename ψ ZFAx.r3 _).1 hs))

/-- **Validity in `N` of every axiom of `ZF` other than the Separation schema.** -/
theorem valid_nonsep : ∀ φ, ZF φ → (∀ ψ, φ ≠ ZFAx.sep ψ) → Valid (Constr M) φ :=
  fun φ h hns => hM.valid_cases φ h fun ψ e => (hns ψ e).elim

/-- With Separation, every axiom of `ZF` is valid in `N`. -/
theorem valid_of_sep (hsep : ∀ ψ, Valid (Constr M) (ZFAx.sep ψ)) : ∀ φ, ZF φ → Valid (Constr M) φ :=
  fun φ h => hM.valid_cases φ h fun ψ e => e ▸ hsep ψ

end SynZF

/-- info: 'PSet.SynZF.level_bound' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.level_bound
/-- info: 'PSet.SynZF.powN' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.powN
/-- info: 'PSet.SynZF.replN' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.replN
/-- info: 'PSet.SynZF.valid_nonsep' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.valid_nonsep

end PSet
