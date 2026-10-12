import Vendor.ConZF.Def
/-!
Relational level histories (gate 4, the hierarchy recurrence checkpoint). A history on an
ordinal `α` is a pure function `h` on `succ α` satisfying the uniform recurrence
`h(β) = ⋃_{γ ∈ β} defPow (h γ)` at every row (`lhistF`, ambient `IsLHist`). No case distinction
on the kind of the ordinal enters the formula: the zero, successor, and limit laws are theorems.

Overlap compatibility (`lhist_agree`): two histories agree at every ordinal where both are
defined, by `∈`-induction. Existence (`lhist_exists`): by `∈`-induction on `α` in the ambient
universe, collecting the histories of the members of `α` with the internal Replacement of the
class, taking their union, and adjoining the new row, itself the union of the definable
powersets of the earlier rows, collected by a second Replacement. Levels (`levelF`, `Level`):
exist and are unique for every ordinal of the class, are transitive and increasing, and satisfy
`L_0 = ∅`, `L_{succ β} = defPow L_β`, and `L_λ = ⋃_{β<λ} L_β` at limits.
-/
universe u

namespace PSet
open Fml CardF RecF AssignF

namespace LF

/-- A pure function on `d` (no codomain): pure pairs with first component in `d`, total on `d`,
functional. Variables `f, d`. -/
def mapF (f d : Nat) : Fml :=
  and (all (imp (mem 0 (f+1)) (ex (and (mem 0 (d+2)) (ex (pairF 2 1 0))))))
    (and (all (imp (mem 0 (d+1)) (ex (pairMemF (f+2) 1 0))))
      (all (all (all (imp (pairMemF (f+3) 2 1) (imp (pairMemF (f+3) 2 0) (eq 1 0)))))))

/-- The recurrence at a row: `∀ β v, ⟨β, v⟩ ∈ h → ∀ x (x ∈ v ↔ ∃ γ ∈ β, ∃ u w, ⟨γ, u⟩ ∈ h ∧
defPowF u w ∧ x ∈ w)`. Variables `h`. -/
def recF (h : Nat) : Fml :=
  all (all (imp (pairMemF (h+2) 1 0)
    (all (iff (mem 0 1)
      (ex (and (mem 0 3) (ex (ex (and (pairMemF (h+6) 2 1) (and (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else 0) defPowF) (mem 3 0)))))))))))

/-- A history on `α`: pure function on `succ α` with the recurrence. Variables `α = 0, h = 1`. -/
def lhistF : Fml := and (ex (and (succF 0 1) (mapF 2 0))) (recF 1)

/-- `A` is the level at `α`: some history on `α` has row `⟨α, A⟩`. Variables `α = 0, A = 1`. -/
def levelF : Fml := ex (and (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else 0) lhistF) (pairMemF 0 1 2))

set_option maxRecDepth 200000 in
theorem bound_lhistF : Bound 2 lhistF := by decide

set_option maxRecDepth 200000 in
theorem bound_levelF : Bound 2 levelF := by decide

end LF

open LF

/-- Ambient: a pure function on `d`. -/
def IsMap (h d : PSet.{u}) : Prop :=
  (∀ q, q ∈ h → ¬¬∃ i v, i ∈ d ∧ q ≈ pair i v) ∧ (∀ i, i ∈ d → ¬¬∃ v, pair i v ∈ h) ∧
  (∀ i v v', pair i v ∈ h → pair i v' ∈ h → v ≈ v')

/-- Ambient: the recurrence at every row. -/
def IsRec (h : PSet.{u}) : Prop :=
  ∀ β v, pair β v ∈ h → ∀ x, x ∈ v ↔ ¬¬∃ γ, γ ∈ β ∧ ¬¬∃ u, pair γ u ∈ h ∧ x ∈ defPow u

/-- Ambient: a history on `α`. -/
def IsLHist (α h : PSet.{u}) : Prop := IsMap h (succ α) ∧ IsRec h

instance {h d : PSet.{u}} : Stable (IsMap h d) := inferInstanceAs (Stable (_ ∧ _ ∧ _))
instance {h : PSet.{u}} : Stable (IsRec h) := inferInstanceAs (Stable (∀ _ _, _ → ∀ _, _ ↔ ¬_))
instance {α h : PSet.{u}} : Stable (IsLHist α h) := inferInstanceAs (Stable (_ ∧ _))

theorem IsMap.congr_dom {h d d' : PSet.{u}} (e : d ≈ d') (m : IsMap h d) : IsMap h d' :=
  ⟨fun q hq => nn_map (fun ⟨i, v, hi, e'⟩ => ⟨i, v, (mem_congr_right e).1 hi, e'⟩) (m.1 q hq),
   fun i hi => m.2.1 i ((mem_congr_right e).2 hi), m.2.2⟩

/-- The domain of a map is determined: first components are exactly the members of `d`. -/
theorem IsMap.dom_mem {h d i v : PSet.{u}} (m : IsMap h d) (hv : pair i v ∈ h) : i ∈ d :=
  Stable.of_nn (m.1 _ hv) fun ⟨_, _, hi, e⟩ => (mem_congr_left (pair_inj e).1).2 hi

namespace TransClass
variable {M : PSet.{u} → Prop} (hN : TransClass M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hN hE

theorem sat_mapF (f d : Nat) : Sat M (mapF f d) E ↔ IsMap (E f) (E d) := by
  refine sat_and.trans (and_congr ?_ (sat_and.trans (and_congr (hN.sat_totalF hE f d) (hN.sat_funcF hE f))))
  constructor
  · intro h q hq
    refine Stable.of_nn (sat_ex.1 (h q (hN.trans (hE f) hq) hq)) fun ⟨i, hi, hs⟩ => ?_
    have ⟨hin, hs⟩ := sat_and.1 hs
    refine Stable.of_nn (sat_ex.1 hs) fun ⟨v, hv, hs⟩ => ?_
    exact nn_intro ⟨i, v, hin, (hN.sat_pairF (Env.cons_mem hv (Env.cons_mem hi (Env.cons_mem (hN.trans (hE f) hq) hE))) 2 1 0).1 hs⟩
  · intro h q hq hq'
    refine sat_ex.2 (nn_bind (h q hq') fun ⟨i, v, hin, e'⟩ => ?_)
    have ⟨hi, hv⟩ := hN.of_pair_mem (hE f) ((mem_congr_left e').1 hq')
    exact nn_intro ⟨i, hi, sat_and.2 ⟨hin, sat_ex.2 (nn_intro ⟨v, hv,
      (hN.sat_pairF (Env.cons_mem hv (Env.cons_mem hi (Env.cons_mem hq hE))) 2 1 0).2 e'⟩)⟩⟩

end TransClass

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- The family formula, renamed to slots `1, 0`, at a member `u` and a member `w`. -/
theorem sat_defPowF_ren {u w : PSet.{u}} {E : Nat → PSet.{u}} (hu : M u) (hw : M w) :
    Sat M (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else 0) defPowF) (Env.cons w (Env.cons u E)) ↔
      ∀ z, z ∈ w ↔ Definable u z :=
  (sat_rename _ _ _).trans ((sat_bound bound_defPowF (e' := Env.cons u (Env.cons w envω)) fun i hi => by
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim).trans (hM.sat_defPowF hu hw))

/-- The inner block of the recurrence at `u`: some row `⟨γ, u⟩` of `h` and some family member
of `u` containing `x`; exactly `⟨γ, u⟩ ∈ h` and `x ∈ defPow u`. -/
theorem sat_recInner (j : Nat) {u γ x v β : PSet.{u}} {E : Nat → PSet.{u}} (hu : M u) (hγ : M γ) (hx : M x) (hv : M v)
    (hβ : M β) (hE : ∀ i, M (E i)) :
    Sat M (ex (and (pairMemF (j+6) 2 1) (and (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else 0) defPowF) (mem 3 0))))
      (Env.cons u (Env.cons γ (Env.cons x (Env.cons v (Env.cons β E))))) ↔
      PSet.pair γ u ∈ E j ∧ x ∈ defPow u := by
  have hT := hM.toTransClass
  have hE6 : ∀ i, M (Env.cons u (Env.cons γ (Env.cons x (Env.cons v (Env.cons β E)))) i) :=
    Env.cons_mem hu (Env.cons_mem hγ (Env.cons_mem hx (Env.cons_mem hv (Env.cons_mem hβ hE))))
  refine sat_ex.trans ⟨fun hk => Stable.of_nn hk fun ⟨w, hw, hs⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
  · have hE7 := Env.cons_mem hw hE6
    have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h2, h3⟩ := sat_and.1 h2
    exact ⟨(hT.sat_pairMemF hE7 (j+6) 2 1).1 h1, mem_defPow.2 (((hM.sat_defPowF_ren hu hw).1 h2 x).1 h3)⟩
  · have hw := hM.defPow_mem hu
    have hE7 := Env.cons_mem hw hE6
    exact nn_intro ⟨defPow u, hw, sat_and.2 ⟨(hT.sat_pairMemF hE7 (j+6) 2 1).2 h1, sat_and.2
      ⟨(hM.sat_defPowF_ren hu hw).2 fun _ => mem_defPow, h2⟩⟩⟩

/-- **The recurrence bridge.** -/
theorem sat_recF (j : Nat) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i)) :
    Sat M (recF j) E ↔ IsRec (E j) := by
  have hT := hM.toTransClass
  have hh : M (E j) := hE j
  -- the body at a row `⟨β, v⟩` and a point `x` in the class
  have body : ∀ {β v x : PSet.{u}}, M β → M v → M x →
      (Sat M (ex (and (mem 0 3) (ex (ex (and (pairMemF (j+6) 2 1)
        (and (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else 0) defPowF) (mem 3 0)))))))
        (Env.cons x (Env.cons v (Env.cons β E))) ↔
      ¬¬∃ γ, γ ∈ β ∧ ¬¬∃ u, PSet.pair γ u ∈ E j ∧ x ∈ defPow u) := by
    intro β v x hβ hv hx
    have hE4 := Env.cons_mem hx (Env.cons_mem hv (Env.cons_mem hβ hE))
    refine sat_ex.trans (nn_congr ⟨fun ⟨γ, hγ, hs⟩ => ?_, fun ⟨γ, hγβ, k'⟩ => ?_⟩)
    · have ⟨h1, h2⟩ := sat_and.1 hs
      refine ⟨γ, h1, nn_map (fun ⟨u, hu, hs'⟩ => ⟨u, (hM.sat_recInner j hu hγ hx hv hβ hE).1 hs'⟩) (sat_ex.1 h2)⟩
    · have hγ := hM.trans hβ hγβ
      refine ⟨γ, hγ, sat_and.2 ⟨hγβ, sat_ex.2 (nn_map (fun ⟨u, hu, hxu⟩ => ?_) k')⟩⟩
      have huM := (hT.of_pair_mem hh hu).2
      exact ⟨u, huM, (hM.sat_recInner j huM hγ hx hv hβ hE).2 ⟨hu, hxu⟩⟩
  constructor
  · intro hs β v hβv x
    have ⟨hβ, hv⟩ := hT.of_pair_mem hh hβv
    have hE3 := Env.cons_mem hv (Env.cons_mem hβ hE)
    have hrow := (hT.sat_pairMemF hE3 (j+2) 1 0).2 hβv
    constructor
    · intro hx
      have hx' := hM.trans hv hx
      exact (body hβ hv hx').1 ((sat_iff.1 (hs β hβ v hv hrow x hx')).1 hx)
    · intro hx
      have hxM : M x := (hM.stable x).dne (nn_bind hx fun ⟨_, _, h'⟩ => nn_map (fun ⟨u, hu, hxu⟩ =>
        hM.trans (hM.defPow_mem (hT.of_pair_mem hh hu).2) hxu) h')
      exact (sat_iff.1 (hs β hβ v hv hrow x hxM)).2 ((body hβ hv hxM).2 hx)
  · intro hr β hβ v hv hβv x hx
    have hE3 := Env.cons_mem hv (Env.cons_mem hβ hE)
    have hβv' := (hT.sat_pairMemF hE3 (j+2) 1 0).1 hβv
    exact sat_iff.2 ((hr β v hβv' x).trans (body hβ hv hx).symm)

/-- **The history bridge.** -/
theorem sat_lhistF {α h : PSet.{u}} {E : Nat → PSet.{u}} (hα : M α) (hh : M h) (hE : ∀ i, M (E i)) :
    Sat M lhistF (Env.cons α (Env.cons h E)) ↔ IsLHist α h := by
  have hT := hM.toTransClass
  have hE2 : ∀ i, M (Env.cons α (Env.cons h E) i) := Env.cons_mem hα (Env.cons_mem hh hE)
  refine sat_and.trans (and_congr ⟨fun hs => ?_, fun hm => ?_⟩ ?_)
  · refine Stable.of_nn (sat_ex.1 hs) fun ⟨d, hd, hs⟩ => ?_
    have ⟨h1, h2⟩ := sat_and.1 hs
    have hE3 := Env.cons_mem hd hE2
    exact ((hT.sat_mapF hE3 2 0).1 h2).congr_dom ((hT.sat_succF hE3 0 1).1 h1)
  · have hE3 := Env.cons_mem (hM.succ_mem hα) hE2
    exact sat_ex.2 (nn_intro ⟨succ α, hM.succ_mem hα, sat_and.2 ⟨(hT.sat_succF hE3 0 1).2 (Equiv.refl _),
      (hT.sat_mapF hE3 2 0).2 hm⟩⟩)
  · exact hM.sat_recF 1 hE2

/-- Ambient: `A` is the level at `α` in the class. -/
def Level (M : PSet.{u} → Prop) (α A : PSet.{u}) : Prop :=
  ¬¬∃ h, M h ∧ IsLHist α h ∧ PSet.pair α A ∈ h

instance {α A : PSet.{u}} : Stable (Level M α A) := inferInstanceAs (Stable (¬_))

/-- **The level bridge.** -/
theorem sat_levelF {α A : PSet.{u}} {E : Nat → PSet.{u}} (hα : M α) (hA : M A) (hE : ∀ i, M (E i)) :
    Sat M levelF (Env.cons α (Env.cons A E)) ↔ Level M α A := by
  have hT := hM.toTransClass
  have hE2 : ∀ i, M (Env.cons α (Env.cons A E) i) := Env.cons_mem hα (Env.cons_mem hA hE)
  have key : ∀ h, M h → (Sat M (rename (fun k => if k = 0 then 1 else if k = 1 then 0 else 0) lhistF)
      (Env.cons h (Env.cons α (Env.cons A E))) ↔ IsLHist α h) := by
    intro h hh
    refine (sat_rename _ _ _).trans (Iff.trans ?_ (hM.sat_lhistF hα hh (E := fun _ => h) fun _ => hh))
    refine Sat.resp_iff (fun _ => Iff.rfl) _ fun i => ?_
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact Equiv.refl _
  refine sat_ex.trans (nn_congr ⟨fun ⟨h, hh, hs⟩ => ?_, fun ⟨h, hh, hl, hr⟩ => ?_⟩)
  · have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨h, hh, (key h hh).1 h1, (hT.sat_pairMemF (Env.cons_mem hh hE2) 0 1 2).1 h2⟩
  · exact ⟨h, hh, sat_and.2 ⟨(key h hh).2 hl, (hT.sat_pairMemF (Env.cons_mem hh hE2) 0 1 2).2 hr⟩⟩

end SynZF

/-! ### Overlap agreement -/

/-- The rows of a history are transitive ordinals' worth of indices: a row index is in the
domain, and members of row indices are row indices. -/
theorem IsLHist.mem_dom {α h β v : PSet.{u}} (hl : IsLHist α h) (hr : PSet.pair β v ∈ h) : β ∈ succ α :=
  hl.1.dom_mem hr

/-- **Overlap agreement**: two histories on ordinals agree at every common index. -/
theorem lhist_agree {α α' h h' : PSet.{u}} (hα : IsOrd α) (hα' : IsOrd α') (hl : IsLHist α h) (hl' : IsLHist α' h') :
    ∀ γ u u', PSet.pair γ u ∈ h → PSet.pair γ u' ∈ h' → u ≈ u' := by
  intro γ
  refine mem_induction (P := fun γ => ∀ u u', PSet.pair γ u ∈ h → PSet.pair γ u' ∈ h' → u ≈ u') (fun γ ih u u' hu hu' => ?_) γ
  refine ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · refine (hl'.2 γ u' hu' x).2 (nn_bind ((hl.2 γ u hu x).1 hx) fun ⟨δ, hδ, k⟩ => nn_bind k fun ⟨w, hw, hxw⟩ => ?_)
    have hδ' : δ ∈ succ α' := hα'.succ.trans _ (hl'.mem_dom hu') δ hδ
    refine nn_map (fun ⟨w', hw'⟩ => ⟨δ, hδ, nn_intro ⟨w', hw', (mem_congr_right (defPow_congr (ih δ hδ w w' hw hw'))).1 hxw⟩⟩)
      (hl'.1.2.1 δ hδ')
  · refine (hl.2 γ u hu x).2 (nn_bind ((hl'.2 γ u' hu' x).1 hx) fun ⟨δ, hδ, k⟩ => nn_bind k fun ⟨w', hw', hxw⟩ => ?_)
    have hδ' : δ ∈ succ α := hα.succ.trans _ (hl.mem_dom hu) δ hδ
    refine nn_map (fun ⟨w, hw⟩ => ⟨δ, hδ, nn_intro ⟨w, hw, (mem_congr_right (defPow_congr (ih δ hδ w w' hw hw'))).2 hxw⟩⟩)
      (hl.1.2.1 δ hδ')

/-- Histories on the same ordinal are equal. -/
theorem lhist_unique {α h h' : PSet.{u}} (hα : IsOrd α) (hl : IsLHist α h) (hl' : IsLHist α h') : h ≈ h' := by
  have ag := lhist_agree hα hα hl hl'
  have ag' := lhist_agree hα hα hl' hl
  refine ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · refine Stable.of_nn (hl.1.1 q hq) fun ⟨γ, u, hγ, e⟩ => ?_
    have hu : PSet.pair γ u ∈ h := (mem_congr_left e).1 hq
    refine Stable.of_nn (hl'.1.2.1 γ hγ) fun ⟨u', hu'⟩ => ?_
    exact (mem_congr_left (e.trans (pair_congr (Equiv.refl _) (ag γ u u' hu hu')))).2 hu'
  · refine Stable.of_nn (hl'.1.1 q hq) fun ⟨γ, u, hγ, e⟩ => ?_
    have hu : PSet.pair γ u ∈ h' := (mem_congr_left e).1 hq
    refine Stable.of_nn (hl.1.2.1 γ hγ) fun ⟨u', hu'⟩ => ?_
    exact (mem_congr_left (e.trans (pair_congr (Equiv.refl _) (ag' γ u u' hu hu')))).2 hu'

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

/-- **Existence of histories**, by `∈`-induction on the ordinal in the ambient universe. -/
theorem lhist_exists : ∀ α : PSet.{u}, IsOrd α → M α → ¬¬∃ h, M h ∧ IsLHist α h := by
  have hT := hM.toTransClass
  refine mem_induction (P := fun α => IsOrd α → M α → ¬¬∃ h, M h ∧ IsLHist α h) fun α ih hα hαM => ?_
  -- 1. collect the histories of the members of `α`
  let e1 : Nat → PSet.{u} := Env.cons α envω
  have he1 : ∀ i, M (e1 i) := Env.cons_mem hαM hM.envω_mem
  have hfun : ∀ x y y', x ∈ e1 0 → M y → M y' → Sat M lhistF (Env.cons x (Env.cons y e1)) →
      Sat M lhistF (Env.cons x (Env.cons y' e1)) → y ≈ y' := fun x y y' hx hy hy' h1 h2 =>
    lhist_unique (hα.mem hx) ((hM.sat_lhistF (hM.trans hαM hx) hy he1).1 h1) ((hM.sat_lhistF (hM.trans hαM hx) hy' he1).1 h2)
  refine nn_bind (hM.replM lhistF he1 hfun) fun ⟨b, hb, hbs⟩ => ?_
  -- 2. the set of histories of members of `α`, and their union `U`
  let e2 : Nat → PSet.{u} := Env.cons b (Env.cons α envω)
  have he2 : ∀ i, M (e2 i) := Env.cons_mem hb he1
  let ψ : Fml := ex (and (mem 0 3) lhistF)
  have keyψ : ∀ h, M h → (Sat M ψ (Env.cons h e2) ↔ ¬¬∃ β, β ∈ α ∧ IsLHist β h) := by
    intro h hh
    have he3 := Env.cons_mem hh he2
    refine sat_ex.trans ⟨fun k => nn_map (fun ⟨β, hβ, hs⟩ => ?_) k, fun k => nn_map (fun ⟨β, hβα, hl⟩ => ?_) k⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      exact ⟨β, h1, (hM.sat_lhistF hβ hh he2).1 h2⟩
    · have hβ := hM.trans hαM hβα
      exact ⟨β, hβ, sat_and.2 ⟨hβα, (hM.sat_lhistF hβ hh he2).2 hl⟩⟩
  have hψ : ∀ h h' : PSet.{u}, h ≈ h' → Sat M ψ (Env.cons h e2) → Sat M ψ (Env.cons h' e2) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  let B := sep (fun h => Sat M ψ (Env.cons h e2)) b
  have hB : M B := hM.sepM ψ he2
  have memB : ∀ h, h ∈ B → M h ∧ ¬¬∃ β, β ∈ α ∧ IsLHist β h := fun h hh =>
    have hhM := hM.trans hb ((mem_sep hψ).1 hh).1
    ⟨hhM, (keyψ h hhM).1 ((mem_sep hψ).1 hh).2⟩
  have inB : ∀ β h, β ∈ α → M h → IsLHist β h → h ∈ B := fun β h hβ hh hl =>
    (mem_sep hψ).2 ⟨hbs β h hβ hh ((hM.sat_lhistF (hM.trans hαM hβ) hh he1).2 hl), (keyψ h hh).2 (nn_intro ⟨β, hβ, hl⟩)⟩
  let U := PSet.sUnion B
  have hU : M U := hM.sUnion hB
  -- rows of `U`
  have rowU : ∀ q, q ∈ U → ¬¬∃ β h, β ∈ α ∧ IsLHist β h ∧ h ∈ B ∧ q ∈ h := fun q hq =>
    nn_bind (mem_sUnion.1 hq) fun ⟨h, hh, hqh⟩ => nn_map (fun ⟨β, hβ, hl⟩ => ⟨β, h, hβ, hl, hh, hqh⟩) (memB h hh).2
  have succ_sub : ∀ {β γ : PSet.{u}}, β ∈ α → γ ∈ succ β → γ ∈ α := fun {β γ} hβ hγ =>
    Stable.of_nn (mem_succ.1 hγ) fun
      | .inl h' => hα.trans β hβ γ h'
      | .inr e' => (mem_congr_left e').2 hβ
  have pureU : ∀ q, q ∈ U → ¬¬∃ γ v, γ ∈ α ∧ q ≈ PSet.pair γ v := fun q hq =>
    nn_bind (rowU q hq) fun ⟨β, h, hβ, hl, _, hqh⟩ => nn_map (fun ⟨γ, v, hγ, e⟩ =>
      ⟨γ, v, succ_sub hβ hγ, e⟩) (hl.1.1 q hqh)
  -- agreement of any two rows of `U` at the same index
  have agreeU : ∀ γ u u', PSet.pair γ u ∈ U → PSet.pair γ u' ∈ U → u ≈ u' := fun γ u u' hu hu' =>
    Stable.of_nn (rowU _ hu) fun ⟨β, h, hβ, hl, _, hqh⟩ => Stable.of_nn (rowU _ hu') fun ⟨β', h', hβ', hl', _, hqh'⟩ =>
      lhist_agree (hα.mem hβ) (hα.mem hβ') hl hl' γ u u' hqh hqh'
  -- totality of `U` on `α`
  have totU : ∀ β, β ∈ α → ¬¬∃ v, PSet.pair β v ∈ U := fun β hβ =>
    nn_bind (ih β hβ (hα.mem hβ) (hM.trans hαM hβ)) fun ⟨h, hh, hl⟩ =>
      nn_map (fun ⟨v, hv⟩ => ⟨v, mem_sUnion.2 (nn_intro ⟨h, inB β h hβ hh hl, hv⟩)⟩) (hl.1.2.1 β (self_mem_succ β))
  -- the recurrence at the rows of `U`, read in `U`
  have recU : ∀ β v, PSet.pair β v ∈ U → ∀ x, x ∈ v ↔ ¬¬∃ γ, γ ∈ β ∧ ¬¬∃ u, PSet.pair γ u ∈ U ∧ x ∈ defPow u := by
    intro β v hβv x
    refine Stable.by_cases (x ∈ v) (fun hx => ⟨fun _ => ?_, fun _ => hx⟩) fun hx => ⟨fun h => (hx h).elim, fun k => (hx ?_).elim⟩
    · refine Stable.of_nn (rowU _ hβv) fun ⟨β', h, hβ', hl, hhB, hqh⟩ => ?_
      refine nn_bind ((hl.2 β v hqh x).1 hx) fun ⟨γ, hγ, k⟩ => nn_map (fun ⟨u, hu, hxu⟩ =>
        ⟨γ, hγ, nn_intro ⟨u, mem_sUnion.2 (nn_intro ⟨h, hhB, hu⟩), hxu⟩⟩) k
    · refine Stable.of_nn (rowU _ hβv) fun ⟨β', h, hβ', hl, hhB, hqh⟩ => ?_
      refine (hl.2 β v hqh x).2 (nn_bind k fun ⟨γ, hγ, k⟩ => nn_bind k fun ⟨u, hu, hxu⟩ => ?_)
      have hγd : γ ∈ succ β' := (hα.mem hβ').succ.trans _ (hl.mem_dom hqh) γ hγ
      refine nn_map (fun ⟨u', hu'⟩ => ⟨γ, hγ, nn_intro ⟨u', hu', ?_⟩⟩) (hl.1.2.1 γ hγd)
      exact (mem_congr_right (defPow_congr (agreeU γ u u' hu (mem_sUnion.2 (nn_intro ⟨h, hhB, hu'⟩))))).1 hxu
  -- 3. the new row: the union of the definable powersets of the rows of `U`
  let e3 : Nat → PSet.{u} := Env.cons α (Env.cons U envω)
  have he3 : ∀ i, M (e3 i) := Env.cons_mem hαM (Env.cons_mem hU hM.envω_mem)
  let χ : Fml := ex (and (pairMemF 4 1 0) (rename (fun k => if k = 0 then 0 else if k = 1 then 2 else 0) defPowF))
  have keyχ : ∀ x y, M x → M y → (Sat M χ (Env.cons x (Env.cons y e3)) ↔ ¬¬∃ u, PSet.pair x u ∈ U ∧ y ≈ defPow u) := by
    intro x y hx hy
    have he5 := Env.cons_mem hx (Env.cons_mem hy he3)
    have dp : ∀ u, M u → (Sat M (rename (fun k => if k = 0 then 0 else if k = 1 then 2 else 0) defPowF)
        (Env.cons u (Env.cons x (Env.cons y e3))) ↔ y ≈ defPow u) := fun u hu =>
      (sat_rename _ _ _).trans (((sat_bound bound_defPowF (e' := Env.cons u (Env.cons y envω)) fun i hi => by
        rcases i with _ | _ | i
        · exact Equiv.refl _
        · exact Equiv.refl _
        · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim).trans
        (hM.sat_defPowF hu hy)).trans ⟨fun k => ext fun z => (k z).trans mem_defPow.symm,
          fun e z => (mem_congr_right e).trans mem_defPow⟩)
    refine sat_ex.trans ⟨fun k => nn_map (fun ⟨u, hu, hs⟩ => ?_) k, fun k => nn_map (fun ⟨u, hu, e⟩ => ?_) k⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      exact ⟨u, (hT.sat_pairMemF (Env.cons_mem hu he5) 4 1 0).1 h1, (dp u hu).1 h2⟩
    · have huM := (hT.of_pair_mem hU hu).2
      exact ⟨u, huM, sat_and.2 ⟨(hT.sat_pairMemF (Env.cons_mem huM he5) 4 1 0).2 hu, (dp u huM).2 e⟩⟩
  have hfunχ : ∀ x y y', x ∈ e3 0 → M y → M y' → Sat M χ (Env.cons x (Env.cons y e3)) →
      Sat M χ (Env.cons x (Env.cons y' e3)) → y ≈ y' := fun x y y' hx hy hy' h1 h2 =>
    have hxM := hM.trans hαM hx
    Stable.of_nn ((keyχ x y hxM hy).1 h1) fun ⟨u, hu, e⟩ => Stable.of_nn ((keyχ x y' hxM hy').1 h2) fun ⟨u', hu', e'⟩ =>
      e.trans ((defPow_congr (agreeU x u u' hu hu')).trans e'.symm)
  refine nn_bind (hM.replM χ he3 hfunχ) fun ⟨c, hc, hcs⟩ => ?_
  let e4 : Nat → PSet.{u} := Env.cons c (Env.cons α (Env.cons U envω))
  have he4 : ∀ i, M (e4 i) := Env.cons_mem hc he3
  let χ' : Fml := ex (and (mem 0 3) (ex (and (pairMemF 5 1 0) (rename (fun k => if k = 0 then 0 else if k = 1 then 2 else 0) defPowF))))
  have keyχ' : ∀ y, M y → (Sat M χ' (Env.cons y e4) ↔ ¬¬∃ x, x ∈ α ∧ ¬¬∃ u, PSet.pair x u ∈ U ∧ y ≈ defPow u) := by
    intro y hy
    have he5 := Env.cons_mem hy he4
    have dp : ∀ x u, M x → M u → (Sat M (rename (fun k => if k = 0 then 0 else if k = 1 then 2 else 0) defPowF)
        (Env.cons u (Env.cons x (Env.cons y e4))) ↔ y ≈ defPow u) := fun x u hx hu =>
      (sat_rename _ _ _).trans (((sat_bound bound_defPowF (e' := Env.cons u (Env.cons y envω)) fun i hi => by
        rcases i with _ | _ | i
        · exact Equiv.refl _
        · exact Equiv.refl _
        · exact (Nat.not_lt_zero _ (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))).elim).trans
        (hM.sat_defPowF hu hy)).trans ⟨fun k => ext fun z => (k z).trans mem_defPow.symm,
          fun e z => (mem_congr_right e).trans mem_defPow⟩)
    refine sat_ex.trans ⟨fun k => nn_bind k fun ⟨x, hx, hs⟩ => ?_, fun k => nn_bind k fun ⟨x, hxα, k⟩ => ?_⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      have he6 := Env.cons_mem hx he5
      refine nn_map (fun ⟨u, hu, hs⟩ => ?_) (sat_ex.1 h2)
      have ⟨h3, h4⟩ := sat_and.1 hs
      exact ⟨x, h1, nn_intro ⟨u, (hT.sat_pairMemF (Env.cons_mem hu he6) 5 1 0).1 h3, (dp x u hx hu).1 h4⟩⟩
    · have hx := hM.trans hαM hxα
      have he6 := Env.cons_mem hx he5
      refine nn_map (fun ⟨u, hu, e⟩ => ?_) k
      have huM := (hT.of_pair_mem hU hu).2
      exact ⟨x, hx, sat_and.2 ⟨hxα, sat_ex.2 (nn_intro ⟨u, huM, sat_and.2
        ⟨(hT.sat_pairMemF (Env.cons_mem huM he6) 5 1 0).2 hu, (dp x u hx huM).2 e⟩⟩)⟩⟩
  have hψ' : ∀ y y' : PSet.{u}, y ≈ y' → Sat M χ' (Env.cons y e4) → Sat M χ' (Env.cons y' e4) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  let C := sep (fun y => Sat M χ' (Env.cons y e4)) c
  have hC : M C := hM.sepM χ' he4
  let vα := PSet.sUnion C
  have hvα : M vα := hM.sUnion hC
  have memvα : ∀ x, x ∈ vα ↔ ¬¬∃ β, β ∈ α ∧ ¬¬∃ u, PSet.pair β u ∈ U ∧ x ∈ defPow u := by
    intro x
    refine mem_sUnion.trans ⟨fun k => nn_bind k fun ⟨y, hy, hxy⟩ => ?_, fun k => nn_bind k fun ⟨β, hβ, k⟩ => nn_bind k fun ⟨u, hu, hxu⟩ => ?_⟩
    · have hyM := hM.trans hc ((mem_sep hψ').1 hy).1
      refine nn_bind ((keyχ' y hyM).1 ((mem_sep hψ').1 hy).2) fun ⟨β, hβ, k⟩ => nn_map (fun ⟨u, hu, e⟩ =>
        ⟨β, hβ, nn_intro ⟨u, hu, (mem_congr_right e).1 hxy⟩⟩) k
    · have huM := (hT.of_pair_mem hU hu).2
      have hy : M (defPow u) := hM.defPow_mem huM
      have hyc : defPow u ∈ c := hcs β (defPow u) hβ hy ((keyχ β (defPow u) (hM.trans hαM hβ) hy).2 (nn_intro ⟨u, hu, Equiv.refl _⟩))
      exact nn_intro ⟨defPow u, (mem_sep hψ').2 ⟨hyc, (keyχ' _ hy).2 (nn_intro ⟨β, hβ, nn_intro ⟨u, hu, Equiv.refl _⟩⟩)⟩, hxu⟩
  -- 4. the history: `U` with the new row
  let h := PSet.union U (singleton (PSet.pair α vα))
  have hh : M h := hM.union hU (hM.single (hM.pair hαM hvα))
  have memh : ∀ q, q ∈ h ↔ ¬¬(q ∈ U ∨ q ≈ PSet.pair α vα) := fun q =>
    mem_union.trans (nn_congr (or_congr Iff.rfl mem_singleton))
  -- rows of `h` at indices in `α` are rows of `U`
  have rowh : ∀ γ u, γ ∈ α → PSet.pair γ u ∈ h → PSet.pair γ u ∈ U := fun γ u hγ hq =>
    Stable.of_nn ((memh _).1 hq) fun
      | .inl hq => hq
      | .inr e => (not_mem_self α ((mem_congr_left (pair_inj e).1).1 hγ)).elim
  refine nn_intro ⟨h, hh, ⟨fun q hq => ?_, fun β hβ => ?_, fun γ u u' hu hu' => ?_⟩, fun β v hβv x => ?_⟩
  · refine nn_bind ((memh q).1 hq) fun
      | .inl hq => nn_map (fun ⟨γ, v, hγ, e⟩ => ⟨γ, v, mem_succ_of_mem hγ, e⟩) (pureU q hq)
      | .inr e => nn_intro ⟨α, vα, self_mem_succ α, e⟩
  · refine Stable.of_nn (mem_succ.1 hβ) fun
      | .inl hβ => nn_map (fun ⟨v, hv⟩ => ⟨v, (memh _).2 (nn_intro (.inl hv))⟩) (totU β hβ)
      | .inr e => nn_intro ⟨vα, (memh _).2 (nn_intro (.inr (pair_congr e (Equiv.refl _))))⟩
  · refine Stable.of_nn ((memh _).1 hu) fun h1 => Stable.of_nn ((memh _).1 hu') fun h2 => ?_
    rcases h1 with h1 | e1 <;> rcases h2 with h2 | e2
    · exact agreeU γ u u' h1 h2
    · exact (not_mem_self α ((mem_congr_left (pair_inj e2).1).1 (Stable.of_nn (pureU _ h1) fun ⟨γ', _, hγ', e⟩ =>
        (mem_congr_left (pair_inj e).1).2 hγ'))).elim
    · exact (not_mem_self α ((mem_congr_left (pair_inj e1).1).1 (Stable.of_nn (pureU _ h2) fun ⟨γ', _, hγ', e⟩ =>
        (mem_congr_left (pair_inj e).1).2 hγ'))).elim
    · exact (pair_inj e1).2.trans (pair_inj e2).2.symm
  · -- the recurrence at every row of `h`
    refine Stable.by_cases (x ∈ v) (fun hx => ⟨fun _ => ?_, fun _ => hx⟩) fun hx => ⟨fun k => (hx k).elim, fun k => (hx ?_).elim⟩
    · refine Stable.of_nn ((memh _).1 hβv) fun
        | .inl hβv => nn_bind ((recU β v hβv x).1 hx) fun ⟨γ, hγ, k⟩ => nn_map (fun ⟨u, hu, hxu⟩ =>
            ⟨γ, hγ, nn_intro ⟨u, (memh _).2 (nn_intro (.inl hu)), hxu⟩⟩) k
        | .inr e => ?_
      have ⟨eβ, ev⟩ := pair_inj e
      refine nn_bind ((memvα x).1 ((mem_congr_right ev).1 hx)) fun ⟨γ, hγ, k⟩ => nn_map (fun ⟨u, hu, hxu⟩ =>
        ⟨γ, (mem_congr_right eβ).2 hγ, nn_intro ⟨u, (memh _).2 (nn_intro (.inl hu)), hxu⟩⟩) k
    · refine Stable.of_nn ((memh _).1 hβv) fun
        | .inl hβv => ?_
        | .inr e => ?_
      · have hβα : β ∈ α := Stable.of_nn (pureU _ hβv) fun ⟨_, _, hβ', e⟩ => (mem_congr_left (pair_inj e).1).2 hβ'
        exact (recU β v hβv x).2 (nn_bind k fun ⟨γ, hγ, k⟩ => nn_map (fun ⟨u, hu, hxu⟩ =>
          ⟨γ, hγ, nn_intro ⟨u, rowh γ u (hα.trans β hβα γ hγ) hu, hxu⟩⟩) k)
      have ⟨eβ, ev⟩ := pair_inj e
      refine (mem_congr_right ev).2 ((memvα x).2 (nn_bind k fun ⟨γ, hγ, k⟩ => nn_map (fun ⟨u, hu, hxu⟩ =>
        ⟨γ, (mem_congr_right eβ).1 hγ, nn_intro ⟨u, rowh γ u ((mem_congr_right eβ).1 hγ) hu, hxu⟩⟩) k))

/-- **Existence of levels.** -/
theorem level_exists {α : PSet.{u}} (hα : IsOrd α) (hαM : M α) : ¬¬∃ A, M A ∧ Level M α A :=
  nn_bind (hM.lhist_exists α hα hαM) fun ⟨h, hh, hl⟩ => nn_map (fun ⟨A, hA⟩ =>
    ⟨A, (hM.toTransClass.of_pair_mem hh hA).2, nn_intro ⟨h, hh, hl, hA⟩⟩) (hl.1.2.1 α (self_mem_succ α))

omit hM in
/-- **Uniqueness of levels.** -/
theorem level_unique {α A A' : PSet.{u}} (hα : IsOrd α) (h : Level M α A) (h' : Level M α A') : A ≈ A' :=
  Stable.of_nn h fun ⟨_, _, hl, hr⟩ => Stable.of_nn h' fun ⟨_, _, hl', hr'⟩ => lhist_agree hα hα hl hl' α A A' hr hr'

omit hM in
theorem IsLHist.congr {α α' h : PSet.{u}} (e : α ≈ α') (hl : IsLHist α h) : IsLHist α' h :=
  ⟨hl.1.congr_dom (succ_congr e), hl.2⟩

omit hM in
theorem level_congr {α α' A : PSet.{u}} (e : α ≈ α') (h : Level M α A) : Level M α' A :=
  nn_map (fun ⟨h, hh, hl, hr⟩ => ⟨h, hh, IsLHist.congr e hl, (mem_congr_left (pair_congr e (Equiv.refl _))).1 hr⟩) h

/-- **Restriction**: the rows of a history at indices up to `γ ∈ succ α` form a history on `γ`, so
every row of a history is a level. -/
theorem level_of_row {α h γ u : PSet.{u}} (hα : IsOrd α) (hαM : M α) (hh : M h) (hl : IsLHist α h) (hγ : γ ∈ succ α)
    (hr : PSet.pair γ u ∈ h) : Level M γ u := by
  have hT := hM.toTransClass
  have hγM : M γ := hM.trans (hM.succ_mem hαM) hγ
  have hγo : IsOrd γ := hα.succ.mem hγ
  let sγ := succ γ
  have hsγ : M sγ := hM.succ_mem hγM
  let E : Nat → PSet.{u} := Env.cons h (Env.cons sγ envω)
  have hE : ∀ i, M (E i) := Env.cons_mem hh (Env.cons_mem hsγ hM.envω_mem)
  let φ : Fml := ex (ex (and (mem 1 4) (pairF 2 1 0)))
  have keyφ : ∀ q, M q → (Sat M φ (Env.cons q E) ↔ ¬¬∃ i v, i ∈ sγ ∧ q ≈ PSet.pair i v) := by
    intro q hq
    have he1 := Env.cons_mem hq hE
    refine sat_ex.trans ⟨fun k => nn_bind k fun ⟨i, hi, hs⟩ => nn_map (fun ⟨v, hv, hs⟩ => ?_) (sat_ex.1 hs),
      fun k => nn_bind k fun ⟨i, v, hi, e⟩ => ?_⟩
    · have ⟨h1, h2⟩ := sat_and.1 hs
      exact ⟨i, v, h1, (hT.sat_pairF (Env.cons_mem hv (Env.cons_mem hi he1)) 2 1 0).1 h2⟩
    · have ⟨hiM, hvM⟩ := hT.of_pair_class (hM.resp e hq)
      exact nn_intro ⟨i, hiM, sat_ex.2 (nn_intro ⟨v, hvM, sat_and.2 ⟨hi, (hT.sat_pairF (Env.cons_mem hvM (Env.cons_mem hiM he1)) 2 1 0).2 e⟩⟩)⟩
  have hφ : ∀ q q' : PSet.{u}, q ≈ q' → Sat M φ (Env.cons q E) → Sat M φ (Env.cons q' E) := fun _ _ e k =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k
  let h' := sep (fun q => Sat M φ (Env.cons q E)) h
  have hh' : M h' := hM.sepM φ hE
  have memh' : ∀ q, q ∈ h' ↔ q ∈ h ∧ ¬¬∃ i v, i ∈ sγ ∧ q ≈ PSet.pair i v := fun q =>
    (mem_sep hφ).trans ⟨fun ⟨h1, h2⟩ => ⟨h1, (keyφ q (hM.trans hh h1)).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (keyφ q (hM.trans hh h1)).2 h2⟩⟩
  have sub_succ : ∀ i, i ∈ sγ → i ∈ succ α := fun i hi => Stable.of_nn (mem_succ.1 hi) fun
    | .inl h1 => hα.succ.trans γ hγ i h1
    | .inr e => (mem_congr_left e).2 hγ
  have rowh' : ∀ i v, i ∈ sγ → PSet.pair i v ∈ h → PSet.pair i v ∈ h' := fun i v hi hv =>
    (memh' _).2 ⟨hv, nn_intro ⟨i, v, hi, Equiv.refl _⟩⟩
  refine nn_intro ⟨h', hh', ⟨⟨fun q hq => ?_, fun i hi => ?_, fun i v v' h1 h2 => hl.1.2.2 i v v' ((memh' _).1 h1).1 ((memh' _).1 h2).1⟩,
    fun β v hβv x => ?_⟩, rowh' γ u (self_mem_succ γ) hr⟩
  · exact ((memh' q).1 hq).2
  · exact nn_map (fun ⟨v, hv⟩ => ⟨v, rowh' i v hi hv⟩) (hl.1.2.1 i (sub_succ i hi))
  · have ⟨hβv', hβ⟩ := (memh' _).1 hβv
    have hβs : β ∈ sγ := Stable.of_nn hβ fun ⟨_, _, hi, e⟩ => (mem_congr_left (pair_inj e).1).2 hi
    exact (hl.2 β v hβv' x).trans (nn_congr (exists_congr fun δ => and_congr_right fun hδ => nn_congr (exists_congr fun w =>
      and_congr ⟨fun hw => rowh' δ w (hγo.succ.trans β hβs δ hδ) hw, fun hw => ((memh' _).1 hw).1⟩ Iff.rfl)))

/-- **The uniform recurrence at levels**: `L_α = ⋃_{γ ∈ α} defPow L_γ`. -/
theorem level_rec {α A : PSet.{u}} (hα : IsOrd α) (hαM : M α) (h : Level M α A) :
    ∀ x, x ∈ A ↔ ¬¬∃ γ, γ ∈ α ∧ ¬¬∃ B, Level M γ B ∧ x ∈ defPow B := by
  intro x
  refine Stable.of_nn h fun ⟨hst, hh, hl, hr⟩ => ?_
  refine (hl.2 α A hr x).trans (nn_congr (exists_congr fun γ => and_congr_right fun hγ => ?_))
  constructor
  · exact nn_map fun ⟨B, hB, hx⟩ => ⟨B, hM.level_of_row hα hαM hh hl (mem_succ_of_mem hγ) hB, hx⟩
  · intro k
    refine nn_bind (hl.1.2.1 γ (mem_succ_of_mem hγ)) fun ⟨B', hB'⟩ => nn_map (fun ⟨B, hB, hx⟩ => ⟨B', hB', ?_⟩) k
    exact (mem_congr_right (defPow_congr (level_unique (hα.mem hγ) hB
      (hM.level_of_row hα hαM hh hl (mem_succ_of_mem hγ) hB')))).1 hx

/-- **The zero law**: `L_0 = ∅`. -/
theorem level_zero {A : PSet.{u}} (h : Level M PSet.empty A) : A ≈ PSet.empty :=
  ext fun x => ⟨fun hx => Stable.of_nn ((hM.level_rec isOrd_empty hM.empty h x).1 hx) fun ⟨γ, hγ, _⟩ =>
      (not_mem_empty γ hγ).elim, fun hx => (not_mem_empty x hx).elim⟩

/-- **Transitivity and monotonicity**, jointly by `∈`-induction: every level is transitive, and
levels increase along membership. -/
theorem level_trans_mono : ∀ α : PSet.{u}, IsOrd α → M α → ∀ A, Level M α A →
    Trans A ∧ ∀ β B, β ∈ α → Level M β B → ∀ x, x ∈ B → x ∈ A := by
  refine mem_induction (P := fun α => IsOrd α → M α → ∀ A, Level M α A →
    Trans A ∧ ∀ β B, β ∈ α → Level M β B → ∀ x, x ∈ B → x ∈ A) fun α ih hα hαM A hA => ?_
  have rc := hM.level_rec hα hαM hA
  have mono : ∀ β B, β ∈ α → Level M β B → ∀ x, x ∈ B → x ∈ A := by
    intro β B hβ hB x hx
    have ⟨htB, _⟩ := ih β hβ (hα.mem hβ) (hM.trans hαM hβ) B hB
    exact (rc x).2 (nn_intro ⟨β, hβ, nn_intro ⟨B, hB, mem_defPow_of_trans htB hx⟩⟩)
  refine ⟨fun y hy z hz => ?_, mono⟩
  refine Stable.of_nn ((rc y).1 hy) fun ⟨γ, hγ, k⟩ => Stable.of_nn k fun ⟨B, hB, hyB⟩ => ?_
  have ⟨htB, _⟩ := ih γ hγ (hα.mem hγ) (hM.trans hαM hγ) B hB
  exact (rc z).2 (nn_intro ⟨γ, hγ, nn_intro ⟨B, hB, defPow_trans htB y hyB z hz⟩⟩)

theorem level_trans {α A : PSet.{u}} (hα : IsOrd α) (hαM : M α) (h : Level M α A) : Trans A :=
  (hM.level_trans_mono α hα hαM A h).1

theorem level_mono {α β A B : PSet.{u}} (hα : IsOrd α) (hαM : M α) (hβ : β ∈ α) (hA : Level M α A) (hB : Level M β B) :
    ∀ x, x ∈ B → x ∈ A :=
  (hM.level_trans_mono α hα hαM A hA).2 β B hβ hB

/-- The definable powerset of an earlier level is included in a later level. -/
theorem defPow_level_sub {α γ A C : PSet.{u}} (hα : IsOrd α) (hαM : M α) (hγ : γ ∈ α) (hA : Level M α A) (hC : Level M γ C) :
    ∀ x, x ∈ defPow C → x ∈ A := fun x hx =>
  (hM.level_rec hα hαM hA x).2 (nn_intro ⟨γ, hγ, nn_intro ⟨C, hC, hx⟩⟩)

/-- **The successor law**: `L_{succ β} = defPow L_β`. -/
theorem level_succ {β A B : PSet.{u}} (hβ : IsOrd β) (hβM : M β) (hA : Level M (succ β) A) (hB : Level M β B) :
    A ≈ defPow B := by
  have hβs : IsOrd (succ β) := hβ.succ
  have hβsM : M (succ β) := hM.succ_mem hβM
  have htB : Trans B := hM.level_trans hβ hβM hB
  refine ext fun x => ⟨fun hx => ?_, fun hx => hM.defPow_level_sub hβs hβsM (self_mem_succ β) hA hB x hx⟩
  refine Stable.of_nn ((hM.level_rec hβs hβsM hA x).1 hx) fun ⟨γ, hγ, k⟩ => Stable.of_nn k fun ⟨C, hC, hxC⟩ => ?_
  refine Stable.of_nn (mem_succ.1 hγ) fun
    | .inl hγβ => mem_defPow_of_trans htB (hM.defPow_level_sub hβ hβM hγβ hB hC x hxC)
    | .inr e => (mem_congr_right (defPow_congr (level_unique hβ (level_congr e hC) hB))).1 hxC

/-- A limit ordinal: nonzero and closed under successor. -/
def IsLimit (lam : PSet.{u}) : Prop := IsOrd lam ∧ (¬¬∃ z, z ∈ lam) ∧ ∀ β, β ∈ lam → succ β ∈ lam

/-- **The limit law**: `L_λ = ⋃_{β ∈ λ} L_β`. -/
theorem level_limit {lam A : PSet.{u}} (hl : IsLimit lam) (hlM : M lam) (hA : Level M lam A) :
    ∀ x, x ∈ A ↔ ¬¬∃ β, β ∈ lam ∧ ¬¬∃ B, Level M β B ∧ x ∈ B := by
  intro x
  refine (hM.level_rec hl.1 hlM hA x).trans ⟨fun k => nn_bind k fun ⟨γ, hγ, k⟩ => nn_bind k fun ⟨C, hC, hxC⟩ => ?_,
    fun k => nn_bind k fun ⟨β, hβ, k⟩ => nn_bind k fun ⟨B, hB, hxB⟩ => ?_⟩
  · -- `defPow L_γ = L_{succ γ}` and `succ γ ∈ λ`
    have hsγ := hl.2.2 γ hγ
    refine nn_map (fun ⟨D, _, hD⟩ => ⟨succ γ, hsγ, nn_intro ⟨D, hD, ?_⟩⟩) (hM.level_exists (hl.1.mem hsγ) (hM.trans hlM hsγ))
    exact (mem_congr_right (hM.level_succ (hl.1.mem hγ) (hM.trans hlM hγ) hD hC)).2 hxC
  · have htB := hM.level_trans (hl.1.mem hβ) (hM.trans hlM hβ) hB
    exact nn_intro ⟨β, hβ, nn_intro ⟨B, hB, mem_defPow_of_trans htB hxB⟩⟩

end SynZF

/-- info: 'PSet.SynZF.lhist_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.lhist_exists
/-- info: 'PSet.SynZF.level_succ' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.level_succ
/-- info: 'PSet.SynZF.level_limit' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.level_limit

end PSet
