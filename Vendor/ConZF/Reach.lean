import Vendor.ConZF.Rule
import Vendor.ConZF.VLevel
/-!
The definability rule, uniformly. There is no case distinction between zero, successor and
limit ordinals in the definitions:

* `(q, s)` is *unbounded at `η`* if `I η q` is functional on `s` with values of rank in `η`
  that cover `η`;
* `η` is *reached from `ν`* if some such `q, s` lie in `D ν`, and *reachable* if it is reached
  from some `ν ∈ η`;
* `η` is *good* if it is reachable as soon as it has an element;
* the child `a` of a node with reachable target `η` has target the least `ν` from which `η` is
  reached (as a separation, so nothing is chosen), and the child `b ⟨q, s, x⟩`, for `(q, s)`
  unbounded at `η` and `x ∈ s`, has target the rank of the value at `x`.

A successor `ζ + 1` is reached from `ζ` by a constant function and `ω` from `0` by the identity
on `ω ∈ D 0`; these are facts about a particular `I`, proved in `Model.lean`, not cases of the
rule. `I` is an arbitrary relation respecting bisimulation, and `D` is any budget (`Budget`).
-/
universe u

namespace PSet

variable [B : Budget.{u}]

/-! ### The rule -/

variable (I : PSet.{u} → PSet.{u} → PSet.{u} → PSet.{u} → Prop)

/-- `(q, s)` defines, over `V_η`, a partial function on `s` with values of rank covering `η`. -/
def Unb (η q s : PSet.{u}) : Prop :=
  (∀ x y y', x ∈ s → I η q x y → I η q x y' → y ≈ y') ∧
  (∀ x y, x ∈ s → I η q x y → rank y ∈ η) ∧
  (∀ ζ, ζ ∈ η → ¬¬∃ x y, x ∈ s ∧ I η q x y ∧ ζ ∈ succ (rank y))

/-- `η` is reached from parameters in `D ν`. -/
def Reach (η ν : PSet.{u}) : Prop := ¬¬∃ q s, q ∈ D ν ∧ s ∈ D ν ∧ Unb I η q s

def Reachable (η : PSet.{u}) : Prop := ¬¬∃ ν, ν ∈ η ∧ Reach I η ν

/-- Good: reachable as soon as nonempty. -/
def Good (η : PSet.{u}) : Prop := ∀ ζ, ζ ∈ η → Reachable I η

/-- Hereditarily good ordinals. -/
def Cls (η : PSet.{u}) : Prop := IsOrd η ∧ ∀ μ, μ ∈ succ η → Good I μ

instance {η ν : PSet.{u}} : Stable (Reach I η ν) := inferInstanceAs (Stable (¬_))
instance {η : PSet.{u}} : Stable (Reachable I η) := inferInstanceAs (Stable (¬_))
instance {η : PSet.{u}} : Stable (Good I η) := inferInstanceAs (Stable (∀ ζ, ζ ∈ η → _))
instance {η : PSet.{u}} : Stable (Cls I η) := inferInstanceAs (Stable (_ ∧ ∀ μ, μ ∈ succ η → _))

/-- The least `ν` from which `η` is reached, as the set of the `ν ∈ η` from which it is not. -/
def Gν (η : PSet.{u}) : PSet.{u} := sep (fun ν => ¬ Reach I η ν) η

def rule (η : PSet.{u}) : Label.{u} → PSet.{u} → Prop
  | .a => fun ξ => Reachable I η ∧ ξ ≈ Gν I η
  | .b w => fun ξ => ¬¬∃ q s x y, w ≈ triple q s x ∧ Unb I η q s ∧ x ∈ s ∧ I η q x y ∧ ξ ≈ rank y
  | .c _ => fun _ => False

variable {I}
variable (I_resp : ∀ {η η' q q' x x' y y' : PSet.{u}},
  η ≈ η' → q ≈ q' → x ≈ x' → y ≈ y' → I η q x y → I η' q' x' y')
include I_resp

omit [Budget.{u}] in
theorem Unb.resp {η η' q q' s s' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (es : s ≈ s')
    (h : Unb I η q s) : Unb I η' q' s' := by
  have back : ∀ {x y}, I η' q' x y → I η q x y :=
    I_resp eη.symm eq.symm (Equiv.refl _) (Equiv.refl _)
  refine ⟨fun x y y' hx h1 h2 => h.1 x y y' ((mem_congr_right es).2 hx) (back h1) (back h2),
    fun x y hx h1 => (mem_congr_right eη).1 (h.2.1 x y ((mem_congr_right es).2 hx) (back h1)),
    fun ζ hζ => nn_map (fun ⟨x, y, hx, h1, h2⟩ => ⟨x, y, (mem_congr_right es).1 hx,
      I_resp eη eq (Equiv.refl _) (Equiv.refl _) h1, h2⟩) (h.2.2 ζ ((mem_congr_right eη).2 hζ))⟩

theorem Reach.resp {η η' ν ν' : PSet.{u}} (eη : η ≈ η') (eν : ν ≈ ν') (h : Reach I η ν) :
    Reach I η' ν' :=
  nn_map (fun ⟨q, s, hq, hs, h⟩ => ⟨q, s, (mem_congr_right (D_congr eν)).1 hq,
    (mem_congr_right (D_congr eν)).1 hs, h.resp I_resp eη (Equiv.refl _) (Equiv.refl _)⟩) h

theorem Reachable.resp {η η' : PSet.{u}} (e : η ≈ η') (h : Reachable I η) : Reachable I η' :=
  nn_map (fun ⟨ν, hν, h⟩ => ⟨ν, (mem_congr_right e).1 hν, h.resp I_resp e (Equiv.refl _)⟩) h

theorem Good.resp {η η' : PSet.{u}} (e : η ≈ η') (h : Good I η) : Good I η' :=
  fun ζ hζ => (h ζ ((mem_congr_right e).2 hζ)).resp I_resp e

omit I_resp in
theorem Cls.resp {η η' : PSet.{u}} (e : η ≈ η') (h : Cls I η) : Cls I η' :=
  ⟨h.1.resp e, fun μ hμ => h.2 μ ((mem_congr_right (succ_congr e)).2 hμ)⟩

omit I_resp in
theorem Cls.mem {η ξ : PSet.{u}} (h : Cls I η) (hξ : ξ ∈ η) : Cls I ξ :=
  ⟨h.1.mem hξ, fun μ hμ => h.2 μ <| mem_succ_of_mem <| Stable.of_nn (mem_succ.1 hμ) fun
    | .inl h' => h.1.trans ξ hξ μ h'
    | .inr e => (mem_congr_left e).2 hξ⟩

omit I_resp in
theorem Cls.good {η : PSet.{u}} (h : Cls I η) : Good I η := h.2 η (self_mem_succ η)

theorem mem_Gν {η z : PSet.{u}} : z ∈ Gν I η ↔ z ∈ η ∧ ¬ Reach I η z :=
  mem_sep fun _ _ e h h' => h (h'.resp I_resp (Equiv.refl _) e.symm)

theorem Gν_resp {η η' : PSet.{u}} (e : η ≈ η') : Gν I η ≈ Gν I η' :=
  ext fun _ => (mem_Gν I_resp).trans <| .trans
    (and_congr (mem_congr_right e) ⟨fun h h' => h (h'.resp I_resp e.symm (Equiv.refl _)),
      fun h h' => h (h'.resp I_resp e (Equiv.refl _))⟩) (mem_Gν I_resp).symm

/-- The least `ν` is an element of `η` from which `η` is reached. -/
theorem Gν_spec {η : PSet.{u}} (hη : IsOrd η) (h : Reachable I η) :
    Gν I η ∈ η ∧ IsOrd (Gν I η) ∧ Reach I η (Gν I η) := by
  have up : ∀ {ν ν'}, ν ∈ ν' → Reach I η ν → Reach I η ν' := fun hν =>
    nn_map fun ⟨q, s, hq, hs, hu⟩ => ⟨q, s, D_mono hν hq, D_mono hν hs, hu⟩
  have hG : IsOrd (Gν I η) := by
    refine ⟨fun μ hμ μ' hμ' => ?_, fun μ hμ => hη.mem_trans μ ((mem_Gν I_resp).1 hμ).1⟩
    have ⟨hμη, hμr⟩ := (mem_Gν I_resp).1 hμ
    exact (mem_Gν I_resp).2 ⟨hη.trans μ hμη μ' hμ', fun h' => hμr (up hμ' h')⟩
  have hmem : Gν I η ∈ η := by
    refine Stable.of_nn (hG.subset hη fun z hz => ((mem_Gν I_resp).1 hz).1) ?_
    rintro (h' | e)
    · exact h'
    · exact Stable.of_nn h fun ⟨ν, hν, hr⟩ =>
        (((mem_Gν I_resp).1 ((mem_congr_right e).2 hν)).2 hr).elim
  exact ⟨hmem, hG, Stable.by_cases _ id fun hn =>
    (not_mem_self _ ((mem_Gν I_resp).2 ⟨hmem, hn⟩)).elim⟩

theorem rule_resp {η η' : PSet.{u}} {l l' : Label.{u}} {ξ ξ' : PSet.{u}}
    (eη : η ≈ η') (el : l.Equiv l') (eξ : ξ ≈ ξ') (h : rule I η l ξ) : rule I η' l' ξ' := by
  cases el with
  | a => exact ⟨h.1.resp I_resp eη, eξ.symm.trans (h.2.trans (Gν_resp I_resp eη))⟩
  | b ew =>
    exact nn_map (fun ⟨q, s, x, y, h2, h3, h4, h5, h6⟩ => ⟨q, s, x, y, ew.symm.trans h2,
      h3.resp I_resp eη (Equiv.refl _) (Equiv.refl _), h4,
      I_resp eη (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) h5, eξ.symm.trans h6⟩) h
  | c => exact h.elim

theorem rule_func {η : PSet.{u}} {l : Label.{u}} {ξ ξ' : PSet.{u}}
    (h : rule I η l ξ) (h' : rule I η l ξ') : ξ ≈ ξ' := by
  cases l with
  | a => exact h.2.trans h'.2.symm
  | b w =>
    refine Stable.of_nn h fun ⟨q, s, x, y, h2, h3, h4, h5, h6⟩ =>
      Stable.of_nn h' fun ⟨q', s', x', y', h2', _, _, h5', h6'⟩ => ?_
    obtain ⟨eq, -, ex⟩ := triple_inj (h2.symm.trans h2')
    have h5'' := I_resp (Equiv.refl _) eq.symm ex.symm (Equiv.refl _) h5'
    exact h6.trans ((rank_congr (h3.1 x y y' h4 h5 h5'')).trans h6'.symm)
  | c => exact h.elim

theorem rule_mem {η : PSet.{u}} {l : Label.{u}} {ξ : PSet.{u}} (hη : Cls I η)
    (h : rule I η l ξ) : ξ ∈ η ∧ Cls I ξ := by
  suffices ξ ∈ η from ⟨this, hη.mem this⟩
  cases l with
  | a => exact (mem_congr_left h.2).2 (Gν_spec I_resp hη.1 h.1).1
  | b w =>
    exact Stable.of_nn h fun ⟨q, s, x, y, _, h3, h4, h5, h6⟩ =>
      (mem_congr_left h6).2 (h3.2.1 x y h4 h5)
  | c => exact h.elim

theorem rule_sup (U : PSet.{u}) {η G : PSet.{u}} (hη : Cls I η)
    (hG : ∀ x, x ∈ G ↔ ¬¬∃ ζ, rule I η .a ζ ∧ x ∈ ζ) (x : PSet.{u}) :
    x ∈ η ↔ ¬¬∃ l ξ, Avail D U G l ∧ rule I η l ξ ∧ x ∈ succ ξ := by
  constructor
  · intro hx
    have hr : Reachable I η := hη.good x hx
    have ⟨_, _, hreach⟩ := Gν_spec I_resp hη.1 hr
    have hGe : G ≈ Gν I η := ext fun z => (hG z).trans
      ⟨fun h => Stable.of_nn h fun ⟨ζ, ⟨_, e⟩, hz⟩ => (mem_congr_right e).1 hz,
       fun hz => nn_intro ⟨_, ⟨hr, Equiv.refl _⟩, hz⟩⟩
    refine nn_bind hreach fun ⟨q, s, hq, hs, hu⟩ => ?_
    refine nn_map (fun ⟨x', y, hx', hI, hxy⟩ => ?_) (hu.2.2 x hx)
    have hw : triple q s x' ∈ D G := (mem_congr_right (D_congr hGe)).2
      (triple_mem_D hq hs (D_trans hs hx'))
    exact ⟨.b (triple q s x'), rank y, .inr (.inl ⟨_, hw, Label.Equiv.refl _⟩),
      nn_intro ⟨q, s, x', y, Equiv.refl _, hu, hx', hI, Equiv.refl _⟩, hxy⟩
  · intro h
    refine Stable.of_nn h fun ⟨l, ξ, _, hr, hx⟩ => ?_
    have hξ := (rule_mem I_resp hη hr).1
    refine Stable.of_nn (mem_succ.1 hx) ?_
    rintro (hx | e)
    · exact hη.1.trans ξ hξ x hx
    · exact (mem_congr_left e).2 hξ

/-- The definability rule meets the one-node conditions, for the hereditarily good ordinals. -/
theorem reach_rule (U : PSet.{u}) : Rule D U (rule I) (Cls I) :=
  ⟨rule_func I_resp, rule_resp I_resp, Cls.resp, rule_mem I_resp,
   fun hη hG x => rule_sup I_resp U hη hG x⟩
