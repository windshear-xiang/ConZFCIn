import Vendor.ConZF.ZF
import Vendor.ConZF.Interval
/-!
The first-order cardinal interface. Formulas with de Bruijn variables for singletons,
unordered and Kuratowski pairs, membership of a pair in a set, transitivity and ordinals,
functions and injections (every member a pair), internal powersets, `ω` below an ordinal
(a nonempty successor-closed member), regularity, initiality, strong limit, and strong
inaccessibility (`inaccF`), the axiom of choice (`ac`, a choice function on any set of nonempty
sets), and the theory `ZFCI = ZF + AC + ∃ inaccessible`.

The satisfaction bridges are proved for a transitive class closed under unordered pairs and
respecting bisimulation (`TransClass`), with environments in the class: pair formulas are
exact (`sat_pairF`, `sat_pairMemF`), ordinals are exact (`sat_ordF`), and the syntactic
function, injection, and powerset predicates imply the ambient ones (`isFun_of_sat`,
`isInjRel_of_sat`, `powerset_of_sat`). The main bridge is
`InaccIn N κ → Sat N inaccF (κ, e)` (`sat_inaccF_of_inaccIn`); the converse is not proved.

**Conditional consistency** (`con_ZFCI`): if an upper-model interface `M` has a transitive
class `N` that is closed under unordered pairs and validates the syntactic ZF axioms and `ac`,
then under excluded middle `ZFCI` is consistent, by the interval theorem and `Con.of_model`.
The premises are explicit: excluded middle, the interface, transitivity and pair closure of its
class, and validity of ZF and choice in it.
-/
universe u

namespace PSet
open Fml

/-! ### Formulas -/

namespace CardF

/-- `s = {x}`: `∀v (v ∈ s ↔ v = x)`. -/
def singF (s x : Nat) : Fml := all (iff (mem 0 (s+1)) (eq 0 (x+1)))

/-- `w = {x, y}`. -/
def upairF (w x y : Nat) : Fml := all (iff (mem 0 (w+1)) (or (eq 0 (x+1)) (eq 0 (y+1))))

/-- `p = ⟨x, y⟩ = {{x}, {x, y}}`. -/
def pairF (p x y : Nat) : Fml :=
  all (iff (mem 0 (p+1)) (or (singF 0 (x+1)) (upairF 0 (x+1) (y+1))))

/-- `⟨x, y⟩ ∈ f`. -/
def pairMemF (f x y : Nat) : Fml := ex (and (pairF 0 (x+1) (y+1)) (mem 0 (f+1)))

/-- `x` is transitive: `∀y ∀z (z ∈ y → y ∈ x → z ∈ x)`. -/
def transF (x : Nat) : Fml := all (all (imp (mem 0 1) (imp (mem 1 (x+2)) (mem 0 (x+2)))))

/-- `x` is an ordinal: transitive with transitive members. -/
def ordF (x : Nat) : Fml := and (transF x) (all (imp (mem 0 (x+1)) (transF 0)))

/-- `f` is a function from `d` to `c`: every member is a pair with first component in `d` and
second in `c`, every member of `d` has a value, and values are unique. -/
def funF (f d c : Nat) : Fml :=
  and (all (imp (mem 0 (f+1)) (ex (and (mem 0 (d+2)) (ex (and (mem 0 (c+3)) (pairF 2 1 0)))))))
    (and (all (imp (mem 0 (d+1)) (ex (pairMemF (f+2) 1 0))))
      (all (all (all (imp (pairMemF (f+3) 2 1) (imp (pairMemF (f+3) 2 0) (eq 1 0)))))))

/-- `f` is an injection from `a` to `b`. -/
def injF (f a b : Nat) : Fml :=
  and (funF f a b)
    (all (all (all (all (imp (pairMemF (f+4) 3 1) (imp (pairMemF (f+4) 2 0)
      (imp (eq 1 0) (eq 3 2))))))))

/-- `P` is the powerset of `l`: `∀w (w ∈ P ↔ ∀z (z ∈ w → z ∈ l))`. -/
def powF (P l : Nat) : Fml := all (iff (mem 0 (P+1)) (all (imp (mem 0 1) (mem 0 (l+2)))))

/-- `ω < k`: some member of `k` is nonempty and closed under successor. -/
def omegaLtF (k : Nat) : Fml :=
  ex (and (mem 0 (k+1)) (and (ex (mem 0 1))
    (all (imp (mem 0 1) (ex (and (mem 0 2) (all (iff (mem 0 1) (or (mem 0 2) (eq 0 2))))))))))

/-- `k` is regular: every function from a member of `k` into `k` has its values in a member. -/
def regF (k : Nat) : Fml :=
  all (imp (mem 0 (k+1)) (all (imp (funF 0 1 (k+2))
    (ex (and (mem 0 (k+3)) (all (all (imp (pairMemF 3 1 0) (mem 0 2)))))))))

/-- `k` is initial: no injection into a member. -/
def initialF (k : Nat) : Fml := all (imp (mem 0 (k+1)) (all (neg (injF 0 (k+2) 1))))

/-- `k` is a strong limit: an ordinal injecting into the powerset of a member is a member. -/
def strongLimitF (k : Nat) : Fml :=
  all (imp (mem 0 (k+1)) (all (imp (powF 0 1) (all (imp (ordF 0)
    (all (imp (injF 0 1 2) (mem 1 (k+4)))))))))

/-- `k` is strongly inaccessible. -/
def inaccF (k : Nat) : Fml :=
  and (ordF k) (and (omegaLtF k) (and (initialF k) (and (regF k) (strongLimitF k))))

end CardF

open CardF

/-- **There is a strongly inaccessible cardinal.** -/
def exInacc : Fml := ex (inaccF 0)

/-- **The axiom of choice**: every set of nonempty sets has a choice function. -/
def ac : Fml :=
  all (imp (all (imp (mem 0 1) (ex (mem 0 1))))
    (ex (and (all (imp (mem 0 2) (ex (and (pairMemF 2 1 0) (mem 0 1)))))
      (all (all (all (imp (pairMemF 3 2 1) (imp (pairMemF 3 2 0) (eq 1 0)))))))))

/-- The theory `ZFC + ∃ inaccessible`. -/
inductive ZFCI : Fml → Prop
  | zf {φ} : ZF φ → ZFCI φ
  | ac : ZFCI ac
  | inacc : ZFCI exInacc

/-! ### Bridges -/

/-- A transitive class respecting bisimulation and closed under unordered pairs. -/
structure TransClass (N : PSet.{u} → Prop) : Prop where
  resp : ∀ {x y}, x ≈ y → N x → N y
  trans : ∀ {x z}, N x → z ∈ x → N z
  upair : ∀ {x y}, N x → N y → N (upair x y)

namespace TransClass
variable {N : PSet.{u} → Prop} (hN : TransClass N)
include hN

theorem single_mem {x : PSet.{u}} (hx : N x) : N (singleton x) :=
  hN.resp (ext fun _ => mem_upair.trans ⟨fun h => Stable.of_nn h fun h => mem_singleton.2 (h.elim id id),
    fun h => nn_intro (.inl (mem_singleton.1 h))⟩) (hN.upair hx hx)

theorem pair_mem {x y : PSet.{u}} (hx : N x) (hy : N y) : N (PSet.pair x y) :=
  hN.upair (hN.single_mem hx) (hN.upair hx hy)

/-- The components of a pair in the class are in the class. -/
theorem of_pair_mem {x y f : PSet.{u}} (hf : N f) (h : PSet.pair x y ∈ f) : N x ∧ N y :=
  have hp := hN.trans hf h
  ⟨hN.trans (hN.trans hp (mem_upair_left _ _)) (self_mem_singleton x),
   hN.trans (hN.trans hp (mem_upair_right _ _)) (mem_upair_right x y)⟩

variable {e : Nat → PSet.{u}} (he : ∀ i, N (e i))
include he

theorem sat_singF (s x : Nat) : Sat N (singF s x) e ↔ e s ≈ PSet.singleton (e x) := by
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => mem_singleton.2 ((sat_iff.1 (h v (hN.trans (he s) hv))).1 hv),
      fun hv => ?_⟩
    have ev := mem_singleton.1 hv
    exact (sat_iff.1 (h v (hN.resp ev.symm (he x)))).2 ev
  · exact fun h v _ => sat_iff.2 ((mem_congr_right h).trans mem_singleton)

theorem sat_upairF (w x y : Nat) : Sat N (upairF w x y) e ↔ e w ≈ PSet.upair (e x) (e y) := by
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => mem_upair.2 (sat_or.1 ((sat_iff.1 (h v (hN.trans (he w) hv))).1 hv)),
      fun hv => ?_⟩
    refine Stable.of_nn (mem_upair.1 hv) fun
      | .inl ev => (sat_iff.1 (h v (hN.resp ev.symm (he x)))).2 (sat_or.2 (nn_intro (.inl ev)))
      | .inr ev => (sat_iff.1 (h v (hN.resp ev.symm (he y)))).2 (sat_or.2 (nn_intro (.inr ev)))
  · exact fun h v _ => sat_iff.2 (((mem_congr_right h).trans mem_upair).trans
      (sat_or (M := N) (φ := eq 0 (x+1)) (ψ := eq 0 (y+1)) (e := Env.cons v e)).symm)

theorem sat_pairF (p x y : Nat) : Sat N (pairF p x y) e ↔ e p ≈ PSet.pair (e x) (e y) := by
  have key : ∀ v, N v → (Sat N (or (singF 0 (x+1)) (upairF 0 (x+1) (y+1))) (Env.cons v e) ↔
      v ∈ PSet.pair (e x) (e y)) := fun v hv => by
    have he' : ∀ i, N (Env.cons v e i) := Env.cons_mem hv he
    refine sat_or.trans (.trans (nn_congr (or_congr (hN.sat_singF he' 0 (x+1))
      (hN.sat_upairF he' 0 (x+1) (y+1)))) mem_upair.symm)
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => (key v (hN.trans (he p) hv)).1 ((sat_iff.1 (h v (hN.trans (he p) hv))).1 hv),
      fun hv => ?_⟩
    refine Stable.of_nn (mem_upair.1 hv) fun
      | .inl ev => ?_
      | .inr ev => ?_
    · have hvN : N v := hN.resp ev.symm (hN.single_mem (he x))
      exact (sat_iff.1 (h v hvN)).2 ((key v hvN).2 hv)
    · have hvN : N v := hN.resp ev.symm (hN.upair (he x) (he y))
      exact (sat_iff.1 (h v hvN)).2 ((key v hvN).2 hv)
  · exact fun h v hv => sat_iff.2 ((mem_congr_right h).trans (key v hv).symm)

theorem sat_pairMemF (f x y : Nat) : Sat N (pairMemF f x y) e ↔ PSet.pair (e x) (e y) ∈ e f := by
  refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨p, hp, hs⟩ => ?_, fun h => ?_⟩
  · have ⟨h1, h2⟩ := sat_and.1 hs
    exact (mem_congr_left ((hN.sat_pairF (Env.cons_mem hp he) 0 (x+1) (y+1)).1 h1)).1 h2
  · refine nn_intro ⟨PSet.pair (e x) (e y), hN.pair_mem (he x) (he y), sat_and.2 ⟨?_, h⟩⟩
    exact (hN.sat_pairF (Env.cons_mem (hN.pair_mem (he x) (he y)) he) 0 (x+1) (y+1)).2 (Equiv.refl _)

theorem sat_transF (x : Nat) : Sat N (transF x) e ↔ Trans (e x) :=
  ⟨fun h y hy z hz => h y (hN.trans (he x) hy) z (hN.trans (hN.trans (he x) hy) hz) hz hy,
   fun h y _ z _ hz hy => h y hy z hz⟩

theorem sat_ordF (x : Nat) : Sat N (ordF x) e ↔ IsOrd (e x) := by
  refine sat_and.trans ⟨fun ⟨h1, h2⟩ => ⟨(hN.sat_transF he x).1 h1, fun y hy => ?_⟩,
    fun h => ⟨(hN.sat_transF he x).2 h.trans, fun y hy hyx => ?_⟩⟩
  · exact (hN.sat_transF (Env.cons_mem (hN.trans (he x) hy) he) 0).1 (h2 y (hN.trans (he x) hy) hy)
  · exact (hN.sat_transF (Env.cons_mem hy he) 0).2 (h.mem_trans y hyx)

/-- A syntactic function is a set-coded function. -/
theorem isFun_of_sat (f d c : Nat) (h : Sat N (funF f d c) e) : IsFun (e f) (e d) (e c) := by
  have ⟨h1, h2, h3⟩ := sat_and.1 h |>.imp id sat_and.1
  refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun x hx => ?_⟩
  · have hpN : N (pair x y) := hN.trans (he f) hp
    refine Stable.of_nn (sat_ex.1 (h1 _ hpN hp)) fun ⟨x', hx', hs⟩ => ?_
    have ⟨hxd, hs⟩ := sat_and.1 hs
    refine Stable.of_nn (sat_ex.1 hs) fun ⟨y', hy', hs⟩ => ?_
    have ⟨hyc, hs⟩ := sat_and.1 hs
    have ⟨ex, ey⟩ := pair_inj ((hN.sat_pairF (Env.cons_mem hy' (Env.cons_mem hx' (Env.cons_mem hpN he)))
      2 1 0).1 hs)
    exact ⟨(mem_congr_left ex).2 hxd, (mem_congr_left ey).2 hyc⟩
  · have ⟨hx, hy⟩ := hN.of_pair_mem (he f) hp
    have hy' := (hN.of_pair_mem (he f) hp').2
    have he3 : ∀ i, N (Env.cons y' (Env.cons y (Env.cons x e)) i) :=
      Env.cons_mem hy' (Env.cons_mem hy (Env.cons_mem hx he))
    exact h3 x hx y hy y' hy' ((hN.sat_pairMemF he3 (f+3) 2 1).2 hp) ((hN.sat_pairMemF he3 (f+3) 2 0).2 hp')
  · have hxN := hN.trans (he d) hx
    refine Stable.of_nn (sat_ex.1 (h2 x hxN hx)) fun ⟨y, hy, hs⟩ => ?_
    exact nn_intro ⟨y, (hN.sat_pairMemF (Env.cons_mem hy (Env.cons_mem hxN he)) (f+2) 1 0).1 hs⟩

/-- A syntactic injection satisfies the relational injection condition. -/
theorem isInjRel_of_sat (f a b : Nat) (h : Sat N (injF f a b) e) : IsInjRel (e a) (e b) (e f) := by
  have ⟨h1, h2⟩ := sat_and.1 h
  have hf := hN.isFun_of_sat he f a b h1
  refine ⟨fun ξ hξ => nn_map (fun ⟨w, hp⟩ => ⟨w, (hf.1 ξ w hp).2, hp⟩) (hf.2.2 ξ hξ),
    fun ξ ξ' w w' hp hp' ew => ?_⟩
  have ⟨hξ, hw⟩ := hN.of_pair_mem (he f) hp
  have ⟨hξ', hw'⟩ := hN.of_pair_mem (he f) hp'
  have he4 : ∀ i, N (Env.cons w' (Env.cons w (Env.cons ξ' (Env.cons ξ e))) i) :=
    Env.cons_mem hw' (Env.cons_mem hw (Env.cons_mem hξ' (Env.cons_mem hξ he)))
  exact h2 ξ hξ ξ' hξ' w hw w' hw' ((hN.sat_pairMemF he4 (f+4) 3 1).2 hp)
    ((hN.sat_pairMemF he4 (f+4) 2 0).2 hp') ew

/-- A syntactic powerset is included in the ambient one. -/
theorem powerset_of_sat (P l : Nat) (h : Sat N (powF P l) e) : ∀ w, w ∈ e P → w ∈ powerset (e l) :=
  fun w hw => mem_powerset.2 fun z hz =>
    (sat_iff.1 (h w (hN.trans (he P) hw))).1 hw z (hN.trans (hN.trans (he P) hw) hz) hz

theorem sat_omegaLtF (k : Nat) (h : omega ∈ e k) : Sat N (omegaLtF k) e := by
  have hω : N omega := hN.trans (he k) h
  refine sat_ex.2 (nn_intro ⟨omega, hω, sat_and.2 ⟨h, sat_and.2 ⟨?_, fun y hy hyω => ?_⟩⟩⟩)
  · exact sat_ex.2 (nn_intro ⟨empty, hN.trans hω (ofNat_mem_omega 0), ofNat_mem_omega 0⟩)
  · refine Stable.of_nn (mem_omega.1 hyω) fun ⟨n, e'⟩ => ?_
    have hs : succ y ∈ omega := (mem_congr_left (succ_congr e')).2 (ofNat_mem_omega (n+1))
    refine sat_ex.2 (nn_intro ⟨succ y, hN.trans hω hs, sat_and.2 ⟨hs, fun z _ => sat_iff.2 ?_⟩⟩)
    exact mem_succ.trans (sat_or (M := N) (φ := mem 0 2) (ψ := eq 0 2)
      (e := Env.cons z (Env.cons (succ y) (Env.cons y (Env.cons omega e))))).symm

theorem sat_regF (k : Nat) (h : RegularIn N (e k)) : Sat N (regF k) e := by
  intro δ hδ hδk f hf hfun
  have he2 : ∀ i, N (Env.cons f (Env.cons δ e) i) := Env.cons_mem hf (Env.cons_mem hδ he)
  have hF := hN.isFun_of_sat he2 0 1 (k+2) hfun
  refine Stable.of_nn (h δ f hδk hf hF) fun ⟨β, hβ, hb⟩ => ?_
  have hβN := hN.trans (he k) hβ
  refine sat_ex.2 (nn_intro ⟨β, hβN, sat_and.2 ⟨hβ, fun x hx y hy hp => ?_⟩⟩)
  exact hb x y ((hN.sat_pairMemF (Env.cons_mem hy (Env.cons_mem hx (Env.cons_mem hβN he2))) 3 1 0).1 hp)

theorem sat_initialF (k : Nat) (h : InitialIn N (e k)) : Sat N (initialF k) e :=
  fun δ hδ hδk f hf hinj => h δ f hδk hf
    (hN.isInjRel_of_sat (Env.cons_mem hf (Env.cons_mem hδ he)) 0 (k+2) 1 hinj)

theorem sat_strongLimitF (k : Nat) (h : StrongLimitIn N (e k)) : Sat N (strongLimitF k) e := by
  intro lam hlam hlamk P hP hpow θ hθ hord f hf hinj
  have he4 : ∀ i, N (Env.cons f (Env.cons θ (Env.cons P (Env.cons lam e))) i) :=
    Env.cons_mem hf (Env.cons_mem hθ (Env.cons_mem hP (Env.cons_mem hlam he)))
  exact h lam θ P f hlamk ((hN.sat_ordF (Env.cons_mem hθ (Env.cons_mem hP (Env.cons_mem hlam he))) 0).1 hord)
    hP hf (hN.powerset_of_sat (Env.cons_mem hP (Env.cons_mem hlam he)) 0 1 hpow)
    (hN.isInjRel_of_sat he4 0 1 2 hinj)

/-- **The main bridge**: inaccessibility in `N` implies the syntactic sentence. -/
theorem sat_inaccF_of_inaccIn (k : Nat) (h : InaccIn N (e k)) : Sat N (inaccF k) e :=
  have ⟨h1, h2, h3, h4, h5⟩ := h
  sat_and.2 ⟨(hN.sat_ordF he k).2 h1, sat_and.2 ⟨hN.sat_omegaLtF he k h2, sat_and.2
    ⟨hN.sat_initialF he k h3, sat_and.2 ⟨hN.sat_regF he k h4, hN.sat_strongLimitF he k h5⟩⟩⟩⟩

end TransClass

/-! ### Conditional consistency -/

/-- **Conditional consistency of `ZFC + ∃ inaccessible`.** The premises: excluded middle; an
upper-model interface `M`; its class transitive, respecting bisimulation, and closed under
unordered pairs; and validity in it of the syntactic `ZF` axioms and of choice. -/
theorem con_ZFCI (em : ∀ p : Prop, p ∨ ¬p) (M : UpperModel.{u}) (hT : TransClass M.N)
    (hZF : ∀ φ, ZF φ → Valid M.N φ) (hac : Valid M.N ac) : Con ZFCI := by
  refine Con.of_model (fun φ h => ?_) K.{u} M.N_K
  cases h with
  | zf h => exact hZF _ h
  | ac => exact hac
  | inacc =>
    intro e he
    obtain ⟨ρ, hρ, _, _, hi⟩ := inacc_interval M empty em
    exact sat_ex.2 (nn_intro ⟨ρ, hρ, hT.sat_inaccF_of_inaccIn (Env.cons_mem hρ he) 0 hi⟩)

/-- info: 'PSet.con_ZFCI' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI
/-- info: 'PSet.TransClass.sat_inaccF_of_inaccIn' does not depend on any axioms -/
#guard_msgs in #print axioms TransClass.sat_inaccF_of_inaccIn

/-- **Conditional consistency from negative accessibility of `K`**, without excluded middle. -/
theorem con_ZFCI_of_nnacc (hK : NNAccK.{u}) (M : UpperModel.{u}) (hT : TransClass M.N)
    (hZF : ∀ φ, ZF φ → Valid M.N φ) (hac : Valid M.N ac) : Con ZFCI := by
  refine Con.of_model (fun φ h => ?_) K.{u} M.N_K
  cases h with
  | zf h => exact hZF _ h
  | ac => exact hac
  | inacc =>
    intro e he
    refine Stable.of_nn (inacc_interval_nnacc M empty hK) fun ⟨ρ, hρ, _, _, hi⟩ => ?_
    exact sat_ex.2 (nn_intro ⟨ρ, hρ, hT.sat_inaccF_of_inaccIn (Env.cons_mem hρ he) 0 hi⟩)

/-- info: 'PSet.con_ZFCI_of_nnacc' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_nnacc

end PSet
