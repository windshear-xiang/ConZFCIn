import Vendor.ConZF.InternalZF
/-!
Internal ω-recursion (a prerequisite of conzf15 gate 2). For a native formula `step` (input
variable `0`, output `1`, parameters from `2`) that is functional and total on a `SynZF` class,
and a start `a`, the partial sequences (`partSeqF`: functions on a numeral with the recursion
equations) exist for every numeral and agree wherever both are defined; collection then gives
the sequence `s` as the union of all partial sequences on the successors of members of `ω`,
specified by the formula `seqF step` (variables: `0` the sequence, `1` the start, `2` `ω`,
parameters from `3`). The sequence exists in the class (`seq_exists`), is unique up to
bisimulation (`seq_unique`), and satisfies the recursion (`seq_spec`): its members are pairs
with first component in `ω`, it is functional and total on `ω`, starts at `a`, and consecutive
values are related by `step`. Everything is stated with the formula, so later constructions
may quantify over "the" sequence inside formulas.
-/
universe u

namespace PSet
open Fml CardF

namespace RecF

/-- `z = ∅`. -/
def emptyF (z : Nat) : Fml := all (neg (mem 0 (z+1)))

/-- `s = succ i`. -/
def succF (s i : Nat) : Fml := all (iff (mem 0 (s+1)) (or (mem 0 (i+1)) (eq 0 (i+1))))

/-- Renaming placing the step's input at `iv`, output at `iw`, parameter `k` at `k + sh`. -/
def stepRen (iv iw sh : Nat) : Nat → Nat
  | 0 => iv
  | 1 => iw
  | k+2 => k + sh

/-- `p` is a partial sequence on the numeral `n` starting at `a`: a pure function on `n`,
`p(∅) = a`, and `step (p i) (p (succ i))` whenever `succ i ∈ n`. Step parameters at `k + sh`. -/
def partSeqF (step : Fml) (p n a sh : Nat) : Fml :=
  and (all (imp (mem 0 (p+1)) (ex (and (mem 0 (n+2)) (ex (pairF 2 1 0))))))
    (and (all (imp (mem 0 (n+1)) (ex (pairMemF (p+2) 1 0))))
      (and (all (all (all (imp (pairMemF (p+3) 2 1) (imp (pairMemF (p+3) 2 0) (eq 1 0))))))
        (and (all (all (imp (emptyF 1) (imp (pairMemF (p+2) 1 0) (eq 0 (a+2))))))
          (all (all (all (all (imp (succF 2 3) (imp (mem 2 (n+4)) (imp (pairMemF (p+4) 3 1)
            (imp (pairMemF (p+4) 2 0) (rename (stepRen 1 0 (sh+4)) step))))))))))))

/-- The sequence: `∀ q (q ∈ s ↔ ∃ n ∈ ω, ∃ m, m = succ n ∧ ∃ p, PartSeq p m ∧ q ∈ p)`.
Variables: `0` the sequence, `1` the start, `2` `ω`, step parameters from `3`. -/
def seqF (step : Fml) : Fml :=
  all (iff (mem 0 1) (ex (and (mem 0 4) (ex (and (succF 0 1)
    (ex (and (partSeqF step 0 1 5 7) (mem 3 0))))))))

end RecF

open RecF

/-- The ambient reading of a partial sequence. -/
def PartSeq (M : PSet.{u} → Prop) (step : Fml) (e : Nat → PSet.{u}) (a p n : PSet.{u}) : Prop :=
  (∀ q, q ∈ p → ¬¬∃ i v, i ∈ n ∧ q ≈ pair i v) ∧
  (∀ i, i ∈ n → ¬¬∃ v, pair i v ∈ p) ∧
  (∀ i v v', pair i v ∈ p → pair i v' ∈ p → v ≈ v') ∧
  (∀ v, pair empty v ∈ p → v ≈ a) ∧
  (∀ i v w, pair i v ∈ p → pair (succ i) w ∈ p → Sat M step (Env.cons v (Env.cons w e)))

instance {M : PSet.{u} → Prop} {step : Fml} {e : Nat → PSet.{u}} {a p n : PSet.{u}} :
    Stable (PartSeq M step e a p n) :=
  inferInstanceAs (Stable (_ ∧ _ ∧ _ ∧ _ ∧ ∀ _ _ _, _ → _ → Sat M step _))

theorem succ_mem_omega {n : PSet.{u}} (hn : n ∈ omega) : succ n ∈ omega :=
  Stable.of_nn (mem_omega.1 hn) fun ⟨m, em⟩ =>
    (mem_congr_left (succ_congr em)).2 (ofNat_mem_omega (m+1))

namespace TransClass
variable {M : PSet.{u} → Prop} (hN : TransClass M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hN hE

theorem sat_emptyF (z : Nat) : Sat M (emptyF z) E ↔ E z ≈ empty :=
  ⟨fun h => ext fun w => ⟨fun hw => (h w (hN.trans (hE z) hw) hw).elim, fun hw => (not_mem_empty w hw).elim⟩,
   fun h _ _ hw => not_mem_empty _ ((mem_congr_right h).1 hw)⟩

theorem sat_succF (s i : Nat) : Sat M (succF s i) E ↔ E s ≈ succ (E i) := by
  constructor
  · intro h
    refine ext fun v => ⟨fun hv => mem_succ.2 (sat_or.1 ((sat_iff.1 (h v (hN.trans (hE s) hv))).1 hv)),
      fun hv => ?_⟩
    refine Stable.of_nn (mem_succ.1 hv) fun
      | .inl hv' => (sat_iff.1 (h v (hN.trans (hE i) hv'))).2 (sat_or.2 (nn_intro (.inl hv')))
      | .inr ev => (sat_iff.1 (h v (hN.resp ev.symm (hE i)))).2 (sat_or.2 (nn_intro (.inr ev)))
  · exact fun h v _ => sat_iff.2 (((mem_congr_right h).trans mem_succ).trans
      (sat_or (M := M) (φ := mem 0 (i+1)) (ψ := eq 0 (i+1)) (e := Env.cons v E)).symm)

omit hN hE in
/-- The step, renamed into position, reads as the step at the two values. -/
theorem sat_stepRen (step : Fml) {e : Nat → PSet.{u}} {iv iw sh : Nat} (hsh : ∀ k, E (k + sh) ≈ e k) :
    Sat M (rename (stepRen iv iw sh) step) E ↔ Sat M step (Env.cons (E iv) (Env.cons (E iw) e)) :=
  (sat_rename step _ E).trans (Sat.resp_iff (fun _ => Iff.rfl) step fun i => by
    rcases i with _ | _ | k
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact hsh k)

/-- Clause 1: pure pairs with first component in `n`. -/
theorem sat_pureF (p n : Nat) :
    Sat M (all (imp (mem 0 (p+1)) (ex (and (mem 0 (n+2)) (ex (pairF 2 1 0)))))) E ↔
      ∀ q, q ∈ E p → ¬¬∃ i v, i ∈ E n ∧ q ≈ pair i v := by
  constructor
  · intro h q hq
    refine Stable.of_nn (sat_ex.1 (h q (hN.trans (hE p) hq) hq)) fun ⟨i, hi, hs⟩ => ?_
    have ⟨hin, hs⟩ := sat_and.1 hs
    refine Stable.of_nn (sat_ex.1 hs) fun ⟨v, hv, hs⟩ => ?_
    exact nn_intro ⟨i, v, hin, (hN.sat_pairF (Env.cons_mem hv (Env.cons_mem hi
      (Env.cons_mem (hN.trans (hE p) hq) hE))) 2 1 0).1 hs⟩
  · intro h q hq hq'
    refine sat_ex.2 (nn_bind (h q hq') fun ⟨i, v, hin, e'⟩ => ?_)
    have ⟨hi, hv⟩ := hN.of_pair_mem (hE p) ((mem_congr_left e').1 hq')
    exact nn_intro ⟨i, hi, sat_and.2 ⟨hin, sat_ex.2 (nn_intro ⟨v, hv,
      (hN.sat_pairF (Env.cons_mem hv (Env.cons_mem hi (Env.cons_mem hq hE))) 2 1 0).2 e'⟩)⟩⟩

/-- Clause 2: total on `n`. -/
theorem sat_totalF (p n : Nat) :
    Sat M (all (imp (mem 0 (n+1)) (ex (pairMemF (p+2) 1 0)))) E ↔
      ∀ i, i ∈ E n → ¬¬∃ v, pair i v ∈ E p := by
  constructor
  · intro h i hin
    have hi := hN.trans (hE n) hin
    refine nn_map (fun ⟨v, hv, hs⟩ => ⟨v, ?_⟩) (sat_ex.1 (h i hi hin))
    exact (hN.sat_pairMemF (Env.cons_mem hv (Env.cons_mem hi hE)) (p+2) 1 0).1 hs
  · intro h i hi hin
    refine sat_ex.2 (nn_map (fun ⟨v, hv⟩ => ⟨v, (hN.of_pair_mem (hE p) hv).2, ?_⟩) (h i hin))
    exact (hN.sat_pairMemF (Env.cons_mem (hN.of_pair_mem (hE p) hv).2 (Env.cons_mem hi hE)) (p+2) 1 0).2 hv

/-- Clause 3: functional. -/
theorem sat_funcF (p : Nat) :
    Sat M (all (all (all (imp (pairMemF (p+3) 2 1) (imp (pairMemF (p+3) 2 0) (eq 1 0)))))) E ↔
      ∀ i v v', pair i v ∈ E p → pair i v' ∈ E p → v ≈ v' := by
  constructor
  · intro h i v v' h1 h2
    have ⟨hi, hv⟩ := hN.of_pair_mem (hE p) h1
    have hv' := (hN.of_pair_mem (hE p) h2).2
    have he3 := Env.cons_mem hv' (Env.cons_mem hv (Env.cons_mem hi hE))
    exact h i hi v hv v' hv' ((hN.sat_pairMemF he3 (p+3) 2 1).2 h1) ((hN.sat_pairMemF he3 (p+3) 2 0).2 h2)
  · intro h i hi v hv v' hv' h1 h2
    have he3 := Env.cons_mem hv' (Env.cons_mem hv (Env.cons_mem hi hE))
    exact h i v v' ((hN.sat_pairMemF he3 (p+3) 2 1).1 h1) ((hN.sat_pairMemF he3 (p+3) 2 0).1 h2)

/-- Clause 4: the start. -/
theorem sat_startF (p a : Nat) :
    Sat M (all (all (imp (emptyF 1) (imp (pairMemF (p+2) 1 0) (eq 0 (a+2)))))) E ↔
      ∀ v, pair empty v ∈ E p → v ≈ E a := by
  constructor
  · intro h v hv
    have ⟨h0, hvM⟩ := hN.of_pair_mem (hE p) hv
    have he2 := Env.cons_mem hvM (Env.cons_mem h0 hE)
    exact h empty h0 v hvM ((hN.sat_emptyF he2 1).2 (Equiv.refl _)) ((hN.sat_pairMemF he2 (p+2) 1 0).2 hv)
  · intro h z hz v hv hz0 hzv
    have he2 := Env.cons_mem hv (Env.cons_mem hz hE)
    have e0 := (hN.sat_emptyF he2 1).1 hz0
    exact h v ((mem_congr_left (pair_congr e0 (Equiv.refl _))).1
      ((hN.sat_pairMemF he2 (p+2) 1 0).1 hzv))

/-- Clause 5: the step, given purity and closure of the class under successor. -/
theorem sat_stepF (step : Fml) (p n sh : Nat) {e : Nat → PSet.{u}} (hsh : ∀ k, E (k + sh) ≈ e k)
    (hsucc : ∀ {x}, M x → M (succ x))
    (pure : ∀ q, q ∈ E p → ¬¬∃ i v, i ∈ E n ∧ q ≈ pair i v) :
    Sat M (all (all (all (all (imp (succF 2 3) (imp (mem 2 (n+4)) (imp (pairMemF (p+4) 3 1)
      (imp (pairMemF (p+4) 2 0) (rename (stepRen 1 0 (sh+4)) step))))))))) E ↔
      ∀ i v w, pair i v ∈ E p → pair (succ i) w ∈ E p → Sat M step (Env.cons v (Env.cons w e)) := by
  constructor
  · intro h i v w h1 h2
    have ⟨hi, hv⟩ := hN.of_pair_mem (hE p) h1
    have hw := (hN.of_pair_mem (hE p) h2).2
    have hs : M (succ i) := hsucc hi
    have he4 := Env.cons_mem hw (Env.cons_mem hv (Env.cons_mem hs (Env.cons_mem hi hE)))
    have hsn : succ i ∈ E n := Stable.of_nn (pure _ h2) fun ⟨i', _, hi', e'⟩ =>
      (mem_congr_left (pair_inj e').1).2 hi'
    have h' := h i hi (succ i) hs v hv w hw ((hN.sat_succF he4 2 3).2 (Equiv.refl _)) hsn
      ((hN.sat_pairMemF he4 (p+4) 3 1).2 h1) ((hN.sat_pairMemF he4 (p+4) 2 0).2 h2)
    exact (sat_stepRen (E := Env.cons w (Env.cons v (Env.cons (succ i) (Env.cons i E)))) step
      (e := e) (iv := 1) (iw := 0) (sh := sh + 4) (fun k => hsh k)).1 h'
  · intro h i hi s hs v hv w hw hsi _ h1 h2
    have he4 := Env.cons_mem hw (Env.cons_mem hv (Env.cons_mem hs (Env.cons_mem hi hE)))
    have es := (hN.sat_succF he4 2 3).1 hsi
    have h2' : pair (succ i) w ∈ E p := (mem_congr_left (pair_congr es (Equiv.refl _))).1
      ((hN.sat_pairMemF he4 (p+4) 2 0).1 h2)
    exact (sat_stepRen (E := Env.cons w (Env.cons v (Env.cons s (Env.cons i E)))) step
      (e := e) (iv := 1) (iw := 0) (sh := sh + 4) (fun k => hsh k)).2
      (h i v w ((hN.sat_pairMemF he4 (p+4) 3 1).1 h1) h2')

/-- **The partial-sequence bridge.** -/
theorem sat_partSeqF (step : Fml) (p n a sh : Nat) {e : Nat → PSet.{u}}
    (hsh : ∀ k, E (k + sh) ≈ e k) (hsucc : ∀ {x}, M x → M (succ x)) :
    Sat M (partSeqF step p n a sh) E ↔ PartSeq M step e (E a) (E p) (E n) := by
  constructor
  · intro h
    have ⟨h1, h2, h3, h4, h5⟩ := sat_and.1 h |>.imp id fun h => sat_and.1 h |>.imp id fun h =>
      sat_and.1 h |>.imp id fun h => sat_and.1 h
    have c1 := (hN.sat_pureF hE p n).1 h1
    exact ⟨c1, (hN.sat_totalF hE p n).1 h2, (hN.sat_funcF hE p).1 h3, (hN.sat_startF hE p a).1 h4,
      (hN.sat_stepF hE step p n sh hsh hsucc c1).1 h5⟩
  · intro ⟨c1, c2, c3, c4, c5⟩
    exact sat_and.2 ⟨(hN.sat_pureF hE p n).2 c1, sat_and.2 ⟨(hN.sat_totalF hE p n).2 c2,
      sat_and.2 ⟨(hN.sat_funcF hE p).2 c3, sat_and.2 ⟨(hN.sat_startF hE p a).2 c4,
        (hN.sat_stepF hE step p n sh hsh hsucc c1).2 c5⟩⟩⟩⟩

end TransClass

/-! ### Existence, agreement, and the collected sequence -/

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M) (step : Fml) {e : Nat → PSet.{u}} (he : ∀ i, M (e i))
  (hfun : ∀ x y y', M x → M y → M y' → Sat M step (Env.cons x (Env.cons y e)) →
    Sat M step (Env.cons x (Env.cons y' e)) → y ≈ y')
  (htot : ∀ x, M x → ¬¬∃ y, M y ∧ Sat M step (Env.cons x (Env.cons y e)))
  {a : PSet.{u}} (ha : M a)
include hM

theorem succ_mem {x : PSet.{u}} (hx : M x) : M (succ x) := hM.union hx (hM.single hx)

omit hM in
theorem ofNat_not_mem_self (k : Nat) : ¬ ofNat.{u} k ∈ ofNat k := not_mem_self _

omit hM in
/-- Partial sequences respect bisimulation in the sequence. -/
theorem partSeq_resp {p p' n : PSet.{u}} (ep : p ≈ p') (h : PartSeq M step e a p n) :
    PartSeq M step e a p' n :=
  ⟨fun q hq => h.1 q ((mem_congr_right ep).2 hq),
   fun i hi => nn_map (fun ⟨v, hv⟩ => ⟨v, (mem_congr_right ep).1 hv⟩) (h.2.1 i hi),
   fun i v v' h1 h2 => h.2.2.1 i v v' ((mem_congr_right ep).2 h1) ((mem_congr_right ep).2 h2),
   fun v hv => h.2.2.2.1 v ((mem_congr_right ep).2 hv),
   fun i v w h1 h2 => h.2.2.2.2 i v w ((mem_congr_right ep).2 h1) ((mem_congr_right ep).2 h2)⟩

include hfun in
/-- **Agreement.** Two partial sequences on ordinals agree at every numeral where both are
defined. -/
theorem partSeq_agree {p p' n n' : PSet.{u}} (hp : M p) (hp' : M p') (hn : IsOrd n) (hn' : IsOrd n')
    (h : PartSeq M step e a p n) (h' : PartSeq M step e a p' n') :
    ∀ (m : Nat) (i v v' : PSet.{u}), i ≈ ofNat m → PSet.pair i v ∈ p → PSet.pair i v' ∈ p' → v ≈ v' := by
  have hT := hM.toTransClass
  intro m
  induction m with
  | zero =>
    intro i v v' ei h1 h2
    have e1 := h.2.2.2.1 v ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 h1)
    have e2 := h'.2.2.2.1 v' ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 h2)
    exact e1.trans e2.symm
  | succ m ih =>
    intro i v v' ei h1 h2
    -- the predecessor is in both domains
    have hin : i ∈ n := Stable.of_nn (h.1 _ h1) fun ⟨i', _, hi', e'⟩ =>
      (mem_congr_left (pair_inj e').1).2 hi'
    have hin' : i ∈ n' := Stable.of_nn (h'.1 _ h2) fun ⟨i', _, hi', e'⟩ =>
      (mem_congr_left (pair_inj e').1).2 hi'
    have hm : ofNat m ∈ i := (mem_congr_right ei).2 (self_mem_succ _)
    refine Stable.of_nn (h.2.1 _ (hn.trans i hin _ hm)) fun ⟨u, hu⟩ =>
      Stable.of_nn (h'.2.1 _ (hn'.trans i hin' _ hm)) fun ⟨u', hu'⟩ => ?_
    have eu := ih (ofNat m) u u' (Equiv.refl _) hu hu'
    have s1 := h.2.2.2.2 _ u v hu ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 h1)
    have s2 := h'.2.2.2.2 _ u' v' hu' ((mem_congr_left (pair_congr ei (Equiv.refl _))).1 h2)
    have s2' : Sat M step (Env.cons u (Env.cons v' e)) :=
      Sat.resp step (Env.cons_resp eu.symm fun _ => Equiv.refl _) s2
    exact hfun u v v' (hT.of_pair_mem hp hu).2 (hT.of_pair_mem hp h1).2 (hT.of_pair_mem hp' h2).2 s1 s2'

omit hM in
/-- The first component of a pair in a partial sequence lies in the domain. -/
theorem partSeq_dom {p n i v : PSet.{u}} (h : PartSeq M step e a p n) (hv : PSet.pair i v ∈ p) : i ∈ n :=
  Stable.of_nn (h.1 _ hv) fun ⟨_, _, hi', e'⟩ => (mem_congr_left (pair_inj e').1).2 hi'

omit hM in
/-- The partial sequence on `1`. -/
theorem partSeq_one : PartSeq M step e a (singleton (PSet.pair PSet.empty a)) (ofNat 1) := by
  have mem1 : ∀ q, q ∈ singleton (PSet.pair PSet.empty a) ↔ q ≈ PSet.pair PSet.empty a := fun _ => mem_singleton
  refine ⟨fun q hq => nn_intro ⟨PSet.empty, a, self_mem_succ _, (mem1 q).1 hq⟩, fun i hi => ?_,
    fun i v v' h1 h2 => (pair_inj ((mem1 _).1 h1)).2.trans (pair_inj ((mem1 _).1 h2)).2.symm,
    fun v hv => (pair_inj ((mem1 _).1 hv)).2, fun i v w _ h2 => ?_⟩
  · refine Stable.of_nn (mem_succ.1 hi) fun
      | .inl hi => (not_mem_empty i hi).elim
      | .inr ei => nn_intro ⟨a, (mem1 _).2 (pair_congr ei (Equiv.refl _))⟩
  · exact (not_mem_empty i ((mem_congr_right (pair_inj ((mem1 _).1 h2)).1).1 (self_mem_succ i))).elim

include htot in
/-- **Extension.** A partial sequence on `m + 1` extends to one on `m + 2`. -/
theorem partSeq_extend {p : PSet.{u}} (hp : M p) (m : Nat) (h : PartSeq M step e a p (ofNat (m+1))) :
    ¬¬∃ p', M p' ∧ PartSeq M step e a p' (ofNat (m+2)) := by
  have hT := hM.toTransClass
  refine Stable.of_nn (h.2.1 (ofNat m) (self_mem_succ _)) fun ⟨v₀, hv₀⟩ => ?_
  refine nn_map (fun ⟨w, hw, hs⟩ => ?_) (htot v₀ (hT.of_pair_mem hp hv₀).2)
  let p' := PSet.union p (singleton (PSet.pair (ofNat (m+1)) w))
  have hp' : M p' := hM.union hp (hM.single (hM.pair (hM.trans hM.omega (ofNat_mem_omega _)) hw))
  have memp' : ∀ q, q ∈ p' ↔ ¬¬(q ∈ p ∨ q ≈ PSet.pair (ofNat (m+1)) w) := fun q =>
    mem_union.trans (nn_congr (or_congr Iff.rfl mem_singleton))
  have old : ∀ i v, PSet.pair i v ∈ p → i ∈ ofNat (m+1) := fun _ _ hv => partSeq_dom step h hv
  refine ⟨p', hp', fun q hq => ?_, fun i hi => ?_, fun i v v' h1 h2 => ?_, fun v hv => ?_,
    fun i v w' h1 h2 => ?_⟩
  · refine nn_bind ((memp' q).1 hq) fun
      | .inl hq => nn_map (fun ⟨i, v, hi, e'⟩ => ⟨i, v, mem_succ_of_mem hi, e'⟩) (h.1 q hq)
      | .inr e' => nn_intro ⟨ofNat (m+1), w, self_mem_succ _, e'⟩
  · refine Stable.of_nn (mem_succ.1 hi) fun
      | .inl hi => nn_map (fun ⟨v, hv⟩ => ⟨v, (memp' _).2 (nn_intro (.inl hv))⟩) (h.2.1 i hi)
      | .inr ei => nn_intro ⟨w, (memp' _).2 (nn_intro (.inr (pair_congr ei (Equiv.refl _))))⟩
  · refine Stable.of_nn ((memp' _).1 h1) fun h1 => Stable.of_nn ((memp' _).1 h2) fun h2 => ?_
    rcases h1 with h1 | e1 <;> rcases h2 with h2 | e2
    · exact h.2.2.1 i v v' h1 h2
    · exact (not_mem_self _ ((mem_congr_left (pair_inj e2).1).1 (old i v h1))).elim
    · exact (not_mem_self _ ((mem_congr_left (pair_inj e1).1).1 (old i v' h2))).elim
    · exact (pair_inj e1).2.trans (pair_inj e2).2.symm
  · refine Stable.of_nn ((memp' _).1 hv) fun
      | .inl hv => h.2.2.2.1 v hv
      | .inr e' => (not_mem_empty _ ((mem_congr_right (pair_inj e').1).2 (self_mem_succ (ofNat m)))).elim
  · refine Stable.of_nn ((memp' _).1 h1) fun h1 => Stable.of_nn ((memp' _).1 h2) fun h2 => ?_
    rcases h1 with h1 | e1 <;> rcases h2 with h2 | e2
    · exact h.2.2.2.2 i v w' h1 h2
    · have es : succ i ≈ succ (ofNat m) := (pair_inj e2).1
      have ei : i ≈ ofNat m := succ_inj es
      have hv : PSet.pair (ofNat m) v ∈ p := (mem_congr_left (pair_congr ei (Equiv.refl _))).1 h1
      have ev := h.2.2.1 _ v v₀ hv hv₀
      exact Sat.resp step (Env.cons_resp ev.symm (Env.cons_resp (pair_inj e2).2.symm fun _ => Equiv.refl _)) hs
    · exact (not_mem_self _ ((mem_congr_left (pair_inj e1).1).1
        ((isOrd_ofNat _).trans _ (old _ w' h2) _ (self_mem_succ i)))).elim
    · exact (not_mem_self (ofNat (m+1)) ((mem_congr_left (pair_inj e1).1).1
        ((mem_congr_right (pair_inj e2).1).1 (self_mem_succ i)))).elim

include htot ha in
/-- **Existence.** A partial sequence on every numeral. -/
theorem partSeq_exists : ∀ k : Nat, ¬¬∃ p, M p ∧ PartSeq M step e a p (ofNat k)
  | 0 => nn_intro ⟨PSet.empty, hM.empty, fun q hq => (not_mem_empty q hq).elim,
      fun i hi => (not_mem_empty i hi).elim, fun _ _ _ h => (not_mem_empty _ h).elim,
      fun _ h => (not_mem_empty _ h).elim, fun _ _ _ h => (not_mem_empty _ h).elim⟩
  | 1 => nn_intro ⟨_, hM.single (hM.pair hM.empty ha), partSeq_one step⟩
  | k+2 => nn_bind (partSeq_exists (k+1)) fun ⟨_, hp, h⟩ => hM.partSeq_extend step htot hp k h

omit hM in
theorem partSeq_resp_dom {p n n' : PSet.{u}} (en : n ≈ n') (h : PartSeq M step e a p n) :
    PartSeq M step e a p n' :=
  ⟨fun q hq => nn_map (fun ⟨i, v, hi, e'⟩ => ⟨i, v, (mem_congr_right en).1 hi, e'⟩) (h.1 q hq),
   fun i hi => h.2.1 i ((mem_congr_right en).2 hi), h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

include hfun in
/-- Two partial sequences on the same successor of a natural number are equal. -/
theorem partSeq_unique {p p' n : PSet.{u}} (hp : M p) (hp' : M p') (hn : n ∈ PSet.omega)
    (h : PartSeq M step e a p (succ n)) (h' : PartSeq M step e a p' (succ n)) : p ≈ p' := by
  have hno : IsOrd (succ n) := (isOrd_omega.mem hn).succ
  have agree := hM.partSeq_agree step hfun hp hp' hno hno h h'
  have agree' := hM.partSeq_agree step hfun hp' hp hno hno h' h
  refine ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · refine Stable.of_nn (h.1 q hq) fun ⟨i, v, hi, e'⟩ => ?_
    have hv : PSet.pair i v ∈ p := (mem_congr_left e').1 hq
    refine Stable.of_nn (h'.2.1 i hi) fun ⟨v', hv'⟩ => ?_
    refine Stable.of_nn (mem_omega.1 (isOrd_omega.trans _ (succ_mem_omega hn) i hi)) fun ⟨m, em⟩ => ?_
    exact (mem_congr_left (e'.trans (pair_congr (Equiv.refl _) (agree m i v v' em hv hv')))).2 hv'
  · refine Stable.of_nn (h'.1 q hq) fun ⟨i, v, hi, e'⟩ => ?_
    have hv : PSet.pair i v ∈ p' := (mem_congr_left e').1 hq
    refine Stable.of_nn (h.2.1 i hi) fun ⟨v', hv'⟩ => ?_
    refine Stable.of_nn (mem_omega.1 (isOrd_omega.trans _ (succ_mem_omega hn) i hi)) fun ⟨m, em⟩ => ?_
    exact (mem_congr_left (e'.trans (pair_congr (Equiv.refl _) (agree' m i v v' em hv hv')))).2 hv'

/-- The formula "`y` is a partial sequence on `succ x`" (variables `x = 0`, `y = 1`, `ω = 2`,
`a = 3`, parameters from `4`). -/
def collectF : Fml := ex (and (succF 0 1) (partSeqF step 2 0 4 5))

/-- The formula "`q` is in a partial sequence on the successor of a member of `ω`" (variables
`q = 0`, `b = 1`, `ω = 2`, `a = 3`, parameters from `4`). -/
def memberF : Fml := ex (and (mem 0 3) (ex (and (succF 0 1) (partSeqF step 2 0 5 6))))

include he ha in
theorem sat_collectF {x y : PSet.{u}} (hx : M x) (hy : M y) :
    Sat M (collectF step) (Env.cons x (Env.cons y (Env.cons PSet.omega (Env.cons a e)))) ↔
      PartSeq M step e a y (succ x) := by
  have hT := hM.toTransClass
  have hE := Env.cons_mem hx (Env.cons_mem hy (Env.cons_mem hM.omega (Env.cons_mem ha he)))
  refine sat_ex.trans ⟨fun h => Stable.of_nn h fun ⟨m, hm, hs⟩ => ?_, fun h => ?_⟩
  · have hE' := Env.cons_mem hm hE
    have ⟨h1, h2⟩ := sat_and.1 hs
    have em := (hT.sat_succF hE' 0 1).1 h1
    exact partSeq_resp_dom step em ((hT.sat_partSeqF hE' step 2 0 4 5 (fun _ => Equiv.refl _) hM.succ_mem).1 h2)
  · have hE' := Env.cons_mem (hM.succ_mem hx) hE
    exact nn_intro ⟨succ x, hM.succ_mem hx, sat_and.2 ⟨(hT.sat_succF hE' 0 1).2 (Equiv.refl _),
      (hT.sat_partSeqF hE' step 2 0 4 5 (fun _ => Equiv.refl _) hM.succ_mem).2 h⟩⟩

include he ha in
theorem sat_memberF {q b : PSet.{u}} (hq : M q) (hb : M b) :
    Sat M (memberF step) (Env.cons q (Env.cons b (Env.cons PSet.omega (Env.cons a e)))) ↔
      ¬¬∃ n, n ∈ PSet.omega ∧ PartSeq M step e a q (succ n) := by
  have hT := hM.toTransClass
  have hE := Env.cons_mem hq (Env.cons_mem hb (Env.cons_mem hM.omega (Env.cons_mem ha he)))
  refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨n, hn, hs⟩ => ?_, fun h => nn_bind h fun ⟨n, hnω, hp⟩ => ?_⟩
  · have ⟨hnω, hs⟩ := sat_and.1 hs
    have hE1 := Env.cons_mem hn hE
    refine nn_map (fun ⟨m, hm, hs⟩ => ?_) (sat_ex.1 hs)
    have hE2 := Env.cons_mem hm hE1
    have ⟨h1, h2⟩ := sat_and.1 hs
    have em := (hT.sat_succF hE2 0 1).1 h1
    exact ⟨n, hnω, partSeq_resp_dom step em
      ((hT.sat_partSeqF hE2 step 2 0 5 6 (fun _ => Equiv.refl _) hM.succ_mem).1 h2)⟩
  · have hn := hM.trans hM.omega hnω
    have hE1 := Env.cons_mem hn hE
    have hE2 := Env.cons_mem (hM.succ_mem hn) hE1
    exact nn_intro ⟨n, hn, sat_and.2 ⟨hnω, sat_ex.2 (nn_intro ⟨succ n, hM.succ_mem hn, sat_and.2
      ⟨(hT.sat_succF hE2 0 1).2 (Equiv.refl _),
       (hT.sat_partSeqF hE2 step 2 0 5 6 (fun _ => Equiv.refl _) hM.succ_mem).2 hp⟩⟩)⟩⟩

include he ha in
/-- **The sequence bridge.** -/
theorem sat_seqF {s : PSet.{u}} (hs : M s) :
    Sat M (seqF step) (Env.cons s (Env.cons a (Env.cons PSet.omega e))) ↔
      ∀ q, M q → (q ∈ s ↔ ¬¬∃ n, n ∈ PSet.omega ∧ ¬¬∃ p, M p ∧ PartSeq M step e a p (succ n) ∧ q ∈ p) := by
  have hT := hM.toTransClass
  have hE := Env.cons_mem hs (Env.cons_mem ha (Env.cons_mem hM.omega he))
  refine forall_congr' fun q => forall_congr' fun hq => ?_
  have hE1 := Env.cons_mem hq hE
  suffices hx : Sat M (ex (and (mem 0 4) (ex (and (succF 0 1) (ex (and (partSeqF step 0 1 5 7) (mem 3 0)))))))
      (Env.cons q (Env.cons s (Env.cons a (Env.cons PSet.omega e)))) ↔
      ¬¬∃ n, n ∈ PSet.omega ∧ ¬¬∃ p, M p ∧ PartSeq M step e a p (succ n) ∧ q ∈ p from
    sat_iff.trans ⟨fun h => h.trans hx, fun h => h.trans hx.symm⟩
  refine sat_ex.trans (nn_congr (exists_congr fun n => ?_))
  constructor
  · rintro ⟨hn, hs⟩
    have ⟨hnω, hs⟩ := sat_and.1 hs
    have hE2 := Env.cons_mem hn hE1
    refine ⟨hnω, nn_bind (sat_ex.1 hs) fun ⟨m, hm, hs⟩ => ?_⟩
    have hE3 := Env.cons_mem hm hE2
    have ⟨h1, hs⟩ := sat_and.1 hs
    have em := (hT.sat_succF hE3 0 1).1 h1
    refine nn_map (fun ⟨p, hp, hs⟩ => ?_) (sat_ex.1 hs)
    have hE4 := Env.cons_mem hp hE3
    have ⟨h2, h3⟩ := sat_and.1 hs
    exact ⟨p, hp, partSeq_resp_dom step em
      ((hT.sat_partSeqF hE4 step 0 1 5 7 (fun _ => Equiv.refl _) hM.succ_mem).1 h2), h3⟩
  · rintro ⟨hnω, h⟩
    have hn := hM.trans hM.omega hnω
    have hE2 := Env.cons_mem hn hE1
    have hE3 := Env.cons_mem (hM.succ_mem hn) hE2
    refine ⟨hn, sat_and.2 ⟨hnω, sat_ex.2 (nn_intro ⟨succ n, hM.succ_mem hn, sat_and.2
      ⟨(hT.sat_succF hE3 0 1).2 (Equiv.refl _), sat_ex.2 (nn_map (fun ⟨p, hp, h1, h2⟩ => ?_) h)⟩⟩)⟩⟩
    have hE4 := Env.cons_mem hp hE3
    exact ⟨p, hp, sat_and.2 ⟨(hT.sat_partSeqF hE4 step 0 1 5 7 (fun _ => Equiv.refl _) hM.succ_mem).2 h1, h2⟩⟩

include he hfun ha in
/-- **Existence of the sequence.** -/
theorem seq_exists : ¬¬∃ s, M s ∧ Sat M (seqF step) (Env.cons s (Env.cons a (Env.cons PSet.omega e))) := by
  have hT := hM.toTransClass
  have he₁ : ∀ i, M (Env.cons PSet.omega (Env.cons a e) i) := Env.cons_mem hM.omega (Env.cons_mem ha he)
  -- collect the partial sequences on successors of members of `ω`
  have hcoll := hM.replM (collectF step) he₁ fun x y y' hx hy hy' h1 h2 =>
    hM.partSeq_unique step hfun hy hy' hx ((hM.sat_collectF step he ha (hM.trans hM.omega hx) hy).1 h1)
      ((hM.sat_collectF step he ha (hM.trans hM.omega hx) hy').1 h2)
  refine nn_map (fun ⟨b, hb, hbs⟩ => ?_) hcoll
  have he₂ : ∀ i, M (Env.cons b (Env.cons PSet.omega (Env.cons a e)) i) := Env.cons_mem hb he₁
  let P : PSet.{u} → Prop := fun q => Sat M (memberF step) (Env.cons q (Env.cons b (Env.cons PSet.omega (Env.cons a e))))
  have hP : ∀ q q' : PSet.{u}, q ≈ q' → P q → P q' := fun _ _ e' h =>
    Sat.resp _ (Env.cons_resp e' fun _ => Equiv.refl _) h
  have hS : M (sep P b) := hM.sepM (memberF step) he₂
  refine ⟨_, hM.sUnion hS, (hM.sat_seqF step he ha (hM.sUnion hS)).2 fun q hq => ?_⟩
  constructor
  · intro h
    refine nn_bind (mem_sUnion.1 h) fun ⟨p, hp, hqp⟩ => ?_
    have ⟨hpb, hPp⟩ := (mem_sep hP).1 hp
    have hpM := hM.trans hb hpb
    exact nn_map (fun ⟨n, hn, hps⟩ => ⟨n, hn, nn_intro ⟨p, hpM, hps, hqp⟩⟩)
      ((hM.sat_memberF step he ha hpM hb).1 hPp)
  · intro h
    refine mem_sUnion.2 (nn_bind h fun ⟨n, hnω, h⟩ => nn_map (fun ⟨p, hp, hps, hqp⟩ => ?_) h)
    have hpb : p ∈ b := hbs n p hnω hp ((hM.sat_collectF step he ha (hM.trans hM.omega hnω) hp).2 hps)
    exact ⟨p, (mem_sep hP).2 ⟨hpb, (hM.sat_memberF step he ha hp hb).2 (nn_intro ⟨n, hnω, hps⟩)⟩, hqp⟩

include he ha in
/-- **Uniqueness of the sequence.** -/
theorem seq_unique {s s' : PSet.{u}} (hs : M s) (hs' : M s')
    (h : Sat M (seqF step) (Env.cons s (Env.cons a (Env.cons PSet.omega e))))
    (h' : Sat M (seqF step) (Env.cons s' (Env.cons a (Env.cons PSet.omega e)))) : s ≈ s' :=
  have h1 := (hM.sat_seqF step he ha hs).1 h
  have h2 := (hM.sat_seqF step he ha hs').1 h'
  ext fun q => ⟨fun hq => (h2 q (hM.trans hs hq)).2 ((h1 q (hM.trans hs hq)).1 hq),
    fun hq => (h1 q (hM.trans hs' hq)).2 ((h2 q (hM.trans hs' hq)).1 hq)⟩

include he hfun htot ha in
/-- **The recursion equations** of the sequence: pure pairs on `ω`, functional, total on `ω`,
starting at `a`, with consecutive values related by `step`. -/
theorem seq_spec {s : PSet.{u}} (hs : M s)
    (h : Sat M (seqF step) (Env.cons s (Env.cons a (Env.cons PSet.omega e)))) :
    (∀ q, q ∈ s → ¬¬∃ n v, n ∈ PSet.omega ∧ q ≈ PSet.pair n v) ∧
    PSet.pair PSet.empty a ∈ s ∧
    (∀ n v v', PSet.pair n v ∈ s → PSet.pair n v' ∈ s → v ≈ v') ∧
    (∀ n, n ∈ PSet.omega → ¬¬∃ v, PSet.pair n v ∈ s) ∧
    (∀ n v w, PSet.pair n v ∈ s → PSet.pair (succ n) w ∈ s → Sat M step (Env.cons v (Env.cons w e))) := by
  have hT := hM.toTransClass
  have hsp := (hM.sat_seqF step he ha hs).1 h
  -- membership in `s`, opened
  have open_mem : ∀ q, q ∈ s → ¬¬∃ n p, n ∈ PSet.omega ∧ M p ∧ PartSeq M step e a p (succ n) ∧ q ∈ p :=
    fun q hq => nn_bind ((hsp q (hM.trans hs hq)).1 hq) fun ⟨n, hn, h⟩ =>
      nn_map (fun ⟨p, hp, h1, h2⟩ => ⟨n, p, hn, hp, h1, h2⟩) h
  have close_mem : ∀ q n p, n ∈ PSet.omega → M p → PartSeq M step e a p (succ n) → q ∈ p → q ∈ s :=
    fun q n p hn hp h1 h2 => (hsp q (hM.trans hp h2)).2 (nn_intro ⟨n, hn, nn_intro ⟨p, hp, h1, h2⟩⟩)
  -- agreement of two partial sequences at a member of `ω`
  have agree : ∀ {n p p' v v'} {n₁ n₂ : PSet.{u}}, n ∈ PSet.omega → M p → M p' → n₁ ∈ PSet.omega → n₂ ∈ PSet.omega →
      PartSeq M step e a p (succ n₁) → PartSeq M step e a p' (succ n₂) →
      PSet.pair n v ∈ p → PSet.pair n v' ∈ p' → v ≈ v' := fun {n p p' v v' n₁ n₂} hn hp hp' h₁ h₂ hps hps' hv hv' =>
    Stable.of_nn (mem_omega.1 hn) fun ⟨m, em⟩ =>
      hM.partSeq_agree step hfun hp hp' (isOrd_omega.mem h₁).succ (isOrd_omega.mem h₂).succ hps hps' m n v v' em hv hv'
  refine ⟨fun q hq => ?_, ?_, fun n v v' h1 h2 => ?_, fun n hn => ?_, fun n v w h1 h2 => ?_⟩
  · refine Stable.of_nn (open_mem q hq) fun ⟨n, p, hn, _, hps, hqp⟩ => ?_
    exact nn_map (fun ⟨i, v, hi, e'⟩ => ⟨i, v, isOrd_omega.trans _ (succ_mem_omega hn) i hi, e'⟩) (hps.1 q hqp)
  · refine Stable.of_nn (hM.partSeq_exists step htot ha 1) fun ⟨p, hp, hps⟩ => ?_
    refine Stable.of_nn (hps.2.1 PSet.empty (self_mem_succ _)) fun ⟨v, hv⟩ => ?_
    have ev := hps.2.2.2.1 v hv
    exact close_mem _ PSet.empty p (ofNat_mem_omega 0) hp hps ((mem_congr_left (pair_congr (Equiv.refl _) ev)).1 hv)
  · refine Stable.of_nn (open_mem _ h1) fun ⟨n₁, p, hn₁, hp, hps, hv⟩ =>
      Stable.of_nn (open_mem _ h2) fun ⟨n₂, p', hn₂, hp', hps', hv'⟩ => ?_
    have hnω : n ∈ PSet.omega := isOrd_omega.trans _ (succ_mem_omega hn₁) n (partSeq_dom step hps hv)
    exact agree hnω hp hp' hn₁ hn₂ hps hps' hv hv'
  · refine Stable.of_nn (mem_omega.1 hn) fun ⟨m, em⟩ => ?_
    refine Stable.of_nn (hM.partSeq_exists step htot ha (m+1)) fun ⟨p, hp, hps⟩ => ?_
    have hps' : PartSeq M step e a p (succ n) := partSeq_resp_dom step (succ_congr em.symm) hps
    exact nn_map (fun ⟨v, hv⟩ => ⟨v, close_mem _ n p hn hp hps' hv⟩) (hps'.2.1 n (self_mem_succ n))
  · refine Stable.of_nn (open_mem _ h1) fun ⟨n₁, p, hn₁, hp, hps, hv⟩ =>
      Stable.of_nn (open_mem _ h2) fun ⟨n₂, p', hn₂, hp', hps', hw⟩ => ?_
    have hsn : succ n ∈ succ n₂ := partSeq_dom step hps' hw
    have hn : n ∈ succ n₂ := (isOrd_omega.mem hn₂).succ.trans _ hsn n (self_mem_succ n)
    have hnω : n ∈ PSet.omega := isOrd_omega.trans _ (succ_mem_omega hn₂) n hn
    refine Stable.of_nn (hps'.2.1 n hn) fun ⟨v', hv'⟩ => ?_
    have ev := agree hnω hp hp' hn₁ hn₂ hps hps' hv hv'
    exact Sat.resp step (Env.cons_resp ev.symm fun _ => Equiv.refl _) (hps'.2.2.2.2 n v' w hv' hw)

end SynZF

/-- info: 'PSet.SynZF.seq_exists' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.seq_exists
/-- info: 'PSet.SynZF.seq_spec' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.seq_spec
/-- info: 'PSet.SynZF.seq_unique' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.seq_unique

end PSet
