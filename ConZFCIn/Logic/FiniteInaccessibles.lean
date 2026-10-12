import ConZFCIn.Definitions

/-!
Semantics of the first-order sentence asserting at least `n` strictly increasing strongly
inaccessible cardinals, and the model interface used to prove its consistency.

Satisfaction is characterized exactly using the upstream formula `inaccF`. A separate
implication converts semantic `InaccIn` witnesses into these formula witnesses. The final
consistency proofs expand the universe levels for each externally fixed `n`.
-/
universe u

namespace ConZFCIn
open PSet PSet.Fml PSet.CardF

theorem atLeastInaccF_zero : atLeastInaccF 0 = imp fls fls := rfl
theorem atLeastInaccF_one : atLeastInaccF 1 = exInacc := rfl

private theorem bound_and {k : Nat} {p q : Fml} (hp : Bound k p) (hq : Bound k q) :
    Bound k (and p q) := ⟨⟨hp, hq, trivial⟩, trivial⟩

private theorem bound_ex {k : Nat} {p : Fml} (hp : Bound (k+1) p) :
    Bound k (ex p) := ⟨⟨hp, trivial⟩, trivial⟩

private theorem bound_true {k : Nat} : Bound k trueF := ⟨trivial, trivial⟩

/-- Decide variable bounds by structural recursion on the formula syntax. -/
private def boundDecidable (k : Nat) : (p : Fml) → Decidable (Bound k p)
  | mem i j => (inferInstance : Decidable (i < k ∧ j < k))
  | eq i j => (inferInstance : Decidable (i < k ∧ j < k))
  | fls => (inferInstance : Decidable True)
  | imp p q =>
    letI := boundDecidable k p
    letI := boundDecidable k q
    (inferInstance : Decidable (Bound k p ∧ Bound k q))
  | all p => boundDecidable (k+1) p

theorem bound_inacc_zero : Bound 1 (inaccF 0) :=
  @of_decide_eq_true _ (boundDecidable 1 (inaccF 0)) rfl

theorem bound_aboveInaccF : ∀ (n k : Nat), Bound (k+1) (aboveInaccF n k)
  | 0, _ => bound_true
  | n+1, _k =>
    bound_ex (bound_and (bound_inacc_zero.mono (Nat.succ_le_succ (Nat.zero_le _)))
      (bound_and ⟨Nat.lt_succ_self _, Nat.zero_lt_succ _⟩
        ((bound_aboveInaccF n 0).mono (Nat.succ_le_succ (Nat.zero_le _)))))

/-- The target formula is closed for every `n`. -/
theorem bound_atLeastInaccF : ∀ n, Bound 0 (atLeastInaccF n)
  | 0 => bound_true
  | 1 => bound_ex bound_inacc_zero
  | n+2 => bound_ex (bound_and bound_inacc_zero (bound_aboveInaccF (n+1) 0))

theorem ZFCIn_one_iff (p : Fml) : ZFCIn 1 p ↔ ZFCI p := by
  constructor
  · intro h
    cases h with
    | zf hz => exact .zf hz
    | ac => exact .ac
    | inacc => exact .inacc
  · intro h
    cases h with
    | zf hz => exact .zf hz
    | ac => exact .ac
    | inacc => exact .inacc

private theorem prf_translate {S T : Fml → Prop} (hax : ∀ p, S p → Prf T p)
    {p : Fml} (hp : Prf S p) : Prf T p := by
  induction hp with
  | ax h => exact hax _ h
  | k => exact .k
  | s => exact .s
  | dne => exact .dne
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  | gen _ ih => exact .gen ih
  | inst j => exact .inst j
  | dist => exact .dist
  | refl i => exact .refl i
  | eq_mem_l i j k => exact .eq_mem_l i j k
  | eq_mem_r i j k => exact .eq_mem_r i j k
  | eq_eq i j k => exact .eq_eq i j k

/-- The one-inaccessible consistency statement is equivalent to the upstream `Con ZFCI`. -/
theorem con_ZFCIn_one_iff : Con (ZFCIn 1) ↔ Con ZFCI :=
  ⟨fun h hp => h (prf_translate (fun p hz => .ax ((ZFCIn_one_iff p).2 hz)) hp),
   fun h hp => h (prf_translate (fun p hz => .ax ((ZFCIn_one_iff p).1 hz)) hp)⟩

private theorem prf_true {T : Fml → Prop} : Prf T trueF := by
  have hk₁ : Prf T (imp fls (imp (imp fls fls) fls)) := .k
  have hk₂ : Prf T (imp fls (imp fls fls)) := .k
  exact .mp (.mp .s hk₁) hk₂

/-- At `n = 0`, the additional axiom is a provable truth, so consistency is equivalent
to consistency of ZFC. -/
theorem con_ZFCIn_zero_iff : Con (ZFCIn 0) ↔ Con ZFC := by
  constructor
  · intro h hp
    apply h (prf_translate (fun p hz => ?_) hp)
    cases hz with
    | inl hz => exact .ax (.zf hz)
    | inr he => cases he; exact .ax .ac
  · intro h hp
    apply h (prf_translate (fun p hz => ?_) hp)
    cases hz with
    | zf hz => exact .ax (.inl hz)
    | ac => exact .ax (.inr rfl)
    | inacc => exact prf_true

/-- The exact satisfaction predicate for `inaccF`. Its implication from `InaccIn` is
proved below using the upstream semantic bridge. -/
def SyntaxInacc (N : PSet.{u} → Prop) (x : PSet.{u}) : Prop :=
  Sat N (inaccF 0) (fun _ => x)

private theorem sat_inacc_zero {N : PSet.{u} → Prop} (e : Nat → PSet.{u}) :
    Sat N (inaccF 0) e ↔ SyntaxInacc N (e 0) :=
  sat_bound bound_inacc_zero fun i hi => by
    cases i with
    | zero => exact Equiv.refl _
    | succ i => exact (Nat.not_lt_zero i (Nat.lt_of_succ_lt_succ hi)).elim

/-- A positively existential finite chain of formula witnesses, each strictly above
the preceding lower bound in the membership order. -/
def SyntaxChainAbove (N : PSet.{u} → Prop) : Nat → PSet.{u} → Prop
  | 0, _ => True
  | n+1, lower => ∃ upper, N upper ∧ SyntaxInacc N upper ∧ lower ∈ upper ∧
      SyntaxChainAbove N n upper

def SyntaxChain (N : PSet.{u} → Prop) : Nat → Prop
  | 0 => True
  | n+1 => ∃ x, N x ∧ SyntaxInacc N x ∧ SyntaxChainAbove N n x

/-- Satisfaction is equivalent to double-negated existence of the finite witness chain. -/
theorem sat_aboveInaccF {N : PSet.{u} → Prop} : ∀ (n k : Nat) (e : Nat → PSet.{u}),
    Sat N (aboveInaccF n k) e ↔ ¬¬SyntaxChainAbove N n (e k)
  | 0, _, _ => ⟨fun _ => nn_intro trivial, fun _ => id⟩
  | n+1, k, e => by
    constructor
    · intro h
      refine nn_bind (sat_ex.1 h) fun ⟨x, hx, hs⟩ => ?_
      have ⟨hi, ht⟩ := sat_and.1 hs
      have ⟨hl, hc⟩ := sat_and.1 ht
      have hi' := (sat_inacc_zero (N := N) (Env.cons x e)).1 hi
      have hc' := (sat_aboveInaccF n 0 (Env.cons x e)).1 hc
      exact nn_map (fun hc'' => ⟨x, hx, hi', hl, hc''⟩) hc'
    · intro h
      refine sat_ex.2 (nn_map (fun ⟨x, hx, hi, hl, hc⟩ => ?_) h)
      exact ⟨x, hx, sat_and.2 ⟨(sat_inacc_zero (N := N) (Env.cons x e)).2 hi,
        sat_and.2 ⟨hl, (sat_aboveInaccF n 0 (Env.cons x e)).2 (nn_intro hc)⟩⟩⟩

theorem sat_atLeastInaccF {N : PSet.{u} → Prop} : ∀ (n : Nat) (e : Nat → PSet.{u}),
    Sat N (atLeastInaccF n) e ↔ ¬¬SyntaxChain N n
  | 0, _ => ⟨fun _ => nn_intro trivial, fun _ => id⟩
  | 1, e => by
    constructor
    · intro h
      exact nn_map (fun ⟨x, hx, hi⟩ =>
        ⟨x, hx, (sat_inacc_zero (N := N) (Env.cons x e)).1 hi, trivial⟩) (sat_ex.1 h)
    · intro h
      exact sat_ex.2 (nn_map (fun ⟨x, hx, hi, _⟩ =>
        ⟨x, hx, (sat_inacc_zero (N := N) (Env.cons x e)).2 hi⟩) h)
  | n+2, e => by
    constructor
    · intro h
      refine nn_bind (sat_ex.1 h) fun ⟨x, hx, hs⟩ => ?_
      have ⟨hi, hc⟩ := sat_and.1 hs
      have hi' := (sat_inacc_zero (N := N) (Env.cons x e)).1 hi
      exact nn_map (fun hc' => ⟨x, hx, hi', hc'⟩)
        ((sat_aboveInaccF (n+1) 0 (Env.cons x e)).1 hc)
    · intro h
      refine sat_ex.2 (nn_map (fun ⟨x, hx, hi, hc⟩ => ?_) h)
      exact ⟨x, hx, sat_and.2 ⟨(sat_inacc_zero (N := N) (Env.cons x e)).2 hi,
        (sat_aboveInaccF (n+1) 0 (Env.cons x e)).2 (nn_intro hc)⟩⟩

/-- Excluded middle turns the double-negated chain in the satisfaction characterization
into a positively existential chain. -/
theorem sat_atLeastInaccF_of_em {N : PSet.{u} → Prop}
    (em : ∀ p : Prop, p ∨ ¬p) (n : Nat) (e : Nat → PSet.{u}) :
    Sat N (atLeastInaccF n) e ↔ SyntaxChain N n := by
  constructor
  · intro h
    cases em (SyntaxChain N n) with
    | inl hc => exact hc
    | inr hc => exact ((sat_atLeastInaccF n e).1 h hc).elim
  · intro h
    exact (sat_atLeastInaccF n e).2 (nn_intro h)

/-- The chain of semantic inaccessibility witnesses supplied by the model construction. -/
def InaccChainAbove (N : PSet.{u} → Prop) : Nat → PSet.{u} → Prop
  | 0, _ => True
  | n+1, lower => ∃ upper, N upper ∧ InaccIn N upper ∧ lower ∈ upper ∧
      InaccChainAbove N n upper

def InaccChain (N : PSet.{u} → Prop) : Nat → Prop
  | 0 => True
  | n+1 => ∃ x, N x ∧ InaccIn N x ∧ InaccChainAbove N n x

theorem syntaxInacc_of_inaccIn {N : PSet.{u} → Prop} (hN : TransClass N)
    {x : PSet.{u}} (hx : N x) (hi : InaccIn N x) : SyntaxInacc N x :=
  hN.sat_inaccF_of_inaccIn (fun _ => hx) 0 hi

theorem syntaxChainAbove_of_inaccChainAbove {N : PSet.{u} → Prop} (hN : TransClass N) :
    ∀ {n : Nat} {x : PSet.{u}}, InaccChainAbove N n x → SyntaxChainAbove N n x
  | 0, _, _ => trivial
  | _n+1, _, ⟨y, hy, hi, hl, ht⟩ =>
    ⟨y, hy, syntaxInacc_of_inaccIn hN hy hi, hl, syntaxChainAbove_of_inaccChainAbove hN ht⟩

theorem syntaxChain_of_inaccChain {N : PSet.{u} → Prop} (hN : TransClass N) :
    ∀ {n : Nat}, InaccChain N n → SyntaxChain N n
  | 0, _ => trivial
  | _n+1, ⟨x, hx, hi, ht⟩ =>
    ⟨x, hx, syntaxInacc_of_inaccIn hN hx hi, syntaxChainAbove_of_inaccChainAbove hN ht⟩

theorem valid_atLeastInaccF_of_chain {N : PSet.{u} → Prop} (hN : TransClass N)
    {n : Nat} (hc : InaccChain N n) : Valid N (atLeastInaccF n) :=
  fun e _ => (sat_atLeastInaccF n e).2 (nn_intro (syntaxChain_of_inaccChain hN hc))

/-- Consistency from an explicitly supplied nonempty model of ZF and choice containing
the inaccessible chain. The final proofs construct this model and all the witnesses. -/
theorem con_ZFCIn_of_model {N : PSet.{u} → Prop} (hN : TransClass N)
    (hZF : ∀ p, ZF p → Valid N p) (hac : Valid N PSet.ac)
    {n : Nat} (hc : InaccChain N n) (hne : ∃ x, N x) : Con (ZFCIn n) := by
  obtain ⟨x, hx⟩ := hne
  refine Con.of_model (fun p hp => ?_) x hx
  cases hp with
  | zf hz => exact hZF _ hz
  | ac => exact hac
  | inacc => exact valid_atLeastInaccF_of_chain hN hc

/-- Membership separates witnesses up to bisimulation. Ordinal transitivity extends
this separation to every pair of entries in a chain. -/
theorem not_equiv_of_mem {x y : PSet.{u}} (h : x ∈ y) : ¬ x ≈ y :=
  fun he => not_mem_self y ((mem_congr_left he).1 h)

/-- Every entry belongs to `N` and satisfies `inaccF`; each precedes every later entry
in the membership order. -/
def StrictInaccList (N : PSet.{u} → Prop) : List PSet.{u} → Prop
  | [] => True
  | x::xs => N x ∧ SyntaxInacc N x ∧ (∀ y, y ∈ xs → x ∈ y) ∧ StrictInaccList N xs

def DistinctSetoidList : List PSet.{u} → Prop
  | [] => True
  | x::xs => (∀ y, y ∈ xs → ¬ x ≈ y) ∧ DistinctSetoidList xs

theorem strictInaccList_distinct {N : PSet.{u} → Prop} :
    ∀ {xs : List PSet.{u}}, StrictInaccList N xs → DistinctSetoidList xs
  | [], _ => trivial
  | _::_, ⟨_, _, hlt, ht⟩ =>
    ⟨fun y hy => not_equiv_of_mem (hlt y hy), strictInaccList_distinct ht⟩

private theorem strictInaccList_mem {N : PSet.{u} → Prop} :
    ∀ {xs : List PSet.{u}} {x : PSet.{u}}, StrictInaccList N xs → x ∈ xs →
      N x ∧ SyntaxInacc N x
  | [], _, _, hm => nomatch hm
  | _::_, _, ⟨hx, hi, _, ht⟩, hm => by
    cases hm with
    | head => exact ⟨hx, hi⟩
    | tail _ hm => exact strictInaccList_mem ht hm

private theorem syntaxInacc_isOrd {N : PSet.{u} → Prop} (hN : TransClass N)
    {x : PSet.{u}} (hx : N x) (hi : SyntaxInacc N x) : IsOrd x :=
  (hN.sat_ordF (fun _ => hx) 0).1 (sat_and.1 hi).1

private theorem syntaxChainAbove_list {N : PSet.{u} → Prop} (hN : TransClass N) :
    ∀ {n : Nat} {x : PSet.{u}}, SyntaxChainAbove N n x →
      ∃ xs : List PSet.{u}, xs.length = n ∧ StrictInaccList N xs ∧
        ∀ y, y ∈ xs → x ∈ y
  | 0, _, _ => ⟨[], rfl, trivial, fun _ h => nomatch h⟩
  | n+1, x, ⟨y, hy, hi, hxy, ht⟩ => by
    obtain ⟨xs, hlen, hs, hys⟩ := syntaxChainAbove_list hN ht
    refine ⟨y::xs, congrArg Nat.succ hlen, ⟨hy, hi, hys, hs⟩, ?_⟩
    intro z hz
    cases hz with
    | head => exact hxy
    | tail _ hz =>
      have ⟨hzN, hzI⟩ := strictInaccList_mem hs hz
      exact (syntaxInacc_isOrd hN hzN hzI).trans y (hys z hz) x hxy

private theorem strictInaccList_above {N : PSet.{u} → Prop} :
    ∀ {xs : List PSet.{u}} {x : PSet.{u}}, StrictInaccList N xs →
      (∀ y, y ∈ xs → x ∈ y) → SyntaxChainAbove N xs.length x
  | [], _, _, _ => trivial
  | y::_ys, _x, ⟨hy, hi, hys, hs⟩, hxy =>
    ⟨y, hy, hi, hxy y (.head _), strictInaccList_above hs hys⟩

/-- A chain is equivalent to a strictly increasing list of length `n`. Its entries are
therefore pairwise inequivalent under bisimulation. -/
theorem syntaxChain_list_iff {N : PSet.{u} → Prop} (hN : TransClass N) (n : Nat) :
    SyntaxChain N n ↔ ∃ xs : List PSet.{u}, xs.length = n ∧ StrictInaccList N xs := by
  constructor
  · intro h
    cases n with
    | zero => exact ⟨[], rfl, trivial⟩
    | succ n =>
      obtain ⟨x, hx, hi, ht⟩ := h
      obtain ⟨xs, hlen, hs, hxs⟩ := syntaxChainAbove_list hN ht
      exact ⟨x::xs, congrArg Nat.succ hlen, hx, hi, hxs, hs⟩
  · intro ⟨xs, hlen, hs⟩
    cases xs with
    | nil => cases hlen; exact trivial
    | cons x xs =>
      cases hlen
      have ⟨hx, hi, hxs, ht⟩ := hs
      exact ⟨x, hx, hi, strictInaccList_above ht hxs⟩

theorem sat_atLeastInaccF_list {N : PSet.{u} → Prop} (hN : TransClass N)
    (n : Nat) (e : Nat → PSet.{u}) :
    Sat N (atLeastInaccF n) e ↔
      ¬¬∃ xs : List PSet.{u}, xs.length = n ∧ StrictInaccList N xs :=
  (sat_atLeastInaccF n e).trans (nn_congr (syntaxChain_list_iff hN n))

end ConZFCIn

#print axioms ConZFCIn.bound_atLeastInaccF
#print axioms ConZFCIn.sat_atLeastInaccF
#print axioms ConZFCIn.sat_atLeastInaccF_of_em
#print axioms ConZFCIn.ZFCIn_one_iff
#print axioms ConZFCIn.con_ZFCIn_zero_iff
#print axioms ConZFCIn.con_ZFCIn_one_iff
#print axioms ConZFCIn.valid_atLeastInaccF_of_chain
#print axioms ConZFCIn.con_ZFCIn_of_model
#print axioms ConZFCIn.sat_atLeastInaccF_list
#print axioms ConZFCIn.strictInaccList_distinct
