import Vendor.ConZF.UpperN
/-!
Finite ordinal words and the shortlex minimum principle (conzf20, con32 §1). An ordinal word is
a pure finite function from a numeral into ordinals (`IsOWord`, formula `owordF`); words are
compared by length, then lexicographically at the first differing position (`WLt`, formula
`wltF`). The order is linear up to bisimulation (`oword_trichotomy`) and, although not
set-like, every inhabited stable class of words has a least member (`minWord`): minimize the
successful length below a supplied witness, then extend a prefix coordinate by coordinate with
the least ordinal still permitting success, each minimization bounded by an already supplied
candidate. The minimum is unique up to bisimulation (`minWord_unique`). Only finitely many
coordinates are ever chosen; no class of all words is collected.
-/
universe u

namespace PSet
open Fml CardF LF AssignF

/-! ### Words -/

/-- An ordinal word of length `n`: `n ∈ ω`, a pure function on `n`, with ordinal values. -/
def IsOWord (c n : PSet.{u}) : Prop := n ∈ omega ∧ IsMap c n ∧ ∀ i v, pair i v ∈ c → IsOrd v

instance {c n : PSet.{u}} : Stable (IsOWord c n) := inferInstanceAs (Stable (_ ∧ _ ∧ _))

theorem IsMap.dom_unique {c n n' : PSet.{u}} (h : IsMap c n) (h' : IsMap c n') : n ≈ n' :=
  ext fun i => ⟨fun hi => Stable.of_nn (h.2.1 i hi) fun ⟨_, hv⟩ => Stable.of_nn (h'.1 _ hv)
      fun ⟨_, _, hi', e'⟩ => (mem_congr_left (pair_inj e').1).2 hi',
    fun hi => Stable.of_nn (h'.2.1 i hi) fun ⟨_, hv⟩ => Stable.of_nn (h.1 _ hv)
      fun ⟨_, _, hi', e'⟩ => (mem_congr_left (pair_inj e').1).2 hi'⟩

theorem IsMap.congr {c c' n : PSet.{u}} (e : c ≈ c') (h : IsMap c n) : IsMap c' n :=
  ⟨fun q hq => h.1 q ((mem_congr_right e).2 hq), fun i hi => nn_map (fun ⟨v, hv⟩ => ⟨v, (mem_congr_right e).1 hv⟩) (h.2.1 i hi),
   fun i v v' h1 h2 => h.2.2 i v v' ((mem_congr_right e).2 h1) ((mem_congr_right e).2 h2)⟩

theorem IsOWord.congr {c c' n : PSet.{u}} (e : c ≈ c') (h : IsOWord c n) : IsOWord c' n :=
  ⟨h.1, h.2.1.congr e, fun i v hv => h.2.2 i v ((mem_congr_right e).2 hv)⟩

theorem IsOWord.congr_len {c n n' : PSet.{u}} (e : n ≈ n') (h : IsOWord c n) : IsOWord c n' :=
  ⟨(mem_congr_left e).1 h.1, ⟨fun q hq => nn_map (fun ⟨i, v, hi, e'⟩ => ⟨i, v, (mem_congr_right e).1 hi, e'⟩) (h.2.1.1 q hq),
    fun i hi => h.2.1.2.1 i ((mem_congr_right e).2 hi), h.2.1.2.2⟩, h.2.2⟩

/-- Two pure functions on the same domain with the same values are equal. -/
theorem IsMap.ext {c d n : PSet.{u}} (hc : IsMap c n) (hd : IsMap d n)
    (h : ∀ i v w, pair i v ∈ c → pair i w ∈ d → v ≈ w) : c ≈ d := by
  refine PSet.ext fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · refine Stable.of_nn (hc.1 q hq) fun ⟨i, v, hi, e⟩ => Stable.of_nn (hd.2.1 i hi) fun ⟨w, hw⟩ => ?_
    exact (mem_congr_left (e.trans (pair_congr (Equiv.refl _) (h i v w ((mem_congr_left e).1 hq) hw)))).2 hw
  · refine Stable.of_nn (hd.1 q hq) fun ⟨i, w, hi, e⟩ => Stable.of_nn (hc.2.1 i hi) fun ⟨v, hv⟩ => ?_
    exact (mem_congr_left (e.trans (pair_congr (Equiv.refl _) (h i v w hv ((mem_congr_left e).1 hq)).symm))).2 hv

/-- The values of a pure function on the first `k` numerals, read as a native environment. -/
theorem exists_reads {d n : PSet.{u}} (h : IsMap d n) :
    ∀ k : Nat, (∀ j, j < k → ofNat j ∈ n) → ¬¬∃ e : Nat → PSet.{u}, ∀ j, j < k → Reads d j (e j)
  | 0, _ => nn_intro ⟨fun _ => empty, fun j hj => (Nat.not_lt_zero j hj).elim⟩
  | k+1, hk => by
    refine nn_bind (exists_reads h k fun j hj => hk j (Nat.lt_succ_of_lt hj)) fun ⟨e, he⟩ =>
      nn_map (fun ⟨v, hv⟩ => ⟨fun j => if j < k then e j else v, fun j hj => ?_⟩) (h.2.1 _ (hk k (Nat.lt_succ_self k)))
    show Reads d j (if j < k then e j else v)
    split
    · exact he j ‹_›
    · cases Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.le_of_not_lt ‹_›)
      exact hv

/-! ### Shortlex -/

/-- `c` and `d` agree at every position in `i`. -/
def Agree (c d i : PSet.{u}) : Prop := ∀ j, j ∈ i → ∀ v w, pair j v ∈ c → pair j w ∈ d → v ≈ w

/-- **Shortlex**: shorter, or equal length and smaller at the first differing position. -/
def WLt (c n d m : PSet.{u}) : Prop :=
  ¬¬(n ∈ m ∨ (n ≈ m ∧ ¬¬∃ i, i ∈ n ∧ Agree c d i ∧ ¬¬∃ v w, pair i v ∈ c ∧ pair i w ∈ d ∧ v ∈ w))

instance {c n d m : PSet.{u}} : Stable (WLt c n d m) := inferInstanceAs (Stable (¬_))

theorem Agree.symm {c d i : PSet.{u}} (h : Agree c d i) : Agree d c i :=
  fun j hj v w hv hw => (h j hj w v hw hv).symm

theorem Agree.congr {c c' d d' i i' : PSet.{u}} (ec : c ≈ c') (ed : d ≈ d') (ei : i ≈ i') (h : Agree c d i) : Agree c' d' i' :=
  fun j hj v w hv hw => h j ((mem_congr_right ei).2 hj) v w ((mem_congr_right ec).2 hv) ((mem_congr_right ed).2 hw)

theorem WLt.congr {c c' n n' d d' m m' : PSet.{u}} (ec : c ≈ c') (en : n ≈ n') (ed : d ≈ d') (em : m ≈ m')
    (h : WLt c n d m) : WLt c' n' d' m' :=
  nn_map (fun h => h.imp (fun h => (mem_congr_left en).1 ((mem_congr_right em).1 h)) fun ⟨e, k0⟩ =>
    ⟨en.symm.trans (e.trans em), nn_map (fun ⟨i, hi, ha, k⟩ => ⟨i, (mem_congr_right en).1 hi, ha.congr ec ed (Equiv.refl _),
      nn_map (fun ⟨v, w, hv, hw, hvw⟩ => ⟨v, w, (mem_congr_right ec).1 hv, (mem_congr_right ed).1 hw, hvw⟩) k⟩) k0⟩) h

theorem IsOWord.isOrd_len {c n : PSet.{u}} (h : IsOWord c n) : IsOrd n := isOrd_omega.mem h.1

/-- **Linearity** of shortlex on ordinal words, up to bisimulation. -/
theorem oword_trichotomy {c n d m : PSet.{u}} (hc : IsOWord c n) (hd : IsOWord d m) :
    ¬¬(WLt c n d m ∨ c ≈ d ∨ WLt d m c n) := by
  intro hk
  refine Stable.of_nn (hc.isOrd_len.trichotomy hd.isOrd_len) fun
    | .inl h => hk (.inl (nn_intro (.inl h)))
    | .inr (.inr h) => hk (.inr (.inr (nn_intro (.inl h))))
    | .inr (.inl e) => ?_
  refine Stable.of_nn (mem_omega.1 hc.1) fun ⟨K, eK⟩ => ?_
  have hd' : IsOWord d n := hd.congr_len e.symm
  -- first difference below `k`
  have claim : ∀ k, k ≤ K → ¬¬((∀ j, j ∈ ofNat k → ∀ v w, pair j v ∈ c → pair j w ∈ d → v ≈ w) ∨
      ∃ i, i ∈ ofNat k ∧ Agree c d i ∧ ¬¬∃ v w, pair i v ∈ c ∧ pair i w ∈ d ∧ (v ∈ w ∨ w ∈ v)) := by
    intro k
    induction k with
    | zero => exact fun _ => nn_intro (.inl fun j hj => (not_mem_empty j hj).elim)
    | succ k ih =>
      intro hk
      refine nn_bind (ih (Nat.le_of_succ_le hk)) fun
        | .inr ⟨i, hi, ha, k'⟩ => nn_intro (.inr ⟨i, mem_succ_of_mem hi, ha, k'⟩)
        | .inl hag => ?_
      have hkn : ofNat k ∈ n := (mem_congr_right eK).2 (mem_ofNat.2 (nn_intro ⟨k, hk, Equiv.refl _⟩))
      refine nn_bind (hc.2.1.2.1 _ hkn) fun ⟨v, hv⟩ => nn_bind (hd'.2.1.2.1 _ hkn) fun ⟨w, hw⟩ => ?_
      refine nn_map (fun h => ?_) ((hc.2.2 _ v hv).trichotomy (hd.2.2 _ w hw))
      rcases h with h | h | h
      · exact .inr ⟨ofNat k, self_mem_succ _, hag, nn_intro ⟨v, w, hv, hw, .inl h⟩⟩
      · refine .inl fun j hj v' w' hv' hw' => ?_
        refine Stable.of_nn (mem_succ.1 hj) fun
          | .inl hj => hag j hj v' w' hv' hw'
          | .inr ej => ?_
        have ev := hc.2.1.2.2 _ v' v ((mem_congr_left (pair_congr ej (Equiv.refl _))).1 hv') hv
        have ew := hd.2.1.2.2 _ w' w ((mem_congr_left (pair_congr ej (Equiv.refl _))).1 hw') hw
        exact ev.trans (h.trans ew.symm)
      · exact .inr ⟨ofNat k, self_mem_succ _, hag, nn_intro ⟨v, w, hv, hw, .inr h⟩⟩
  refine Stable.of_nn (claim K (Nat.le_refl K)) fun h => ?_
  rcases h with hag | ⟨i, hi, ha, k⟩
  · exact hk (.inr (.inl (hc.2.1.ext hd'.2.1 fun j v w hv hw => hag j ((mem_congr_right eK).1
      (Stable.of_nn (hc.2.1.1 _ hv) fun ⟨_, _, hj, e'⟩ => (mem_congr_left (pair_inj e').1).2 hj)) v w hv hw)))
  · have hin : i ∈ n := (mem_congr_right eK).2 hi
    refine Stable.of_nn k fun ⟨v, w, hv, hw, h⟩ => ?_
    rcases h with h | h
    · exact hk (.inl (nn_intro (.inr ⟨e, nn_intro ⟨i, hin, ha, nn_intro ⟨v, w, hv, hw, h⟩⟩⟩)))
    · exact hk (.inr (.inr (nn_intro (.inr ⟨e.symm, nn_intro ⟨i, (mem_congr_right e).1 hin, ha.symm, nn_intro ⟨w, v, hw, hv, h⟩⟩⟩))))

/-! ### The minimum principle -/

theorem Reads.congr {c : PSet.{u}} {j : Nat} {v v' : PSet.{u}} (e : v ≈ v') (h : Reads c j v) : Reads c j v' :=
  (mem_congr_left (pair_congr (Equiv.refl _) e)).1 h

/-- **The shortlex minimum principle**: an inhabited stable class of ordinal words of the class
has a least member. -/
theorem minWord {N : PSet.{u} → Prop} (χ : PSet.{u} → PSet.{u} → Prop) [∀ c n, Stable (χ c n)]
    (hχ : ∀ {c c' n n'}, c ≈ c' → n ≈ n' → χ c n → χ c' n')
    (h : ¬¬∃ c n, N c ∧ IsOWord c n ∧ χ c n) :
    ¬¬∃ c n, N c ∧ IsOWord c n ∧ χ c n ∧ ∀ d m, N d → IsOWord d m → WLt d m c n → ¬ χ d m := by
  refine Stable.of_nn h fun ⟨c₀, n₀, hc₀, ho₀, hχ₀⟩ => ?_
  -- the least successful length
  let S := PSet.sep (fun n => ¬¬∃ c, N c ∧ IsOWord c n ∧ χ c n) (succ n₀)
  have hS : ∀ n, n ∈ S ↔ n ∈ succ n₀ ∧ ¬¬∃ c, N c ∧ IsOWord c n ∧ χ c n := fun n =>
    mem_sep fun _ _ e k => nn_map (fun ⟨c, hc, ho, hχ'⟩ => ⟨c, hc, ho.congr_len e, hχ (Equiv.refl _) e hχ'⟩) k
  have hn₀S : n₀ ∈ S := (hS n₀).2 ⟨self_mem_succ n₀, nn_intro ⟨c₀, hc₀, ho₀, hχ₀⟩⟩
  refine Stable.of_nn (exists_minimal S n₀ hn₀S) fun ⟨n₁, hn₁S, hmin⟩ => ?_
  have ⟨hn₁s, hn₁⟩ := (hS n₁).1 hn₁S
  have hsucc : IsOrd (succ n₀) := ho₀.isOrd_len.succ
  have hn₁ω : n₁ ∈ omega := Stable.of_nn (mem_succ.1 hn₁s) fun
    | .inl h => isOrd_omega.trans _ ho₀.1 _ h
    | .inr e => (mem_congr_left e).2 ho₀.1
  have hlen : ∀ m, (¬¬∃ d, N d ∧ IsOWord d m ∧ χ d m) → ¬ m ∈ n₁ := fun m k hm =>
    hmin m hm ((hS m).2 ⟨hsucc.trans n₁ hn₁s m hm, k⟩)
  refine Stable.of_nn (mem_omega.1 hn₁ω) fun ⟨K, eK⟩ => ?_
  -- prefixes
  let Ext : (Nat → PSet.{u}) → Nat → Prop := fun p i =>
    ¬¬∃ c, N c ∧ IsOWord c n₁ ∧ χ c n₁ ∧ ∀ j, j < i → Reads c j (p j)
  have Ext_congr : ∀ {p p' : Nat → PSet.{u}} {i : Nat}, (∀ j, j < i → p j ≈ p' j) → Ext p i → Ext p' i :=
    fun hpp h => nn_map (fun ⟨c, hc, ho, hχ', hr⟩ => ⟨c, hc, ho, hχ', fun j hj => (hr j hj).congr (hpp j hj)⟩) h
  have Ext_mono : ∀ {p : Nat → PSet.{u}} {i i' : Nat}, i' ≤ i → Ext p i → Ext p i' :=
    fun hii h => nn_map (fun ⟨c, hc, ho, hχ', hr⟩ => ⟨c, hc, ho, hχ', fun j hj => hr j (Nat.lt_of_lt_of_le hj hii)⟩) h
  let LexLt : (Nat → PSet.{u}) → (Nat → PSet.{u}) → Nat → Prop := fun p' p i =>
    ∃ j, j < i ∧ (∀ k, k < j → p' k ≈ p k) ∧ p' j ∈ p j
  have hpos : ∀ i, i < K → ofNat i ∈ n₁ := fun i hi => (mem_congr_right eK).2 (mem_ofNat.2 (nn_intro ⟨i, hi, Equiv.refl _⟩))
  have inv : ∀ i, i ≤ K → ¬¬∃ p : Nat → PSet.{u}, Ext p i ∧ ∀ p', Ext p' i → ¬ LexLt p' p i := by
    intro i
    induction i with
    | zero =>
      intro _
      refine nn_intro ⟨fun _ => empty, nn_map (fun ⟨c, hc, ho, hχ'⟩ => ⟨c, hc, ho, hχ', fun j hj => (Nat.not_lt_zero j hj).elim⟩) hn₁,
        fun _ _ ⟨j, hj, _⟩ => (Nat.not_lt_zero j hj).elim⟩
    | succ i ih =>
      intro hi
      refine nn_bind (ih (Nat.le_of_succ_le hi)) fun ⟨p, hp, hpmin⟩ => Stable.of_nn hp fun ⟨c, hc, ho, hχ', hr⟩ => ?_
      refine Stable.of_nn (ho.2.1.2.1 _ (hpos i hi)) fun ⟨η, hη⟩ => ?_
      have hηo : IsOrd η := ho.2.2 _ η hη
      let upd : PSet.{u} → Nat → PSet.{u} := fun ξ j => if j < i then p j else ξ
      have upd_lt : ∀ ξ j, j < i → upd ξ j = p j := fun ξ j hj => by
        show (if j < i then p j else ξ) = p j
        split
        · rfl
        · exact absurd hj ‹_›
      have upd_eq : ∀ ξ, upd ξ i = ξ := fun ξ => by
        show (if i < i then p i else ξ) = ξ
        split
        · exact absurd ‹i < i› (Nat.lt_irrefl i)
        · rfl
      let T := PSet.sep (fun ξ => Ext (upd ξ) (i+1)) (succ η)
      have hT : ∀ ξ, ξ ∈ T ↔ ξ ∈ succ η ∧ Ext (upd ξ) (i+1) := fun ξ =>
        mem_sep fun ξ ξ' e k => Ext_congr (fun j hj => by
          rcases Nat.lt_or_ge j i with h' | h'
          · rw [upd_lt ξ j h', upd_lt ξ' j h']; exact Equiv.refl _
          · cases Nat.le_antisymm (Nat.le_of_lt_succ hj) h'
            rw [upd_eq, upd_eq]; exact e) k
      have hηT : η ∈ T := (hT η).2 ⟨self_mem_succ η, nn_intro ⟨c, hc, ho, hχ', fun j hj => by
        rcases Nat.lt_or_ge j i with h' | h'
        · rw [upd_lt η j h']; exact hr j h'
        · cases Nat.le_antisymm (Nat.le_of_lt_succ hj) h'
          rw [upd_eq]; exact hη⟩⟩
      refine Stable.of_nn (exists_minimal T η hηT) fun ⟨ξ, hξT, hξmin⟩ => ?_
      have ⟨hξs, hξE⟩ := (hT ξ).1 hξT
      refine nn_intro ⟨upd ξ, hξE, fun p' hp' ⟨j, hj, hag, hlt⟩ => ?_⟩
      rcases Nat.lt_or_ge j i with h' | h'
      · refine hpmin p' (Ext_mono (Nat.le_succ i) hp') ⟨j, h', fun k hk => ?_, ?_⟩
        · have := hag k hk; rwa [upd_lt ξ k (Nat.lt_trans hk h')] at this
        · rwa [upd_lt ξ j h'] at hlt
      · cases Nat.le_antisymm (Nat.le_of_lt_succ hj) h'
        rw [upd_eq] at hlt
        have hp'i : p' i ∈ succ η := hηo.succ.trans ξ hξs _ hlt
        refine hξmin (p' i) hlt ((hT _).2 ⟨hp'i, Ext_congr (fun k hk => ?_) hp'⟩)
        rcases Nat.lt_or_ge k i with h'' | h''
        · have := hag k h''
          rw [upd_lt ξ k h''] at this
          rw [upd_lt _ k h'']
          exact this
        · cases Nat.le_antisymm (Nat.le_of_lt_succ hk) h''
          rw [upd_eq]
          exact Equiv.refl _
  -- the minimal word
  refine Stable.of_nn (inv K (Nat.le_refl K)) fun ⟨p, hp, hpmin⟩ => Stable.of_nn hp fun ⟨c, hc, ho, hχ', hr⟩ => ?_
  refine nn_intro ⟨c, n₁, hc, ho, hχ', fun d m hd hdo hlt hχd => ?_⟩
  refine Stable.of_nn hlt fun
    | .inl hm => hlen m (nn_intro ⟨d, hd, hdo, hχd⟩) hm
    | .inr ⟨em, k0⟩ => Stable.of_nn k0 fun ⟨i, hi, ha, k⟩ => ?_
  have hin : i ∈ n₁ := (mem_congr_right em).1 hi
  refine Stable.of_nn (mem_ofNat.1 ((mem_congr_right eK).1 hin)) fun ⟨I, hI, eI⟩ => ?_
  have hdo' : IsOWord d n₁ := hdo.congr_len em
  refine Stable.of_nn (exists_reads hdo'.2.1 K hpos) fun ⟨p', hp'⟩ => ?_
  refine Stable.of_nn k fun ⟨v, w, hv, hw, hvw⟩ => ?_
  refine hpmin p' (nn_intro ⟨d, hd, hdo', hχ (Equiv.refl _) em hχd, hp'⟩) ⟨I, hI, fun k' hk' => ?_, ?_⟩
  · have hk'i : ofNat k' ∈ i := (mem_congr_right eI).2 (mem_ofNat.2 (nn_intro ⟨k', hk', Equiv.refl _⟩))
    exact ha _ hk'i _ _ (hp' k' (Nat.lt_trans hk' hI)) (hr k' (Nat.lt_trans hk' hI))
  · have ev := hdo.2.1.2.2 _ v (p' I) ((mem_congr_left (pair_congr eI (Equiv.refl _))).1 hv) (hp' I hI)
    have ew := ho.2.1.2.2 _ w (p I) ((mem_congr_left (pair_congr eI (Equiv.refl _))).1 hw) (hr I hI)
    exact (mem_congr_left ev).1 ((mem_congr_right ew).1 hvw)

/-- The minimum is unique up to bisimulation. -/
theorem minWord_unique {N : PSet.{u} → Prop} {χ : PSet.{u} → PSet.{u} → Prop} {c n c' n' : PSet.{u}}
    (hc : N c) (ho : IsOWord c n) (hχ : χ c n) (hmin : ∀ d m, N d → IsOWord d m → WLt d m c n → ¬ χ d m)
    (hc' : N c') (ho' : IsOWord c' n') (hχ' : χ c' n') (hmin' : ∀ d m, N d → IsOWord d m → WLt d m c' n' → ¬ χ d m) :
    c ≈ c' :=
  Stable.of_nn (oword_trichotomy ho ho') fun
    | .inl h => (hmin' c n hc ho h hχ).elim
    | .inr (.inl e) => e
    | .inr (.inr h) => (hmin c' n' hc' ho' h hχ').elim


/-! ### The formulas -/

namespace LF

/-- `c` is an ordinal word of length `n`, with `ω` at index `w`. -/
def owordF (c n w : Nat) : Fml :=
  and (mem n w) (and (mapF c n) (all (all (imp (pairMemF (c+2) 1 0) (ordF 0)))))

/-- `c` and `d` agree at every position in `i`. -/
def agreeF (c d i : Nat) : Fml :=
  all (imp (mem 0 (i+1)) (all (all (imp (pairMemF (c+3) 2 1) (imp (pairMemF (d+3) 2 0) (eq 1 0))))))

/-- Shortlex: `n ∈ m`, or `n = m` and a first differing position with the smaller value in `c`. -/
def wltF (c n d m : Nat) : Fml :=
  or (mem n m) (and (eq n m) (ex (and (mem 0 (n+1)) (and (agreeF (c+1) (d+1) 0)
    (ex (ex (and (pairMemF (c+3) 2 1) (and (pairMemF (d+3) 2 0) (mem 1 0)))))))))

end LF

namespace TransClass
variable {M : PSet.{u} → Prop} (hN : TransClass M) {E : Nat → PSet.{u}} (hE : ∀ i, M (E i))
include hN hE

theorem sat_owordF (c n w : Nat) (hw : E w ≈ omega) : Sat M (owordF c n w) E ↔ IsOWord (E c) (E n) := by
  refine sat_and.trans (and_congr (mem_congr_right hw) (sat_and.trans (and_congr (hN.sat_mapF hE c n) ⟨fun h i v hv => ?_, fun h i _ v _ hv => ?_⟩)))
  · have ⟨hi, hvM⟩ := hN.of_pair_mem (hE c) hv
    exact (hN.sat_ordF (Env.cons_mem hvM (Env.cons_mem hi hE)) 0).1 (h i hi v hvM ((hN.sat_pairMemF (Env.cons_mem hvM (Env.cons_mem hi hE)) (c+2) 1 0).2 hv))
  · exact (hN.sat_ordF (Env.cons_mem ‹M v› (Env.cons_mem ‹M i› hE)) 0).2 (h i v ((hN.sat_pairMemF (Env.cons_mem ‹M v› (Env.cons_mem ‹M i› hE)) (c+2) 1 0).1 hv))

theorem sat_agreeF (c d i : Nat) : Sat M (agreeF c d i) E ↔ Agree (E c) (E d) (E i) := by
  constructor
  · intro h j hj v w hv hw
    have hjM := hN.trans (hE i) hj
    have hvM := (hN.of_pair_mem (hE c) hv).2
    have hwM := (hN.of_pair_mem (hE d) hw).2
    have hE3 := Env.cons_mem hwM (Env.cons_mem hvM (Env.cons_mem hjM hE))
    exact h j hjM hj v hvM w hwM ((hN.sat_pairMemF hE3 (c+3) 2 1).2 hv) ((hN.sat_pairMemF hE3 (d+3) 2 0).2 hw)
  · intro h j hjM hj v hvM w hwM hv hw
    have hE3 := Env.cons_mem hwM (Env.cons_mem hvM (Env.cons_mem hjM hE))
    exact h j hj v w ((hN.sat_pairMemF hE3 (c+3) 2 1).1 hv) ((hN.sat_pairMemF hE3 (d+3) 2 0).1 hw)

theorem sat_wltF (c n d m : Nat) : Sat M (wltF c n d m) E ↔ WLt (E c) (E n) (E d) (E m) := by
  refine sat_or.trans (nn_congr (or_congr Iff.rfl (sat_and.trans (and_congr Iff.rfl (sat_ex.trans (nn_congr
    ⟨fun ⟨i, hiM, hs⟩ => ?_, fun ⟨i, hi, ha, k⟩ => ?_⟩))))))
  · have ⟨h1, h2⟩ := sat_and.1 hs
    have ⟨h3, h4⟩ := sat_and.1 h2
    have hE1 := Env.cons_mem hiM hE
    refine ⟨i, h1, (hN.sat_agreeF hE1 (c+1) (d+1) 0).1 h3, ?_⟩
    refine nn_bind (sat_ex.1 h4) fun ⟨v, hvM, hs⟩ => nn_map (fun ⟨w, hwM, hs⟩ => ?_) (sat_ex.1 hs)
    have ⟨h5, h6⟩ := sat_and.1 hs
    have ⟨h7, h8⟩ := sat_and.1 h6
    have hE3 := Env.cons_mem hwM (Env.cons_mem hvM hE1)
    exact ⟨v, w, (hN.sat_pairMemF hE3 (c+3) 2 1).1 h5, (hN.sat_pairMemF hE3 (d+3) 2 0).1 h7, h8⟩
  · have hiM := hN.trans (hE n) hi
    have hE1 := Env.cons_mem hiM hE
    refine ⟨i, hiM, sat_and.2 ⟨hi, sat_and.2 ⟨(hN.sat_agreeF hE1 (c+1) (d+1) 0).2 ha, ?_⟩⟩⟩
    refine sat_ex.2 (nn_map (fun ⟨v, w, hv, hw, hvw⟩ => ?_) k)
    have hvM := (hN.of_pair_mem (hE c) hv).2
    have hwM := (hN.of_pair_mem (hE d) hw).2
    have hE3 := Env.cons_mem hwM (Env.cons_mem hvM hE1)
    exact ⟨v, hvM, sat_ex.2 (nn_intro ⟨w, hwM, sat_and.2 ⟨(hN.sat_pairMemF hE3 (c+3) 2 1).2 hv,
      sat_and.2 ⟨(hN.sat_pairMemF hE3 (d+3) 2 0).2 hw, hvw⟩⟩⟩)⟩

end TransClass

/-- info: 'PSet.minWord' does not depend on any axioms -/
#guard_msgs in #print axioms minWord
/-- info: 'PSet.oword_trichotomy' does not depend on any axioms -/
#guard_msgs in #print axioms oword_trichotomy

end PSet
