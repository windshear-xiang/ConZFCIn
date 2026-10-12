import Vendor.ConZF.Cardinal
/-!
The internal ZF interface (conzf15 §1 and the derived set-construction rules). A class `M` is a
`SynZF` when it is stable, respects bisimulation, is transitive, contains `ω`, and validates the
syntactic `ZF` axioms. Stability is explicit: internal existence gives only double-negated
existence, and identifying an internal witness with a native set then gives `¬¬M t`, which
stability turns into `M t`.

From syntactic validity alone (no ambient closure), the class is closed under: separation by
any native formula with parameters in `M` (`sepM`), the empty set, unordered pairs, pairs,
unions, and it has internal powersets (`powM`: a member whose members in `M` are exactly the
subsets in `M`, not the ambient powerset), internal products (`prodM`: a member whose members
are exactly the pairs of members), and a collecting set for every functional native relation
(`replM`). Graph normalization (`cleanM`): the restriction of a member `f` to an internal
product is a member of `M` with the same pair-edges; it turns any junk-bearing function or
cofinal relation into a pure one in `M` (`normalizeFun`, `normalizeCof`), which is what the
transport of functions along the lift and the least-graph construction need.
-/
universe u

namespace PSet
open Fml CardF

/-- A stable transitive class containing `ω` and validating the syntactic `ZF` axioms. -/
structure SynZF (M : PSet.{u} → Prop) : Prop where
  stable : ∀ x, Stable (M x)
  resp : ∀ {x y}, x ≈ y → M x → M y
  trans : ∀ {x z}, M x → z ∈ x → M z
  omega : M omega
  valid : ∀ φ, ZF φ → Valid M φ

/-- The constant environment at `ω`. -/
def envω : Nat → PSet.{u} := fun _ => PSet.omega

namespace SynZF
variable {M : PSet.{u} → Prop} (hM : SynZF M)
include hM

theorem envω_mem : ∀ i, M (envω i) := fun _ => hM.omega

/-- **Internal separation.** The separation of `e 0` by a native formula with parameters in
`M` is in `M`. -/
theorem sepM (ψ : Fml) {e : Nat → PSet.{u}} (he : ∀ i, M (e i)) :
    M (sep (fun z => Sat M ψ (Env.cons z e)) (e 0)) := by
  let P : PSet.{u} → Prop := fun z => Sat M ψ (Env.cons z e)
  have hP : ∀ z z' : PSet.{u}, z ≈ z' → P z → P z' := fun _ _ ez h =>
    Sat.resp ψ (Env.cons_resp ez fun _ => Equiv.refl _) h
  have : ∀ z, Stable (P z) := fun z => Sat.stable ψ _
  have h := hM.valid _ (ZF.sep ψ) e he
  refine (hM.stable _).dne (nn_map (fun ⟨y, hy, hs⟩ => ?_) (sat_ex.1 h))
  have hPz : ∀ z, Sat M (rename ZFAx.sepR ψ) (Env.cons z (Env.cons y e)) ↔ P z := fun z =>
    (sat_rename ψ ZFAx.sepR _).trans
      (Sat.resp_iff (fun _ => Iff.rfl) ψ fun i => by cases i <;> exact Equiv.refl _)
  refine hM.resp (ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩) hy
  · have ⟨h1, h2⟩ := sat_and.1 ((sat_iff.1 (hs z (hM.trans hy hz))).1 hz)
    exact (mem_sep hP).2 ⟨h1, (hPz z).1 h2⟩
  · have ⟨h1, h2⟩ := (mem_sep hP).1 hz
    exact (sat_iff.1 (hs z (hM.trans (he 0) h1))).2 (sat_and.2 ⟨h1, (hPz z).2 h2⟩)

theorem empty : M empty :=
  hM.resp (ext fun z => ⟨fun hz => ((mem_sep fun _ _ _ h => h).1 hz).2.elim,
    fun hz => (not_mem_empty z hz).elim⟩) (hM.sepM fls hM.envω_mem)

theorem upair {x y : PSet.{u}} (hx : M x) (hy : M y) : M (PSet.upair x y) := by
  have h := hM.valid _ ZF.pair (Env.cons x (Env.cons y envω)) (Env.cons_mem hx (Env.cons_mem hy hM.envω_mem))
  refine (hM.stable _).dne (nn_map (fun ⟨z, hz, hs⟩ => ?_) (sat_ex.1 h))
  have ⟨hxz, hyz⟩ := sat_and.1 hs
  have he : ∀ i, M (Env.cons z (Env.cons x (Env.cons y envω)) i) :=
    Env.cons_mem hz (Env.cons_mem hx (Env.cons_mem hy hM.envω_mem))
  refine hM.resp (ext fun v => ((mem_sep fun _ _ e h => ?_).trans ?_)) (hM.sepM (or (eq 0 2) (eq 0 3)) he)
  · exact Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine ⟨fun ⟨_, h⟩ => mem_upair.2 (sat_or.1 h), fun h => ⟨?_, sat_or.2 (mem_upair.1 h)⟩⟩
  exact Stable.of_nn (mem_upair.1 h) fun
    | .inl e => (mem_congr_left e).2 hxz
    | .inr e => (mem_congr_left e).2 hyz

theorem single {x : PSet.{u}} (hx : M x) : M (singleton x) :=
  hM.resp (ext fun _ => mem_upair.trans ⟨fun h => Stable.of_nn h fun h => mem_singleton.2 (h.elim id id),
    fun h => nn_intro (.inl (mem_singleton.1 h))⟩) (hM.upair hx hx)

theorem pair {x y : PSet.{u}} (hx : M x) (hy : M y) : M (PSet.pair x y) :=
  hM.upair (hM.single hx) (hM.upair hx hy)

theorem toTransClass : TransClass M := ⟨hM.resp, hM.trans, hM.upair⟩

theorem sUnion {x : PSet.{u}} (hx : M x) : M (PSet.sUnion x) := by
  have h := hM.valid _ ZF.union (Env.cons x envω) (Env.cons_mem hx hM.envω_mem)
  refine (hM.stable _).dne (nn_map (fun ⟨u, hu, hs⟩ => ?_) (sat_ex.1 h))
  have he : ∀ i, M (Env.cons u (Env.cons x envω) i) := Env.cons_mem hu (Env.cons_mem hx hM.envω_mem)
  refine hM.resp (ext fun z => ((mem_sep fun _ _ e h => ?_).trans ?_))
    (hM.sepM (ex (and (mem 0 3) (mem 1 0))) he)
  · exact Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  constructor
  · rintro ⟨_, h⟩
    exact Stable.of_nn (sat_ex.1 h) fun ⟨y, _, hs⟩ =>
      mem_sUnion.2 (nn_intro ⟨y, (sat_and.1 hs).1, (sat_and.1 hs).2⟩)
  · intro hz
    refine ⟨Stable.of_nn (mem_sUnion.1 hz) fun ⟨y, hy, hzy⟩ => ?_, ?_⟩
    · exact hs y (hM.trans hx hy) z (hM.trans (hM.trans hx hy) hzy) hzy hy
    · exact sat_ex.2 (nn_map (fun ⟨y, hy, hzy⟩ => ⟨y, hM.trans hx hy, sat_and.2 ⟨hy, hzy⟩⟩)
        (mem_sUnion.1 hz))

theorem union {x y : PSet.{u}} (hx : M x) (hy : M y) : M (PSet.union x y) :=
  hM.resp (ext fun _ => ⟨fun h => mem_union.2 (nn_bind (mem_sUnion.1 h) fun ⟨_, hw, hzw⟩ =>
      nn_map (fun
        | .inl e => .inl ((mem_congr_right e).1 hzw)
        | .inr e => .inr ((mem_congr_right e).1 hzw)) (mem_upair.1 hw)),
    fun h => mem_sUnion.2 (nn_map (fun
        | .inl h => ⟨x, mem_upair_left _ _, h⟩
        | .inr h => ⟨y, mem_upair_right _ _, h⟩) (mem_union.1 h))⟩)
    (hM.sUnion (hM.upair hx hy))

/-- **Internal powersets.** Some member of `M` has as its members in `M` exactly the subsets
of `x` in `M`. -/
theorem powM {x : PSet.{u}} (hx : M x) :
    ¬¬∃ P, M P ∧ ∀ y, M y → (y ∈ P ↔ ∀ z, z ∈ y → z ∈ x) := by
  have h := hM.valid _ ZF.power (Env.cons x envω) (Env.cons_mem hx hM.envω_mem)
  refine nn_map (fun ⟨p, hp, hs⟩ => ?_) (sat_ex.1 h)
  have he : ∀ i, M (Env.cons p (Env.cons x envω) i) := Env.cons_mem hp (Env.cons_mem hx hM.envω_mem)
  have hP : ∀ a b : PSet.{u}, a ≈ b → Sat M (all (imp (mem 0 1) (mem 0 3))) (Env.cons a (Env.cons p (Env.cons x envω))) →
      Sat M (all (imp (mem 0 1) (mem 0 3))) (Env.cons b (Env.cons p (Env.cons x envω))) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine ⟨_, hM.sepM (all (imp (mem 0 1) (mem 0 3))) he, fun y hy => (mem_sep hP).trans ⟨fun ⟨_, h⟩ z hz => h z (hM.trans hy hz) hz, fun h => ⟨hs y hy fun z _ hz => h z hz, fun z _ hz => h z hz⟩⟩⟩

/-- **Collection.** Every relation on a member that is *defined by a native formula* with
parameters in the class, and functional there, has a collecting member. Arbitrary native
predicates are not collected: only formula-definable ones, which is the distinction the whole
internal construction rests on. -/
theorem replM (ψ : Fml) {e : Nat → PSet.{u}} (he : ∀ i, M (e i))
    (hf : ∀ x y y', x ∈ e 0 → M y → M y' → Sat M ψ (Env.cons x (Env.cons y e)) →
      Sat M ψ (Env.cons x (Env.cons y' e)) → y ≈ y') :
    ¬¬∃ b, M b ∧ ∀ x y, x ∈ e 0 → M y → Sat M ψ (Env.cons x (Env.cons y e)) → y ∈ b := by
  have h := hM.valid _ (ZF.repl ψ) e he
  have R1 : ∀ {x y y'}, Sat M (rename ZFAx.r1 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) →
      Sat M ψ (Env.cons x (Env.cons y e)) := fun h =>
    Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) ((sat_rename ψ ZFAx.r1 _).1 h)
  have R2 : ∀ {x y y'}, Sat M (rename ZFAx.r2 ψ) (Env.cons y' (Env.cons y (Env.cons x e))) →
      Sat M ψ (Env.cons x (Env.cons y' e)) := fun h =>
    Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) ((sat_rename ψ ZFAx.r2 _).1 h)
  have R3 : ∀ {x y b}, Sat M ψ (Env.cons x (Env.cons y e)) →
      Sat M (rename ZFAx.r3 ψ) (Env.cons x (Env.cons y (Env.cons b e))) := fun h =>
    (sat_rename ψ ZFAx.r3 _).2 (Sat.resp ψ (fun i => by rcases i with _ | _ | _ <;> exact Equiv.refl _) h)
  have hant : Sat M (all (imp (mem 0 1) (all (all (imp (rename ZFAx.r1 ψ)
      (imp (rename ZFAx.r2 ψ) (eq 1 0))))))) e :=
    fun x _ hx y hy y' hy' h1 h2 => hf x y y' hx hy hy' (R1 h1) (R2 h2)
  refine nn_map (fun ⟨b, hb, hs⟩ => ⟨b, hb, fun x y hx hy hxy => ?_⟩) (sat_ex.1 (h hant))
  exact hs y hy (sat_ex.2 (nn_intro ⟨x, hM.trans (he 0) hx, sat_and.2 ⟨hx, R3 hxy⟩⟩))

/-- **Internal products.** Some member of `M` has as members exactly the pairs of members of
`a` and `b`. -/
theorem prodM {a b : PSet.{u}} (ha : M a) (hb : M b) :
    ¬¬∃ p, M p ∧ ∀ q, q ∈ p ↔ ¬¬∃ x y, x ∈ a ∧ y ∈ b ∧ q ≈ PSet.pair x y := by
  have hab : M (PSet.union a b) := hM.union ha hb
  refine nn_bind (hM.powM hab) fun ⟨P₁, hP₁, h₁⟩ => nn_bind (hM.powM hP₁) fun ⟨P₂, hP₂, h₂⟩ => ?_
  have he : ∀ i, M (Env.cons P₂ (Env.cons a (Env.cons b envω)) i) :=
    Env.cons_mem hP₂ (Env.cons_mem ha (Env.cons_mem hb hM.envω_mem))
  let ψ : Fml := ex (and (mem 0 3) (ex (and (mem 0 5) (pairF 2 1 0))))
  have hT := hM.toTransClass
  -- the satisfaction of `ψ` at `q`
  have key : ∀ q, M q → (Sat M ψ (Env.cons q (Env.cons P₂ (Env.cons a (Env.cons b envω)))) ↔
      ¬¬∃ x y, x ∈ a ∧ y ∈ b ∧ q ≈ PSet.pair x y) := by
    intro q hq
    have he1 := Env.cons_mem hq he
    refine sat_ex.trans ⟨fun h => nn_bind h fun ⟨x, hx, hs⟩ => ?_, fun h => nn_bind h fun ⟨x, y, hxa, hyb, e⟩ => ?_⟩
    · have ⟨hxa, hs⟩ := sat_and.1 hs
      refine nn_map (fun ⟨y, hy, hs⟩ => ?_) (sat_ex.1 hs)
      have ⟨hyb, hs⟩ := sat_and.1 hs
      exact ⟨x, y, hxa, hyb, (hT.sat_pairF (Env.cons_mem hy (Env.cons_mem hx he1)) 2 1 0).1 hs⟩
    · have hx := hM.trans ha hxa
      have hy := hM.trans hb hyb
      exact nn_intro ⟨x, hx, sat_and.2 ⟨hxa, sat_ex.2 (nn_intro ⟨y, hy, sat_and.2 ⟨hyb,
        (hT.sat_pairF (Env.cons_mem hy (Env.cons_mem hx he1)) 2 1 0).2 e⟩⟩)⟩⟩
  have hψ : ∀ q q' : PSet.{u}, q ≈ q' → Sat M ψ (Env.cons q (Env.cons P₂ (Env.cons a (Env.cons b envω)))) →
      Sat M ψ (Env.cons q' (Env.cons P₂ (Env.cons a (Env.cons b envω)))) := fun _ _ e h =>
    Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) h
  refine nn_intro ⟨_, hM.sepM ψ he, fun q => (mem_sep hψ).trans ⟨fun ⟨hq, h⟩ => (key q (hM.trans hP₂ hq)).1 h,
    fun h => ?_⟩⟩
  -- pairs of members lie in the internal double powerset
  have hpair : ∀ x y, x ∈ a → y ∈ b → PSet.pair x y ∈ P₂ := by
    intro x y hxa hyb
    have hx := hM.trans ha hxa
    have hy := hM.trans hb hyb
    have hxu : x ∈ PSet.union a b := mem_union.2 (nn_intro (.inl hxa))
    have hyu : y ∈ PSet.union a b := mem_union.2 (nn_intro (.inr hyb))
    have h1 : singleton x ∈ P₁ := (h₁ _ (hM.single hx)).2 fun z hz => (mem_congr_left (mem_singleton.1 hz)).2 hxu
    have h2 : PSet.upair x y ∈ P₁ := (h₁ _ (hM.upair hx hy)).2 fun z hz => Stable.of_nn (mem_upair.1 hz) fun
      | .inl e => (mem_congr_left e).2 hxu
      | .inr e => (mem_congr_left e).2 hyu
    exact (h₂ _ (hM.pair hx hy)).2 fun z hz => Stable.of_nn (mem_upair.1 hz) fun
      | .inl e => (mem_congr_left e).2 h1
      | .inr e => (mem_congr_left e).2 h2
  have hqP : q ∈ P₂ := Stable.of_nn h fun ⟨x, y, hxa, hyb, e⟩ => (mem_congr_left e).2 (hpair x y hxa hyb)
  exact ⟨hqP, (key q (hM.trans hP₂ hqP)).2 h⟩

/-- **Graph normalization.** The restriction of a member `f` to a member `p` is a member. -/
theorem cleanM {f p : PSet.{u}} (hf : M f) (hp : M p) : M (sep (fun q => q ∈ p) f) :=
  have he : ∀ i, M (Env.cons f (Env.cons p envω) i) := Env.cons_mem hf (Env.cons_mem hp hM.envω_mem)
  hM.resp (ext fun _ => (mem_sep fun _ _ e h => Sat.resp (mem 0 2) (Env.cons_resp e fun _ => Equiv.refl _) h).trans
    (mem_sep fun _ _ e h => (mem_congr_left e).1 h).symm) (hM.sepM (mem 0 2) he)

/-- Cleaning a function: a pure function in `M` with the same pair-edges. -/
theorem normalizeFun {f a b : PSet.{u}} (hf : M f) (ha : M a) (hb : M b) (h : IsFun f a b) :
    ¬¬∃ f', M f' ∧ IsFun f' a b ∧ (∀ q, q ∈ f' → ¬¬∃ x y, x ∈ a ∧ y ∈ b ∧ q ≈ PSet.pair x y) ∧
      ∀ x y, PSet.pair x y ∈ f' ↔ PSet.pair x y ∈ f := by
  refine nn_map (fun ⟨p, hp, hpm⟩ => ?_) (hM.prodM ha hb)
  have hsep : ∀ q q' : PSet.{u}, q ≈ q' → q ∈ p → q' ∈ p := fun _ _ e h => (mem_congr_left e).1 h
  have edge : ∀ x y, PSet.pair x y ∈ sep (fun q => q ∈ p) f ↔ PSet.pair x y ∈ f := fun x y =>
    (mem_sep hsep).trans ⟨fun h => h.1, fun hxy => ⟨hxy, (hpm _).2 (nn_intro ⟨x, y, (h.1 x y hxy).1,
      (h.1 x y hxy).2, Equiv.refl _⟩)⟩⟩
  refine ⟨_, hM.cleanM hf hp, ⟨fun x y hxy => h.1 x y ((edge x y).1 hxy),
    fun x y y' h1 h2 => h.2.1 x y y' ((edge x y).1 h1) ((edge x y').1 h2),
    fun x hx => nn_map (fun ⟨y, hy⟩ => ⟨y, (edge x y).2 hy⟩) (h.2.2 x hx)⟩,
    fun q hq => (hpm q).1 ((mem_sep hsep).1 hq).2, edge⟩

end SynZF

/-- Cleaning a cofinal relation: a pure cofinal relation in `M` with the same pair-edges. -/
theorem SynZF.normalizeCof {M : PSet.{u+1} → Prop} (hM : SynZF M) {g Q ζ : PSet.{u+1}}
    (hg : M g) (hQ : M Q) (hζ : M ζ) (h : Cof g Q ζ) :
    ¬¬∃ g', M g' ∧ Cof g' Q ζ ∧ (∀ q, q ∈ g' → ¬¬∃ x y, x ∈ Q ∧ y ∈ ζ ∧ q ≈ PSet.pair x y) ∧
      ∀ x y, PSet.pair x y ∈ g' ↔ PSet.pair x y ∈ g := by
  refine nn_map (fun ⟨p, hp, hpm⟩ => ?_) (hM.prodM hQ hζ)
  have hsep : ∀ q q' : PSet.{u+1}, q ≈ q' → q ∈ p → q' ∈ p := fun _ _ e h => (mem_congr_left e).1 h
  have edge : ∀ x y, PSet.pair x y ∈ sep (fun q => q ∈ p) g ↔ PSet.pair x y ∈ g := fun x y =>
    (mem_sep hsep).trans ⟨fun h => h.1, fun hxy => ⟨hxy, (hpm _).2 (nn_intro ⟨x, y, (h.1 x y hxy).1,
      (h.1 x y hxy).2, Equiv.refl _⟩)⟩⟩
  refine ⟨_, hM.cleanM hg hp, ⟨fun x y hxy => h.1 x y ((edge x y).1 hxy),
    fun x y y' h1 h2 => h.2.1 x y y' ((edge x y).1 h1) ((edge x y').1 h2),
    fun ξ hξ => nn_map (fun ⟨x, y, hxy, hs⟩ => ⟨x, y, (edge x y).2 hxy, hs⟩) (h.2.2 ξ hξ)⟩,
    fun q hq => (hpm q).1 ((mem_sep hsep).1 hq).2, edge⟩

/-- **Choice functions from the choice sentence.** In a class validating `ac`, every member
whose members are nonempty has a pure choice function in the class: the functional choice
relation supplied by `ac` is cleaned to the product with the union. -/
theorem SynZF.choiceFun_of_ac {M : PSet.{u} → Prop} (hM : SynZF M) (hac : Valid M ac) {t : PSet.{u}}
    (ht : M t) (hne : ∀ A, A ∈ t → ¬¬∃ x, x ∈ A) :
    ¬¬∃ f, M f ∧ IsFun f t (PSet.sUnion t) ∧
      (∀ q, q ∈ f → ¬¬∃ A x, A ∈ t ∧ x ∈ PSet.sUnion t ∧ q ≈ PSet.pair A x) ∧
      ∀ A x, PSet.pair A x ∈ f → x ∈ A := by
  have hT := hM.toTransClass
  have he : ∀ i, M (Env.cons t envω i) := Env.cons_mem ht hM.envω_mem
  have h := hac envω hM.envω_mem t ht fun A hA hAt => sat_ex.2
    (nn_map (fun ⟨x, hx⟩ => ⟨x, hM.trans hA hx, hx⟩) (hne A hAt))
  refine nn_bind (sat_ex.1 h) fun ⟨g, hg, hs⟩ => ?_
  have ⟨h1, h2⟩ := sat_and.1 hs
  have he2 : ∀ i, M (Env.cons g (Env.cons t envω) i) := Env.cons_mem hg he
  -- the relation supplied by `ac`, read ambiently
  have val : ∀ A, A ∈ t → ¬¬∃ x, x ∈ A ∧ PSet.pair A x ∈ g := fun A hAt => by
    have hA := hM.trans ht hAt
    refine nn_map (fun ⟨x, hx, hs⟩ => ?_) (sat_ex.1 (h1 A hA hAt))
    have ⟨hp, hxA⟩ := sat_and.1 hs
    exact ⟨x, hxA, (hT.sat_pairMemF (Env.cons_mem hx (Env.cons_mem hA he2)) 2 1 0).1 hp⟩
  have func : ∀ A x x', PSet.pair A x ∈ g → PSet.pair A x' ∈ g → x ≈ x' := fun A x x' hp hp' => by
    have ⟨hA, hx⟩ := hT.of_pair_mem hg hp
    have hx' := (hT.of_pair_mem hg hp').2
    have he3 : ∀ i, M (Env.cons x' (Env.cons x (Env.cons A (Env.cons g (Env.cons t envω)))) i) :=
      Env.cons_mem hx' (Env.cons_mem hx (Env.cons_mem hA he2))
    exact h2 A hA x hx x' hx' ((hT.sat_pairMemF he3 3 2 1).2 hp) ((hT.sat_pairMemF he3 3 2 0).2 hp')
  refine nn_map (fun ⟨p, hp, hpm⟩ => ?_) (hM.prodM ht (hM.sUnion ht))
  have hsep : ∀ q q' : PSet.{u}, q ≈ q' → q ∈ p → q' ∈ p := fun _ _ e h => (mem_congr_left e).1 h
  have edge : ∀ A x, PSet.pair A x ∈ sep (fun q => q ∈ p) g ↔
      PSet.pair A x ∈ g ∧ A ∈ t ∧ x ∈ PSet.sUnion t := fun A x =>
    (mem_sep hsep).trans ⟨fun ⟨h1, h2⟩ => ⟨h1, Stable.of_nn ((hpm _).1 h2) fun ⟨A', x', hA', hx', e⟩ =>
        have ⟨eA, ex⟩ := pair_inj e
        ⟨(mem_congr_left eA).2 hA', (mem_congr_left ex).2 hx'⟩⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h1, (hpm _).2 (nn_intro ⟨A, x, h2, h3, Equiv.refl _⟩)⟩⟩
  refine ⟨_, hM.cleanM hg hp, ⟨fun A x h => ((edge A x).1 h).2,
    fun A x x' h h' => func A x x' ((edge A x).1 h).1 ((edge A x').1 h').1, fun A hAt => ?_⟩,
    fun q hq => (hpm q).1 ((mem_sep hsep).1 hq).2, fun A x h => ?_⟩
  · exact nn_map (fun ⟨x, hxA, hp⟩ => ⟨x, (edge A x).2 ⟨hp, hAt, mem_sUnion.2 (nn_intro ⟨A, hAt, hxA⟩)⟩⟩)
      (val A hAt)
  · have ⟨hp, hAt, _⟩ := (edge A x).1 h
    exact Stable.of_nn (val A hAt) fun ⟨x', hx'A, hp'⟩ => (mem_congr_left (func A x' x hp' hp)).1 hx'A

/-- info: 'PSet.SynZF.choiceFun_of_ac' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.choiceFun_of_ac
/-- info: 'PSet.SynZF.replM' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.replM
/-- info: 'PSet.SynZF.normalizeFun' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.normalizeFun

end PSet
