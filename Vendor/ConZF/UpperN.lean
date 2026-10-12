import Vendor.ConZF.Interval
import Vendor.ConZF.ReflectN
/-!
The concrete constructible upper class and the classification fields of `UpperModel`. A stable,
bisimulation-respecting `ZFModel` is a `SynZF` class (`SynZF.of_zfModel`); at the upper universe
the seeded hereditarily-good class with seed `K` is such a model under the accessibility
hypothesis, and `NL := Constr` of it is a syntactic `ZF` class containing `K`, every lifted lower
ordinal, and the identity graph on each of its members.

The three cofinality classification fields are discharged for any `SynZF` class (conzf16 §A5,
§A7), with no choice and no canonical order: the identity graph on a nonzero ordinal at most `ω`
is a partial cofinal graph from `ω`; failure of regularity supplies negatively an unbounded
function from a smaller ordinal, which ordinal comparison makes cofinal; regularity above `ω`
implies initiality (the zero-totalized reverse of an injection would be a bounded function
covering `κ`) and limitness (the constant function at a predecessor would be bounded), so a
regular non-inaccessible fails strong limit, and the reverse of the supplied injection
restricted to `P × κ` is a partial cofinal graph from `P`. The constructor
`upperModel_of_leastCof` then exposes the remaining inputs of `UpperModel`: the least partial
cofinal relation and its laws; `con_ZFCI_of_leastCof` states the conditional consistency with
every outstanding assumption visible.
-/
universe u

namespace PSet
open Fml CardF RecF

/-- A stable, bisimulation-respecting model of `ZF` is a syntactic `ZF` class. -/
theorem SynZF.of_zfModel {M : PSet.{u} → Prop} (hZ : ZFModel M) (hst : ∀ x, Stable (M x))
    (hresp : ∀ {x y}, x ≈ y → M x → M y) : SynZF M :=
  ⟨hst, hresp, hZ.trans, hZ.omega, hZ.valid⟩

/-- The identity graph on a lifted ordinal `η ≤ ζ` is a partial cofinal relation from `lift ζ`. -/
theorem cof_idGraph_le {η ζ : PSet.{u}} (hζ : IsOrd ζ) (hle : η ∈ succ ζ) :
    Cof (idGraph (lift η)) (lift ζ) (lift η) := by
  have hsub : ∀ x, x ∈ η → x ∈ ζ := fun x hx => Stable.of_nn (mem_succ.1 hle) fun
    | .inl h => hζ.trans _ h x hx
    | .inr e => (mem_congr_right e).1 hx
  refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun ξ hξ => ?_⟩
  · refine Stable.of_nn (mem_idGraph.1 hp) fun ⟨z, hz, e⟩ => ?_
    have ⟨ex, ey⟩ := pair_inj e
    refine ⟨?_, (mem_congr_left ey).2 hz⟩
    refine Stable.of_nn (mem_lift.1 hz) fun ⟨x₀, hx₀, e'⟩ => ?_
    exact (mem_congr_left (ex.trans e')).2 (lift_mem_of_mem (hsub x₀ hx₀))
  · refine Stable.of_nn (mem_idGraph.1 hp) fun ⟨z, _, e⟩ =>
      Stable.of_nn (mem_idGraph.1 hp') fun ⟨z', _, e'⟩ => ?_
    have ⟨ex, ey⟩ := pair_inj e
    have ⟨ex', ey'⟩ := pair_inj e'
    exact ey.trans ((ex.symm.trans ex').trans ey'.symm)
  · exact nn_intro ⟨ξ, ξ, mem_idGraph.2 (nn_intro ⟨ξ, hξ, Equiv.refl _⟩), self_mem_succ ξ⟩

namespace SynZF
variable {N : PSet.{u} → Prop} (hN : SynZF N)
include hN

/-- Identity graphs belong to the class whenever their domains do. -/
theorem idGraph_mem {X : PSet.{u}} (hX : N X) : N (idGraph X) := by
  have hT := hN.toTransClass
  have he : ∀ i, N (Env.cons X envω i) := Env.cons_mem hX hN.envω_mem
  have hf : ∀ x y y', x ∈ Env.cons X envω 0 → N y → N y' →
      Sat N (pairF 1 0 0) (Env.cons x (Env.cons y (Env.cons X envω))) →
      Sat N (pairF 1 0 0) (Env.cons x (Env.cons y' (Env.cons X envω))) → y ≈ y' := fun x y y' hx hy hy' h1 h2 =>
    ((hT.sat_pairF (Env.cons_mem (hN.trans hX hx) (Env.cons_mem hy he)) 1 0 0).1 h1).trans
      ((hT.sat_pairF (Env.cons_mem (hN.trans hX hx) (Env.cons_mem hy' he)) 1 0 0).1 h2).symm
  refine (hN.stable _).dne (nn_map (fun ⟨b, hb, hcol⟩ => ?_) (hN.replM (pairF 1 0 0) he hf))
  have he' : ∀ i, N (Env.cons b (Env.cons X envω) i) := Env.cons_mem hb he
  let ψ : Fml := ex (and (mem 0 3) (pairF 1 0 0))
  refine hN.resp (ext fun z => ?_) (hN.sepM ψ he')
  refine (mem_sep fun _ _ e k => Sat.resp _ (Env.cons_resp e fun _ => Equiv.refl _) k).trans (Iff.trans ?_ mem_idGraph.symm)
  constructor
  · intro ⟨hzb, hs⟩
    refine nn_map (fun ⟨x, hx, hs⟩ => ?_) (sat_ex.1 hs)
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨x, h1, (hT.sat_pairF (Env.cons_mem hx (Env.cons_mem (hN.trans hb hzb) he')) 1 0 0).1 h2⟩
  · intro k
    refine Stable.of_nn k fun ⟨x, hx, e⟩ => ?_
    have hxN := hN.trans hX hx
    have hzN : N z := hN.resp e.symm (hN.pair hxN hxN)
    have hp : Sat N (pairF 1 0 0) (Env.cons x (Env.cons z (Env.cons X envω))) :=
      (hT.sat_pairF (Env.cons_mem hxN (Env.cons_mem hzN he)) 1 0 0).2 e
    refine ⟨hcol x z hx hzN hp, sat_ex.2 (nn_intro ⟨x, hxN, sat_and.2 ⟨hx, ?_⟩⟩)⟩
    exact (hT.sat_pairF (Env.cons_mem hxN (Env.cons_mem hzN he')) 1 0 0).2 e

/-! ### Regularity implies initiality and limitness -/

/-- **Regularity implies initiality**: the zero-totalized reverse of a relational injection of
`κ` into a member would be a bounded function covering `κ`. -/
theorem initialIn_of_regularIn {κ : PSet.{u}} (hκ : N κ) (hκo : IsOrd κ) (hreg : RegularIn N κ) : InitialIn N κ := by
  intro δ f hδ hf hinj
  have hT := hN.toTransClass
  have hδN := hN.trans hκ hδ
  have h0 : PSet.empty ∈ κ :=
    Stable.of_nn (mem_succ.1 (isOrd_empty.mem_succ_of_subset (hκo.mem hδ) fun z hz => (not_mem_empty z hz).elim)) fun
      | .inl h => hκo.trans δ hδ _ h
      | .inr e => (mem_congr_left e).2 hδ
  refine Stable.of_nn (hN.prodM hδN hκ) fun ⟨P, hP, hPm⟩ => ?_
  let e := Env.cons P (Env.cons f (Env.cons δ (Env.cons κ envω)))
  have he : ∀ i, N (e i) := Env.cons_mem hP (Env.cons_mem hf (Env.cons_mem hδN (Env.cons_mem hκ hN.envω_mem)))
  -- `z = ⟨x, ξ⟩ ∧ (⟨ξ, x⟩ ∈ f ∨ (¬ ∃ ξ' ∈ κ, ⟨ξ', x⟩ ∈ f) ∧ ξ = ∅)`, under `[ξ, x, z, P, f, δ, κ]`
  let ψ : Fml := ex (ex (and (pairF 2 1 0) (or (pairMemF 4 0 1)
    (and (neg (ex (and (mem 0 7) (pairMemF 5 0 2)))) (emptyF 0)))))
  let Q : PSet.{u} → PSet.{u} → Prop := fun x ξ =>
    PSet.pair ξ x ∈ f ∨ (¬ (¬¬∃ ξ', ξ' ∈ κ ∧ PSet.pair ξ' x ∈ f) ∧ ξ ≈ PSet.empty)
  have read : ∀ z, N z → (Sat N ψ (Env.cons z e) ↔ ¬¬∃ x ξ, N x ∧ N ξ ∧ z ≈ PSet.pair x ξ ∧ ¬¬ Q x ξ) := by
    intro z hz
    have he1 : ∀ i, N (Env.cons z e i) := Env.cons_mem hz he
    refine sat_ex.trans ⟨fun k => nn_bind k fun ⟨x, hx, k⟩ => nn_map (fun ⟨ξ, hξ, hs⟩ => ?_) (sat_ex.1 k),
      fun k => nn_map (fun ⟨x, ξ, hx, hξ, ez, hq⟩ => ?_) k⟩
    · have hE : ∀ i, N (Env.cons ξ (Env.cons x (Env.cons z e)) i) := Env.cons_mem hξ (Env.cons_mem hx he1)
      have ⟨h1, h2⟩ := sat_and.1 hs
      refine ⟨x, ξ, hx, hξ, (hT.sat_pairF hE 2 1 0).1 h1, nn_map (fun h => h.imp (fun h => (hT.sat_pairMemF hE 4 0 1).1 h)
        fun h => ?_) (sat_or.1 h2)⟩
      have ⟨h3, h4⟩ := sat_and.1 h
      refine ⟨fun k => h3 (sat_ex.2 (nn_map (fun ⟨ξ', hξ', hp⟩ => ⟨ξ', hN.trans hκ hξ', sat_and.2 ⟨hξ', ?_⟩⟩) k)),
        (hT.sat_emptyF hE 0).1 h4⟩
      exact (hT.sat_pairMemF (Env.cons_mem (hN.trans hκ hξ') hE) 5 0 2).2 hp
    · have hE : ∀ i, N (Env.cons ξ (Env.cons x (Env.cons z e)) i) := Env.cons_mem hξ (Env.cons_mem hx he1)
      refine ⟨x, hx, sat_ex.2 (nn_intro ⟨ξ, hξ, sat_and.2 ⟨(hT.sat_pairF hE 2 1 0).2 ez, sat_or.2 (nn_map (fun h =>
        h.imp (fun h => (hT.sat_pairMemF hE 4 0 1).2 h) fun ⟨h3, h4⟩ => sat_and.2 ⟨fun k => h3 ?_, (hT.sat_emptyF hE 0).2 h4⟩) hq)⟩⟩)⟩
      refine nn_map (fun ⟨ξ', hξ'N, hs⟩ => ?_) (sat_ex.1 k)
      have ⟨a, b⟩ := sat_and.1 hs
      exact ⟨ξ', a, (hT.sat_pairMemF (Env.cons_mem hξ'N hE) 5 0 2).1 b⟩
  let g := PSet.sep (fun z => Sat N ψ (Env.cons z e)) P
  have hg : N g := hN.sepM ψ he
  have hgm : ∀ z, z ∈ g ↔ z ∈ P ∧ Sat N ψ (Env.cons z e) := fun z =>
    mem_sep fun _ _ e' k => Sat.resp _ (Env.cons_resp e' fun _ => Equiv.refl _) k
  have intro_g : ∀ x ξ, x ∈ δ → ξ ∈ κ → Q x ξ → PSet.pair x ξ ∈ g := fun x ξ hx hξ hq =>
    have hxN := hN.trans hδN hx
    have hξN := hN.trans hκ hξ
    (hgm _).2 ⟨(hPm _).2 (nn_intro ⟨x, ξ, hx, hξ, Equiv.refl _⟩),
      (read _ (hN.pair hxN hξN)).2 (nn_intro ⟨x, ξ, hxN, hξN, Equiv.refl _, nn_intro hq⟩)⟩
  have hfun : IsFun g δ κ := by
    refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun x hx => ?_⟩
    · exact Stable.of_nn ((hPm _).1 ((hgm _).1 hp).1) fun ⟨x', y', hx', hy', e'⟩ =>
        have ⟨ex, ey⟩ := pair_inj e'
        ⟨(mem_congr_left ex).2 hx', (mem_congr_left ey).2 hy'⟩
    · have hyκ : y ∈ κ := Stable.of_nn ((hPm _).1 ((hgm _).1 hp).1) fun ⟨_, y', _, hy', e'⟩ =>
        (mem_congr_left (pair_inj e').2).2 hy'
      have hy'κ : y' ∈ κ := Stable.of_nn ((hPm _).1 ((hgm _).1 hp').1) fun ⟨_, y'', _, hy'', e'⟩ =>
        (mem_congr_left (pair_inj e').2).2 hy''
      have hzN : N (PSet.pair x y) := hN.trans hP ((hgm _).1 hp).1
      have hz'N : N (PSet.pair x y') := hN.trans hP ((hgm _).1 hp').1
      refine Stable.of_nn ((read _ hzN).1 ((hgm _).1 hp).2) fun ⟨x₁, ξ₁, _, _, e₁, q₁⟩ =>
        Stable.of_nn ((read _ hz'N).1 ((hgm _).1 hp').2) fun ⟨x₂, ξ₂, _, _, e₂, q₂⟩ => ?_
      have ⟨ex₁, ey₁⟩ := pair_inj e₁
      have ⟨ex₂, ey₂⟩ := pair_inj e₂
      have ex : x₁ ≈ x₂ := ex₁.symm.trans ex₂
      refine Stable.of_nn q₁ fun q₁ => Stable.of_nn q₂ fun q₂ => ?_
      rcases q₁ with a₁ | ⟨n₁, z₁⟩ <;> rcases q₂ with a₂ | ⟨n₂, z₂⟩
      · exact ey₁.trans ((hinj.inj ξ₁ ξ₂ x₁ x₂ a₁ a₂ ex).trans ey₂.symm)
      · exact (n₂ (nn_intro ⟨ξ₁, (mem_congr_left ey₁).1 hyκ, (mem_congr_left (pair_congr (Equiv.refl _) ex)).1 a₁⟩)).elim
      · exact (n₁ (nn_intro ⟨ξ₂, (mem_congr_left ey₂).1 hy'κ, (mem_congr_left (pair_congr (Equiv.refl _) ex.symm)).1 a₂⟩)).elim
      · exact ey₁.trans (z₁.trans (z₂.symm.trans ey₂.symm))
    · refine Stable.by_cases (¬¬∃ ξ', ξ' ∈ κ ∧ PSet.pair ξ' x ∈ f)
        (fun k => nn_bind k fun ⟨ξ', hξ', hp⟩ => nn_intro ⟨ξ', intro_g x ξ' hx hξ' (.inl hp)⟩)
        fun k => nn_intro ⟨PSet.empty, intro_g x PSet.empty hx h0 (.inr ⟨k, Equiv.refl _⟩)⟩
  refine Stable.of_nn (hreg δ g hδ hg hfun) fun ⟨β, hβ, hb⟩ => ?_
  refine Stable.of_nn (hinj.total β hβ) fun ⟨w, hw, hp⟩ => ?_
  exact not_mem_self β (hb w β (intro_g w β hw hβ (.inl hp)))

/-- **Regularity above `ω` implies limitness**: the constant function at a predecessor would be
bounded. -/
theorem succ_mem_of_regularIn {κ : PSet.{u}} (hκ : N κ) (hκo : IsOrd κ) (hω : PSet.omega ∈ κ) (hreg : RegularIn N κ)
    {μ : PSet.{u}} (hμ : μ ∈ κ) : succ μ ∈ κ := by
  have hT := hN.toTransClass
  have hμN := hN.trans hκ hμ
  refine Stable.of_nn (mem_succ.1 ((hκo.mem hμ).succ.mem_succ_of_subset hκo fun z hz =>
    Stable.of_nn (mem_succ.1 hz) fun
      | .inl h => hκo.trans μ hμ z h
      | .inr e => (mem_congr_left e).2 hμ)) fun
    | .inl h => h
    | .inr eκ => ?_
  refine Stable.of_nn (hN.prodM hN.omega hκ) fun ⟨P, hP, hPm⟩ => ?_
  let e := Env.cons P (Env.cons μ (Env.cons κ envω))
  have he : ∀ i, N (e i) := Env.cons_mem hP (Env.cons_mem hμN (Env.cons_mem hκ hN.envω_mem))
  -- `z = ⟨x, ξ⟩ ∧ ξ = μ`, under `[ξ, x, z, P, μ, κ]`
  let ψ : Fml := ex (ex (and (pairF 2 1 0) (eq 0 4)))
  let c := PSet.sep (fun z => Sat N ψ (Env.cons z e)) P
  have hc : N c := hN.sepM ψ he
  have hcm : ∀ z, z ∈ c ↔ z ∈ P ∧ Sat N ψ (Env.cons z e) := fun z =>
    mem_sep fun _ _ e' k => Sat.resp _ (Env.cons_resp e' fun _ => Equiv.refl _) k
  have read : ∀ z, N z → Sat N ψ (Env.cons z e) → ¬¬∃ x ξ, z ≈ PSet.pair x ξ ∧ ξ ≈ μ := by
    intro z hz hs
    have he1 : ∀ i, N (Env.cons z e i) := Env.cons_mem hz he
    refine nn_bind (sat_ex.1 hs) fun ⟨x, hx, k⟩ => nn_map (fun ⟨ξ, hξ, hs⟩ => ?_) (sat_ex.1 k)
    have hE : ∀ i, N (Env.cons ξ (Env.cons x (Env.cons z e)) i) := Env.cons_mem hξ (Env.cons_mem hx he1)
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨x, ξ, (hT.sat_pairF hE 2 1 0).1 h1, h2⟩
  have intro_c : ∀ n, n ∈ PSet.omega → PSet.pair n μ ∈ c := by
    intro n hn
    have hnN := hN.trans hN.omega hn
    have hzN := hN.pair hnN hμN
    have hE : ∀ i, N (Env.cons μ (Env.cons n (Env.cons (PSet.pair n μ) e)) i) :=
      Env.cons_mem hμN (Env.cons_mem hnN (Env.cons_mem hzN he))
    refine (hcm _).2 ⟨(hPm _).2 (nn_intro ⟨n, μ, hn, hμ, Equiv.refl _⟩), ?_⟩
    exact sat_ex.2 (nn_intro ⟨n, hnN, sat_ex.2 (nn_intro ⟨μ, hμN, sat_and.2 ⟨(hT.sat_pairF hE 2 1 0).2 (Equiv.refl _), Equiv.refl _⟩⟩)⟩)
  have hfun : IsFun c PSet.omega κ := by
    refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun n hn => nn_intro ⟨μ, intro_c n hn⟩⟩
    · exact Stable.of_nn ((hPm _).1 ((hcm _).1 hp).1) fun ⟨x', y', hx', hy', e'⟩ =>
        have ⟨ex, ey⟩ := pair_inj e'
        ⟨(mem_congr_left ex).2 hx', (mem_congr_left ey).2 hy'⟩
    · have hzN : N (PSet.pair x y) := hN.trans hP ((hcm _).1 hp).1
      have hz'N : N (PSet.pair x y') := hN.trans hP ((hcm _).1 hp').1
      refine Stable.of_nn (read _ hzN ((hcm _).1 hp).2) fun ⟨_, ξ₁, e₁, eμ₁⟩ =>
        Stable.of_nn (read _ hz'N ((hcm _).1 hp').2) fun ⟨_, ξ₂, e₂, eμ₂⟩ => ?_
      exact (pair_inj e₁).2.trans (eμ₁.trans (eμ₂.symm.trans (pair_inj e₂).2.symm))
  refine Stable.of_nn (hreg PSet.omega c hω hc hfun) fun ⟨β, hβ, hb⟩ => ?_
  have hμβ : μ ∈ β := hb _ μ (intro_c PSet.empty (ofNat_mem_omega 0))
  have hβs : β ∈ succ μ := (mem_congr_right eκ).2 hβ
  refine Stable.of_nn (mem_succ.1 hβs) fun
    | .inl h => (not_mem_self μ ((hκo.mem hμ).trans β h μ hμβ)).elim
    | .inr e => (not_mem_self μ ((mem_congr_right e).1 hμβ)).elim

end SynZF

/-! ### The classification fields for any syntactic class of the upper universe -/

namespace SynZF
variable {N : PSet.{u+1} → Prop} (hN : SynZF N)
include hN

omit hN in
/-- A total function with no strict bound is cofinal, by ordinal comparison. -/
theorem cof_of_unbounded {κ δ f : PSet.{u+1}} (hκo : IsOrd κ) (hf : IsFun f δ κ)
    (hu : ¬ ∃ β, β ∈ κ ∧ ∀ x y, PSet.pair x y ∈ f → y ∈ β) : Cof f δ κ := by
  refine ⟨hf.1, hf.2.1, fun ξ hξ hno => hu ⟨ξ, hξ, fun x y hp => ?_⟩⟩
  have hy := (hf.1 x y hp).2
  refine Stable.of_nn ((hκo.mem hy).trichotomy (hκo.mem hξ)) fun
    | .inl h => h
    | .inr (.inl e) => (hno ⟨x, y, hp, mem_succ_of_equiv e.symm⟩).elim
    | .inr (.inr h) => (hno ⟨x, y, hp, mem_succ_of_mem h⟩).elim

omit hN in
/-- **Smaller cofinality or regular**: failure of regularity supplies negatively an unbounded
function from a member, which is cofinal. -/
theorem cof_lt_or_reg_of_synZF {κ : PSet.{u+1}} (hκo : IsOrd κ) :
    ¬¬((¬¬∃ δ, δ ∈ κ ∧ ¬¬∃ g, N g ∧ Cof g δ κ) ∨ RegularIn N κ) := by
  refine Stable.by_cases (RegularIn N κ) (fun h => nn_intro (.inr h)) fun hn => nn_intro (.inl fun k => hn ?_)
  intro δ f hδ hf hfun hb
  exact k ⟨δ, hδ, nn_intro ⟨f, hf, cof_of_unbounded hκo hfun hb⟩⟩

/-- **Regular but not inaccessible**: strong limit fails, and the reverse of the supplied
injection restricted to `P × κ` is a partial cofinal graph from `P`, with `succ lam ∈ κ`. -/
theorem cof_powerset_of_synZF {κ : PSet.{u+1}} (hκ : N κ) (hκo : IsOrd κ) (hω : PSet.omega ∈ κ) (hreg : RegularIn N κ)
    (hni : ¬ InaccIn N κ) :
    ¬¬∃ lam P, lam ∈ κ ∧ succ lam ∈ κ ∧ N P ∧ (∀ w, w ∈ P → w ∈ powerset lam) ∧ ¬¬∃ g, N g ∧ Cof g P κ := by
  have hT := hN.toTransClass
  have hinit := hN.initialIn_of_regularIn hκ hκo hreg
  have hnsl : ¬ StrongLimitIn N κ := fun hsl => hni ⟨hκo, hω, hinit, hreg, hsl⟩
  -- negative existence of a witness against strong limit
  have hw : ¬¬∃ lam θ P f, lam ∈ κ ∧ IsOrd θ ∧ N P ∧ N f ∧ (∀ w, w ∈ P → w ∈ powerset lam) ∧ IsInjRel θ P f ∧ ¬ θ ∈ κ := by
    intro k
    refine hnsl fun lam θ P f hlam hθ hP hf hpow hinj => ?_
    exact (inferInstance : Stable (θ ∈ κ)).dne fun hn => k ⟨lam, θ, P, f, hlam, hθ, hP, hf, hpow, hinj, hn⟩
  refine Stable.of_nn hw fun ⟨lam, θ, P, f, hlam, hθ, hP, hf, hpow, hinj, hnθ⟩ => ?_
  have hsub : ∀ ξ, ξ ∈ κ → ξ ∈ θ := fun ξ hξ => Stable.of_nn (hθ.trichotomy hκo) fun
    | .inl h => (hnθ h).elim
    | .inr (.inl e) => (mem_congr_right e).2 hξ
    | .inr (.inr h) => hθ.trans κ h ξ hξ
  refine Stable.of_nn (hN.prodM hP hκ) fun ⟨Pr, hPr, hPrm⟩ => ?_
  let e := Env.cons Pr (Env.cons f (Env.cons P (Env.cons κ envω)))
  have he : ∀ i, N (e i) := Env.cons_mem hPr (Env.cons_mem hf (Env.cons_mem hP (Env.cons_mem hκ hN.envω_mem)))
  -- `z = ⟨w, ξ⟩ ∧ ⟨ξ, w⟩ ∈ f`, under `[ξ, w, z, Pr, f, P, κ]`
  let ψ : Fml := ex (ex (and (pairF 2 1 0) (pairMemF 4 0 1)))
  let g := PSet.sep (fun z => Sat N ψ (Env.cons z e)) Pr
  have hg : N g := hN.sepM ψ he
  have hgm : ∀ z, z ∈ g ↔ z ∈ Pr ∧ Sat N ψ (Env.cons z e) := fun z =>
    mem_sep fun _ _ e' k => Sat.resp _ (Env.cons_resp e' fun _ => Equiv.refl _) k
  have read : ∀ z, N z → Sat N ψ (Env.cons z e) → ¬¬∃ w ξ, z ≈ PSet.pair w ξ ∧ PSet.pair ξ w ∈ f := by
    intro z hz hs
    have he1 : ∀ i, N (Env.cons z e i) := Env.cons_mem hz he
    refine nn_bind (sat_ex.1 hs) fun ⟨w, hwN, k⟩ => nn_map (fun ⟨ξ, hξ, hs⟩ => ?_) (sat_ex.1 k)
    have hE : ∀ i, N (Env.cons ξ (Env.cons w (Env.cons z e)) i) := Env.cons_mem hξ (Env.cons_mem hwN he1)
    have ⟨h1, h2⟩ := sat_and.1 hs
    exact ⟨w, ξ, (hT.sat_pairF hE 2 1 0).1 h1, (hT.sat_pairMemF hE 4 0 1).1 h2⟩
  have intro_g : ∀ w ξ, w ∈ P → ξ ∈ κ → PSet.pair ξ w ∈ f → PSet.pair w ξ ∈ g := by
    intro w ξ hw hξ hp
    have hwN := hN.trans hP hw
    have hξN := hN.trans hκ hξ
    have hzN := hN.pair hwN hξN
    have hE : ∀ i, N (Env.cons ξ (Env.cons w (Env.cons (PSet.pair w ξ) e)) i) :=
      Env.cons_mem hξN (Env.cons_mem hwN (Env.cons_mem hzN he))
    refine (hgm _).2 ⟨(hPrm _).2 (nn_intro ⟨w, ξ, hw, hξ, Equiv.refl _⟩), ?_⟩
    exact sat_ex.2 (nn_intro ⟨w, hwN, sat_ex.2 (nn_intro ⟨ξ, hξN, sat_and.2 ⟨(hT.sat_pairF hE 2 1 0).2 (Equiv.refl _),
      (hT.sat_pairMemF hE 4 0 1).2 hp⟩⟩)⟩)
  have hcof : Cof g P κ := by
    refine ⟨fun x y hp => ?_, fun x y y' hp hp' => ?_, fun ξ hξ => ?_⟩
    · exact Stable.of_nn ((hPrm _).1 ((hgm _).1 hp).1) fun ⟨x', y', hx', hy', e'⟩ =>
        have ⟨ex, ey⟩ := pair_inj e'
        ⟨(mem_congr_left ex).2 hx', (mem_congr_left ey).2 hy'⟩
    · have hzN : N (PSet.pair x y) := hN.trans hPr ((hgm _).1 hp).1
      have hz'N : N (PSet.pair x y') := hN.trans hPr ((hgm _).1 hp').1
      refine Stable.of_nn (read _ hzN ((hgm _).1 hp).2) fun ⟨w₁, ξ₁, e₁, a₁⟩ =>
        Stable.of_nn (read _ hz'N ((hgm _).1 hp').2) fun ⟨w₂, ξ₂, e₂, a₂⟩ => ?_
      have ⟨ex₁, ey₁⟩ := pair_inj e₁
      have ⟨ex₂, ey₂⟩ := pair_inj e₂
      exact ey₁.trans ((hinj.inj ξ₁ ξ₂ w₁ w₂ a₁ a₂ (ex₁.symm.trans ex₂)).trans ey₂.symm)
    · exact nn_map (fun ⟨w, hw, hp⟩ => ⟨w, ξ, intro_g w ξ hw hξ hp, self_mem_succ ξ⟩) (hinj.total ξ (hsub ξ hξ))
  exact nn_intro ⟨lam, P, hlam, hN.succ_mem_of_regularIn hκ hκo hω hreg hlam, hP, hpow, nn_intro ⟨g, hg, hcof⟩⟩

end SynZF

/-! ### The concrete constructible upper class -/

/-- The seeded hereditarily-good class of the upper universe with seed `K`. -/
def MU : PSet.{u+1} → Prop := HG (B := seeded K.{u})

/-- Under the accessibility hypothesis of the upper universe, `MU` is a syntactic `ZF` class. -/
theorem synZF_MU_of_acc (hacc : AccHyp.{u+1}) : SynZF MU.{u} :=
  SynZF.of_zfModel (hg_model (B := seeded K.{u}) hacc) (fun x => inferInstanceAs (Stable (HG (B := seeded K.{u}) x)))
    fun e h => HG.resp (B := seeded K.{u}) e h

/-- Under pointwise accessibility of the hereditarily good ordinals of the seeded upper budget,
`MU` is a syntactic `ZF` class. This is the intended endpoint premise. -/
theorem synZF_MU_of_pointwise (hacc : @PointwiseHGAcc.{u+1} (seeded K.{u})) : SynZF MU.{u} :=
  SynZF.of_zfModel (hg_model_of_pointwise (B := seeded K.{u}) hacc)
    (fun x => inferInstanceAs (Stable (HG (B := seeded K.{u}) x))) fun e h => HG.resp (B := seeded K.{u}) e h

theorem MU_K : MU.{u} K.{u} := hg_seed K.{u}

/-- **The constructible upper class**: the constructible class of `MU`. -/
def NL : PSet.{u+1} → Prop := Constr MU.{u}

theorem synZF_NL (hMU : SynZF MU.{u}) : SynZF NL.{u} := hMU.synZF_constr

theorem NL_K (hMU : SynZF MU.{u}) : NL.{u} K.{u} := hMU.constr_of_ord isOrd_K MU_K

theorem NL_lift_ord (hMU : SynZF MU.{u}) (η : PSet.{u}) (hη : IsOrd η) : NL.{u} (lift η) :=
  hMU.constr_of_ord (isOrd_lift hη) (hMU.trans MU_K (lift_mem_K hη))

theorem NL_idGraph (hMU : SynZF MU.{u}) {X : PSet.{u+1}} (hX : NL.{u} X) : NL.{u} (idGraph X) :=
  (synZF_NL hMU).idGraph_mem hX

theorem NL_resp (hMU : SynZF MU.{u}) {x y : PSet.{u+1}} (e : x ≈ y) (hx : NL.{u} x) : NL.{u} y :=
  (synZF_NL hMU).resp e hx

/-! ### The classification fields at lifted lower ordinals -/

theorem NL_cof_small (hMU : SynZF MU.{u}) (η : PSet.{u}) (hη : IsOrd η) (hle : η ∈ succ omega) (_hne : ∃ ζ, ζ ∈ η) :
    ¬¬∃ g, NL.{u} g ∧ Cof g (lift omega) (lift η) :=
  nn_intro ⟨idGraph (lift η), NL_idGraph hMU (NL_lift_ord hMU η hη), cof_idGraph_le isOrd_omega hle⟩

theorem NL_cof_lt_or_reg (_hMU : SynZF MU.{u}) (η : PSet.{u}) (hη : IsOrd η) (_hω : omega ∈ η) :
    ¬¬((¬¬∃ d : PSet.{u}, d ∈ η ∧ ¬¬∃ g, NL.{u} g ∧ Cof g (lift d) (lift η)) ∨ RegularIn NL.{u} (lift η)) := by
  refine nn_map (fun h => h.imp (fun k => nn_bind k fun ⟨δ, hδ, k⟩ => ?_) id) (SynZF.cof_lt_or_reg_of_synZF (N := NL.{u}) (isOrd_lift hη))
  refine nn_map (fun ⟨d, hd, ed⟩ => ⟨d, hd, nn_map (fun ⟨g, hg, hc⟩ => ⟨g, hg, hc.congr_dom ed⟩) k⟩) (mem_lift.1 hδ)

theorem NL_cof_powerset (hMU : SynZF MU.{u}) (η : PSet.{u}) (hη : IsOrd η) (hω : omega ∈ η) (hreg : RegularIn NL.{u} (lift η))
    (hni : ¬ InaccIn NL.{u} (lift η)) :
    ¬¬∃ (l : PSet.{u}) (P : PSet.{u+1}), succ l ∈ η ∧ NL.{u} P ∧ (∀ w, w ∈ P → w ∈ powerset (lift l)) ∧
      ¬¬∃ g, NL.{u} g ∧ Cof g P (lift η) := by
  have hωl : PSet.omega ∈ lift η := (mem_congr_left lift_omega).1 (lift_mem_of_mem hω)
  refine nn_bind ((synZF_NL hMU).cof_powerset_of_synZF (NL_lift_ord hMU η hη) (isOrd_lift hη) hωl hreg hni)
    fun ⟨lam, P, hlam, hslam, hP, hpow, hg⟩ => ?_
  refine nn_map (fun ⟨l, _, el⟩ => ⟨l, P, ?_, hP, fun w hw => ?_, hg⟩) (mem_lift.1 hlam)
  · have : lift (succ l) ∈ lift η :=
      (mem_congr_left ((lift_succ l).trans (succ_congr el.symm))).2 hslam
    exact lift_mem.1 this
  · exact (mem_congr_right (powerset_congr el)).1 (hpow w hw)

/-! ### The remaining assembly -/

/-- **The upper model from a least partial cofinal relation.** Every field of `UpperModel` other
than the least-cofinal-relation interface is discharged for the constructible upper class. -/
def upperModel_of_leastCof (hMU : SynZF MU.{u})
    (LeastCof : PSet.{u+1} → PSet.{u+1} → PSet.{u+1} → Prop)
    (leastCof_resp : ∀ {f Q Q' ζ ζ'}, Q ≈ Q' → ζ ≈ ζ' → LeastCof f Q ζ → LeastCof f Q' ζ')
    (leastCof_unique : ∀ {f f' Q ζ}, LeastCof f Q ζ → LeastCof f' Q ζ → f ≈ f')
    (leastCof_cof : ∀ {f Q ζ}, LeastCof f Q ζ → Cof f Q ζ)
    (leastCof_exists : ∀ {Q ζ}, NL.{u} Q → NL.{u} ζ → IsOrd ζ → (¬¬∃ g, NL.{u} g ∧ Cof g Q ζ) →
      ¬¬∃ f, NL.{u} f ∧ LeastCof f Q ζ) : UpperModel.{u} where
  N := NL.{u}
  N_resp := NL_resp hMU
  N_lift_ord := NL_lift_ord hMU
  LeastCof := LeastCof
  leastCof_resp := leastCof_resp
  leastCof_unique := leastCof_unique
  leastCof_cof := leastCof_cof
  leastCof_exists := leastCof_exists
  N_idGraph := fun η hη => NL_idGraph hMU (NL_lift_ord hMU η hη)
  N_K := NL_K hMU
  cof_small := NL_cof_small hMU
  cof_lt_or_reg := NL_cof_lt_or_reg hMU
  cof_powerset := NL_cof_powerset hMU

/-- **Conditional consistency of `ZFC + ∃ inaccessible`, with every outstanding assumption
visible**: excluded middle (which yields the accessibility hypothesis, hence `SynZF MU`), a least partial cofinal
relation of the constructible upper class with its four laws, and validity of choice in that
class. Everything else is discharged. -/
theorem con_ZFCI_of_leastCof (em : ∀ p : Prop, p ∨ ¬p)
    (LeastCof : PSet.{u+1} → PSet.{u+1} → PSet.{u+1} → Prop)
    (leastCof_resp : ∀ {f Q Q' ζ ζ'}, Q ≈ Q' → ζ ≈ ζ' → LeastCof f Q ζ → LeastCof f Q' ζ')
    (leastCof_unique : ∀ {f f' Q ζ}, LeastCof f Q ζ → LeastCof f' Q ζ → f ≈ f')
    (leastCof_cof : ∀ {f Q ζ}, LeastCof f Q ζ → Cof f Q ζ)
    (leastCof_exists : ∀ {Q ζ}, NL.{u} Q → NL.{u} ζ → IsOrd ζ → (¬¬∃ g, NL.{u} g ∧ Cof g Q ζ) →
      ¬¬∃ f, NL.{u} f ∧ LeastCof f Q ζ)
    (hac : Valid NL.{u} ac) : Con ZFCI :=
  have hMU : SynZF MU.{u} := synZF_MU_of_acc (accHyp_of_not_not_em fun k => k em)
  con_ZFCI em (upperModel_of_leastCof hMU LeastCof leastCof_resp leastCof_unique leastCof_cof leastCof_exists)
    (synZF_NL hMU).toTransClass (synZF_NL hMU).valid hac

/-- info: 'PSet.synZF_NL' does not depend on any axioms -/
#guard_msgs in #print axioms synZF_NL
/-- info: 'PSet.NL_K' does not depend on any axioms -/
#guard_msgs in #print axioms NL_K
/-- info: 'PSet.SynZF.initialIn_of_regularIn' does not depend on any axioms -/
#guard_msgs in #print axioms SynZF.initialIn_of_regularIn
/-- info: 'PSet.NL_cof_powerset' does not depend on any axioms -/
#guard_msgs in #print axioms NL_cof_powerset
/-- info: 'PSet.con_ZFCI_of_leastCof' does not depend on any axioms -/
#guard_msgs in #print axioms con_ZFCI_of_leastCof

end PSet
