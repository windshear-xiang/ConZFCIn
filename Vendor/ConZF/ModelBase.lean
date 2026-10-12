import Vendor.ConZF.Reach
import Vendor.ConZF.ZF
/-!
The definability relation and the class of the model. `ISat η q x y`: `q` codes a formula with
parameters, and `V_η ⊨ φ[x, y, params]`. With this definability relation every successor ordinal
and `ω` are reachable. `HG` is the class of the sets of hereditarily good rank; that it is a model
of `ZF` is proved in `Model.lean`, from the rank bounds of `CofinalCut.lean`.
-/
universe u

namespace PSet
variable [B : Budget.{u}]
open Fml

/-- `k`-tuples, as nested pairs. -/
def tup : Nat → (Nat → PSet.{u}) → PSet.{u}
  | 0, _ => empty
  | k+1, e => pair (e 0) (tup k fun i => e (i+1))

omit [Budget.{u}] in
theorem tup_inj : ∀ {k : Nat} {e e' : Nat → PSet.{u}}, tup k e ≈ tup k e' → ∀ i, i < k → e i ≈ e' i
  | 0, _, _, _, _, h => (Nat.not_lt_zero _ h).elim
  | _+1, _, _, h, 0, _ => (pair_inj h).1
  | _+1, _, _, h, i+1, hi => tup_inj (pair_inj h).2 i (Nat.lt_of_succ_lt_succ hi)

theorem tup_mem_D {G : PSet.{u}} : ∀ {k : Nat} {e : Nat → PSet.{u}}, (∀ i, i < k → e i ∈ D G) →
    tup k e ∈ D G
  | 0, _, _ => empty_mem_D G
  | k+1, _, h => pair_mem_D (h 0 (Nat.succ_pos k))
      (tup_mem_D fun i hi => h (i+1) (Nat.succ_lt_succ hi))

theorem enc_mem_D (G : PSet.{u}) : ∀ φ : Fml, enc φ ∈ D G
  | .mem i j | .eq i j =>
    pair_mem_D (ofNat_mem_D G _) (pair_mem_D (ofNat_mem_D G i) (ofNat_mem_D G j))
  | .fls => pair_mem_D (ofNat_mem_D G _) (empty_mem_D G)
  | .imp φ ψ => pair_mem_D (ofNat_mem_D G _) (pair_mem_D (enc_mem_D G φ) (enc_mem_D G ψ))
  | .all φ => pair_mem_D (ofNat_mem_D G _) (enc_mem_D G φ)

/-- The code of a formula with `k` parameters. -/
def code (φ : Fml) (k : Nat) (e : Nat → PSet.{u}) : PSet.{u} :=
  pair (enc φ) (pair (ofNat k) (tup k e))

theorem code_mem_D {G : PSet.{u}} {φ k e} (h : ∀ i, i < k → e i ∈ D G) : code φ k e ∈ D G :=
  pair_mem_D (enc_mem_D G φ) (pair_mem_D (ofNat_mem_D G k) (tup_mem_D h))

def ISat (η q x y : PSet.{u}) : Prop :=
  ¬¬∃ φ k e, q ≈ code φ k e ∧ Bound (k+2) φ ∧
    x ∈ Vl η ∧ y ∈ Vl η ∧ Sat (· ∈ Vl η) φ (Env.cons x (Env.cons y e))

omit [Budget.{u}] in
theorem ISat_resp {η η' q q' x x' y y' : PSet.{u}} (eη : η ≈ η') (eq : q ≈ q') (ex : x ≈ x')
    (ey : y ≈ y') (h : ISat η q x y) : ISat η' q' x' y' :=
  nn_map (fun ⟨φ, k, e, hq, hb, hx, hy, hs⟩ =>
    have eV := Vl_congr eη
    ⟨φ, k, e, eq.symm.trans hq, hb, (mem_congr_right eV).1 ((mem_congr_left ex).1 hx),
      (mem_congr_right eV).1 ((mem_congr_left ey).1 hy),
      (Sat.resp_iff (fun _ => mem_congr_right eV) φ
        (Env.cons_resp ex (Env.cons_resp ey fun _ => Equiv.refl _))).1 hs⟩) h

omit [Budget.{u}] in
/-- What `ISat` says at a code. -/
theorem isat_code {η x y : PSet.{u}} {ψ : Fml} {m : Nat} {e : Nat → PSet.{u}}
    (hb : Bound (m+2) ψ) : ISat η (code ψ m e) x y ↔
      x ∈ Vl η ∧ y ∈ Vl η ∧ Sat (· ∈ Vl η) ψ (Env.cons x (Env.cons y e)) := by
  constructor
  · intro h
    refine Stable.of_nn h fun ⟨φ, k, e', hq, _, hx, hy, h⟩ => ⟨hx, hy, ?_⟩
    have ⟨e1, e2⟩ := pair_inj hq
    cases enc_inj e1
    have ⟨e3, e4⟩ := pair_inj e2
    cases ofNat_inj e3
    refine (sat_bound hb fun i hi => ?_).2 h
    rcases i with _ | _ | i
    · exact Equiv.refl _
    · exact Equiv.refl _
    · exact tup_inj e4 i (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ hi))
  · exact fun ⟨hx, hy, h⟩ => nn_intro ⟨ψ, m, e, Equiv.refl _, hb, hx, hy, h⟩

/-- Reachability from a formula: the form in which it is proved. -/
theorem reachable_of {η ν s : PSet.{u}} {ψ : Fml} {m : Nat} {e : Nat → PSet.{u}}
    (hb : Bound (m+2) ψ) (hν : ν ∈ η) (he : ∀ i, i < m → e i ∈ D ν) (hs : s ∈ D ν)
    (func : ∀ x y y', x ∈ s → y ∈ Vl η → y' ∈ Vl η →
      Sat (· ∈ Vl η) ψ (Env.cons x (Env.cons y e)) →
      Sat (· ∈ Vl η) ψ (Env.cons x (Env.cons y' e)) → y ≈ y')
    (cover : ∀ ζ, ζ ∈ η → ¬¬∃ x y, x ∈ s ∧ x ∈ Vl η ∧ y ∈ Vl η ∧
      Sat (· ∈ Vl η) ψ (Env.cons x (Env.cons y e)) ∧ ζ ∈ succ (rank y))
    (hη : IsOrd η) : Reachable ISat η := by
  refine nn_intro ⟨ν, hν, nn_intro ⟨code ψ m e, s, code_mem_D he, hs, ?_, ?_, ?_⟩⟩
  · intro x y y' hx h1 h2
    have ⟨_, hy, s1⟩ := (isat_code hb).1 h1
    have ⟨_, hy', s2⟩ := (isat_code hb).1 h2
    exact func x y y' hx hy hy' s1 s2
  · exact fun x y _ h1 => (mem_Vl_ord hη).1 ((isat_code hb).1 h1).2.1
  · exact fun ζ hζ => nn_map (fun ⟨x, y, hx, hxV, hy, h, hζ⟩ =>
      ⟨x, y, hx, (isat_code hb).2 ⟨hxV, hy, h⟩, hζ⟩) (cover ζ hζ)

/-- A successor is reached from its predecessor, by a constant function. -/
theorem reachable_succ {ζ : PSet.{u}} (hζ : IsOrd ζ) : Reachable ISat (succ ζ) := by
  have hζV : ζ ∈ Vl (succ ζ) :=
    (mem_Vl_ord hζ.succ).2 ((mem_congr_left hζ.rank_equiv).2 (self_mem_succ ζ))
  have h0V : empty ∈ Vl (succ ζ) := (mem_Vl_ord hζ.succ).2 <|
    (isOrd_rank _).mem_succ_of_subset hζ fun z hz =>
      (not_mem_empty z ((mem_congr_right isOrd_empty.rank_equiv).1 hz)).elim
  refine reachable_of (ψ := .eq 1 2) (m := 1) (e := fun _ => ζ) (s := singleton empty)
    ⟨by decide, by decide⟩ (self_mem_succ ζ) (fun _ _ => self_mem_D ζ)
    (singleton_mem_D (empty_mem_D ζ)) (fun x y y' _ _ _ h1 h2 => h1.trans h2.symm)
    (fun ζ' hζ' => nn_intro ⟨empty, ζ, self_mem_singleton _, h0V, hζV, Equiv.refl ζ, ?_⟩) hζ.succ
  exact (mem_congr_right (succ_congr hζ.rank_equiv)).2 hζ'

/-- `ω` is reached from `0`, by the identity on `ω`. -/
theorem reachable_omega : Reachable ISat omega.{u} := by
  have hV : ∀ {x : PSet.{u}}, x ∈ omega → x ∈ Vl omega := fun hx =>
    (mem_Vl_ord isOrd_omega).2 ((mem_congr_left (isOrd_omega.mem hx).rank_equiv).2 hx)
  refine reachable_of (ψ := .eq 0 1) (m := 0) (e := fun _ => empty) (s := omega)
    ⟨by decide, by decide⟩ (ofNat_mem_omega 0) (fun _ h => (Nat.not_lt_zero _ h).elim)
    (omega_mem_D _) (fun x y y' _ _ _ h1 h2 => h1.symm.trans h2)
    (fun ζ hζ => nn_intro ⟨ζ, ζ, hζ, hV hζ, hV hζ, Equiv.refl ζ, ?_⟩) isOrd_omega
  exact mem_succ_of_equiv (isOrd_omega.mem hζ).rank_equiv.symm

/-! ### Closure of the hereditarily good ordinals -/

theorem good_empty : Good ISat empty.{u} := fun ζ hζ => (not_mem_empty ζ hζ).elim

theorem Cls.succ {η : PSet.{u}} (h : Cls ISat η) : Cls ISat (succ η) :=
  ⟨h.1.succ, fun _ hμ => Stable.of_nn (mem_succ.1 hμ) fun
    | .inl hμ => h.2 _ hμ
    | .inr e => fun _ _ => (reachable_succ h.1).resp ISat_resp e.symm⟩

theorem cls_empty : Cls ISat empty.{u} :=
  ⟨isOrd_empty, fun _ hμ => Stable.of_nn (mem_succ.1 hμ) fun
    | .inl h => (not_mem_empty _ h).elim
    | .inr e => good_empty.resp ISat_resp e.symm⟩

theorem cls_ofNat : ∀ n, Cls ISat (ofNat.{u} n)
  | 0 => cls_empty
  | n+1 => (cls_ofNat n).succ

theorem cls_omega : Cls ISat omega.{u} :=
  ⟨isOrd_omega, fun _ hμ => Stable.of_nn (mem_succ.1 hμ) fun
    | .inl h => Stable.of_nn (mem_omega.1 h) fun ⟨n, e⟩ => ((cls_ofNat n).good).resp ISat_resp e.symm
    | .inr e => fun _ _ => reachable_omega.resp ISat_resp e.symm⟩

/-! ### The model -/

/-- The sets of hereditarily good rank. -/
def HG (x : PSet.{u}) : Prop := Cls ISat (rank x)

instance {x : PSet.{u}} : Stable (HG x) := inferInstanceAs (Stable (Cls ISat _))

theorem HG.of_bound {y R : PSet.{u}} (hR : Cls ISat R) (h : ∀ z, z ∈ y → rank z ∈ R) : HG y :=
  hR.succ.mem (rank_mem_succ hR.1 h)

theorem HG.mem {x z : PSet.{u}} (hx : HG x) (hz : z ∈ x) : HG z := Cls.mem hx (rank_mem hz)

theorem HG.resp {x x' : PSet.{u}} (e : x ≈ x') (hx : HG x) : HG x' := Cls.resp (rank_congr e) hx

/-- `HG` is closed under pairs: compare the two ranks. -/
theorem HG.upair {x y : PSet.{u}} (hx : HG x) (hy : HG y) : HG (PSet.upair x y) := by
  have key : ∀ {x y : PSet.{u}}, HG x → (∀ z, z ∈ rank y → z ∈ rank x) → HG (PSet.upair x y) :=
    fun {x y} hx hsub => HG.of_bound (Cls.succ hx) fun z hz => Stable.of_nn (mem_upair.1 hz) fun
      | .inl e => mem_succ_of_equiv (rank_congr e)
      | .inr e => (mem_congr_left (rank_congr e)).2
          ((isOrd_rank y).mem_succ_of_subset hx.1 hsub)
  refine Stable.of_nn ((isOrd_rank x).trichotomy (isOrd_rank y)) ?_
  rintro (h | h | h)
  · exact Cls.resp (rank_congr (ext fun z => mem_upair.trans
      ((nn_congr Or.comm).trans mem_upair.symm)))
      (key hy fun z hz => (isOrd_rank y).trans _ h z hz)
  · exact key hx fun z hz => (mem_congr_right h).2 hz
  · exact key hx fun z hz => (isOrd_rank x).trans _ h z hz

theorem HG.singleton {x : PSet.{u}} (hx : HG x) : HG (PSet.singleton x) :=
  HG.of_bound (Cls.succ hx) fun _ hz => mem_succ_of_equiv (rank_congr (mem_singleton.1 hz))

theorem HG.pair {x y : PSet.{u}} (hx : HG x) (hy : HG y) : HG (PSet.pair x y) :=
  HG.upair hx.singleton (HG.upair hx hy)

theorem HG.rank {x : PSet.{u}} (hx : HG x) : HG (PSet.rank x) :=
  Cls.resp (isOrd_rank x).rank_equiv.symm hx

omit [Budget.{u}] in
/-- Finitely many elements of an ordinal are included in one of its elements. -/
theorem exists_upper {θ : PSet.{u}} (hθ : IsOrd θ) {R : PSet.{u}} (hR : R ∈ θ) :
    ∀ (k : Nat) (r : Nat → PSet.{u}), (∀ i, i < k → r i ∈ θ) →
      ¬¬∃ R', R' ∈ θ ∧ (∀ z, z ∈ R → z ∈ R') ∧ ∀ i, i < k → ∀ z, z ∈ r i → z ∈ R'
  | 0, _, _ => nn_intro ⟨R, hR, fun _ h => h, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | k+1, r, hr => by
    refine nn_bind (exists_upper hθ hR k r fun i hi => hr i (Nat.lt_succ_of_lt hi))
      fun ⟨R', hR', h1, h2⟩ => ?_
    have hk := hr k (Nat.lt_succ_self k)
    refine nn_map ?_ ((hθ.mem hR').trichotomy (hθ.mem hk))
    have last : ∀ {R'' : PSet.{u}}, (∀ z, z ∈ R' → z ∈ R'') → (∀ z, z ∈ r k → z ∈ R'') →
        R'' ∈ θ → ∃ R', R' ∈ θ ∧ (∀ z, z ∈ R → z ∈ R') ∧ ∀ i, i < k + 1 → ∀ z, z ∈ r i → z ∈ R' :=
      fun {R''} a b c => ⟨R'', c, fun z hz => a z (h1 z hz), fun i hi z hz => by
        rcases Nat.lt_or_ge i k with hi' | hi'
        · exact a z (h2 i hi' z hz)
        · cases Nat.le_antisymm (Nat.le_of_lt_succ hi) hi'; exact b z hz⟩
    rintro (h | h | h)
    · exact last (fun z hz => (hθ.mem hk).trans _ h z hz) (fun _ hz => hz) hk
    · exact last (fun z hz => (mem_congr_right h).1 hz) (fun _ hz => hz) hk
    · exact last (fun _ hz => hz) (fun z hz => (hθ.mem hR').trans _ h z hz) hR'

end PSet
