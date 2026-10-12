import Vendor.ConZF.Ord
import Vendor.ConZF.Pair
/-!
Power set, the levels `V_x`, finite ordinals and `ω`, and the label set `D G`: the sets of rank
below `max (rank G, ω) + ω`. `D G` contains `G` and `ω`, is transitive, is monotone in `G`, and
is closed under pairing, which is all that the definability rule and the model need of it.
Those properties are the fields of the class `Budget`; the standard budget `stdD` is its
default instance, and `Seeded.lean` builds another one around a supplied seed.
-/
universe u

namespace PSet

/-- Power set: subsets are indexed by predicates on the index type, which is small because
`Prop` is impredicative. -/
def powerset (X : PSet.{u}) : PSet.{u} :=
  range (ι := X.Idx → Prop) fun S => range (ι := {i // S i}) fun i => X.Func i.1

theorem mem_powerset {X y : PSet.{u}} : y ∈ powerset X ↔ ∀ z, z ∈ y → z ∈ X := by
  constructor
  · intro h z hz
    refine Stable.of_nn h fun ⟨S, e⟩ => ?_
    exact nn_map (fun ⟨⟨i, _⟩, e'⟩ => ⟨i, e'⟩) ((mem_congr_right e).1 hz)
  · intro h
    refine nn_intro ⟨fun i => X.Func i ∈ y, ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
    · exact nn_map (fun ⟨i, e'⟩ => ⟨⟨i, (mem_congr_left e').1 hz⟩, e'⟩) (h z hz)
    · exact Stable.of_nn hz fun ⟨⟨i, hi⟩, e'⟩ => (mem_congr_left e').2 hi

/-- A Kuratowski pair of elements of `A` is in `P²(A)`. -/
theorem pair_mem_powerset_powerset {A a b : PSet.{u}} (ha : a ∈ A) (hb : b ∈ A) :
    pair a b ∈ powerset (powerset A) := by
  refine mem_powerset.2 fun z hz => mem_powerset.2 fun w hw => ?_
  refine Stable.of_nn (mem_upair.1 hz) fun
    | .inl e => ?_
    | .inr e => ?_
  · exact (mem_congr_left (mem_singleton.1 ((mem_congr_right e).1 hw))).2 ha
  · exact Stable.of_nn (mem_upair.1 ((mem_congr_right e).1 hw)) fun
      | .inl e' => (mem_congr_left e').2 ha
      | .inr e' => (mem_congr_left e').2 hb

/-! ### Levels -/

/-- `Vl x` is the set of sets of rank below `rank x`. -/
def Vl : PSet.{u} → PSet.{u}
  | ⟨_, A⟩ => iUnion fun a => powerset (Vl (A a))

theorem mem_Vl : ∀ {x y : PSet.{u}}, y ∈ Vl x ↔ rank y ∈ rank x
  | ⟨_, A⟩, y => by
    refine mem_iUnion.trans <| .trans (nn_congr <| exists_congr fun a => ?_)
      (mem_rank (x := ⟨_, A⟩) (z := rank y)).symm
    refine mem_powerset.trans ⟨fun h => ?_, fun h z hz => ?_⟩
    · exact rank_mem_succ (isOrd_rank _) fun z hz => mem_Vl.1 (h z hz)
    · refine mem_Vl.2 ?_
      have hz' := rank_mem hz
      refine Stable.of_nn (mem_succ.1 h) ?_
      rintro (h | e)
      · exact (isOrd_rank _).trans _ h _ hz'
      · exact (mem_congr_right e).1 hz'

/-- For an ordinal `η`, `V_η` is the set of sets of rank in `η`. -/
theorem mem_Vl_ord {η y : PSet.{u}} (hη : IsOrd η) : y ∈ Vl η ↔ rank y ∈ η :=
  mem_Vl.trans (mem_congr_right hη.rank_equiv)

theorem Vl_congr {x x' : PSet.{u}} (e : x ≈ x') : Vl x ≈ Vl x' :=
  ext fun _ => mem_Vl.trans <| (mem_congr_right (rank_congr e)).trans mem_Vl.symm

theorem Vl_trans {x y z : PSet.{u}} (hy : y ∈ Vl x) (hz : z ∈ y) : z ∈ Vl x :=
  mem_Vl.2 ((isOrd_rank x).trans _ (mem_Vl.1 hy) _ (rank_mem hz))

/-! ### Finite ordinals and `ω` -/

def ofNat : Nat → PSet.{u}
  | 0 => empty
  | n+1 => succ (ofNat n)

theorem isOrd_ofNat : ∀ n, IsOrd (ofNat.{u} n)
  | 0 => isOrd_empty
  | n+1 => (isOrd_ofNat n).succ

def omega : PSet.{u} := range (ι := ULift.{u} Nat) fun n => ofNat n.down

theorem mem_omega {x : PSet.{u}} : x ∈ omega ↔ ¬¬∃ n, x ≈ ofNat n :=
  ⟨nn_map fun ⟨n, e⟩ => ⟨n.down, e⟩, nn_map fun ⟨n, e⟩ => ⟨⟨n⟩, e⟩⟩

theorem ofNat_mem_omega (n : Nat) : ofNat.{u} n ∈ omega := mem_omega.2 (nn_intro ⟨n, .refl _⟩)

theorem mem_ofNat_mem_omega {z : PSet.{u}} : ∀ {n : Nat}, z ∈ ofNat n → z ∈ omega
  | 0, h => (not_mem_empty z h).elim
  | n+1, h => Stable.of_nn (mem_succ.1 h) fun
    | .inl h => mem_ofNat_mem_omega h
    | .inr e => mem_omega.2 (nn_intro ⟨n, e⟩)

theorem isOrd_omega : IsOrd omega.{u} := by
  refine ⟨fun y hy z hz => ?_, fun y hy => ?_⟩
  · exact Stable.of_nn (mem_omega.1 hy) fun ⟨n, e⟩ => mem_ofNat_mem_omega ((mem_congr_right e).1 hz)
  · exact Stable.of_nn (mem_omega.1 hy) fun ⟨n, e⟩ => ((isOrd_ofNat n).resp e.symm).trans

theorem ofNat_inj : ∀ {m n : Nat}, ofNat.{u} m ≈ ofNat n → m = n
  | 0, 0, _ => rfl
  | 0, _+1, h => (not_mem_empty _ ((mem_congr_right h).2 (self_mem_succ _))).elim
  | _+1, 0, h => (not_mem_empty _ ((mem_congr_right h).1 (self_mem_succ _))).elim
  | _+1, _+1, h => congrArg (· + 1) (ofNat_inj (succ_inj h))

/-! ### The label set -/

def succN : Nat → PSet.{u} → PSet.{u}
  | 0, G => G
  | n+1, G => succ (succN n G)

theorem IsOrd.succN {G : PSet.{u}} (h : IsOrd G) : ∀ n, IsOrd (PSet.succN n G)
  | 0 => h
  | n+1 => (h.succN n).succ

theorem succN_congr {G G' : PSet.{u}} (e : G ≈ G') : ∀ n, succN n G ≈ succN n G'
  | 0 => e
  | n+1 => succ_congr (succN_congr e n)

theorem mem_succN_add {G x : PSet.{u}} {n : Nat} (h : x ∈ succN n G) : ∀ k, x ∈ succN (n + k) G
  | 0 => h
  | k+1 => mem_succ_of_mem (mem_succN_add h k)

theorem mem_succN_of_le {G x : PSet.{u}} {m n : Nat} (hmn : m ≤ n) (h : x ∈ succN m G) :
    x ∈ succN n G := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hmn
  exact mem_succN_add h k

/-- The base of `D G`: an ordinal above the ranks of `G` and `ω`. -/
def base (G : PSet.{u}) : PSet.{u} := rank (upair G omega)

theorem isOrd_base (G : PSet.{u}) : IsOrd (base G) := isOrd_rank _

theorem base_congr {G G' : PSet.{u}} (e : G ≈ G') : base G ≈ base G' :=
  rank_congr (upair_congr e (Equiv.refl _))

theorem succN_mono {B B' : PSet.{u}} (hB : IsOrd B) (hB' : IsOrd B')
    (h : ∀ z, z ∈ B → z ∈ B') : ∀ n z, z ∈ succN n B → z ∈ succN n B'
  | 0, z, hz => h z hz
  | n+1, z, hz => Stable.of_nn (mem_succ.1 hz) fun
    | .inl hz => mem_succ_of_mem (succN_mono hB hB' h n z hz)
    | .inr e => (mem_congr_left e).2
        ((hB.succN n).mem_succ_of_subset (hB'.succN n) (succN_mono hB hB' h n))

/-- Ranks are monotone under inclusion of ranks, for the base. -/
theorem base_mono {ν ν' : PSet.{u}} (h : ∀ z, z ∈ rank ν → z ∈ rank ν') :
    ∀ z, z ∈ base ν → z ∈ base ν' := by
  intro z hz
  refine Stable.of_nn (mem_rank'.1 hz) fun ⟨y, hy, hz⟩ => ?_
  refine Stable.of_nn (mem_upair.1 hy) fun
    | .inl e => ?_
    | .inr e => mem_rank'.2 (nn_intro ⟨omega, mem_upair_right _ _,
        (mem_congr_right (succ_congr (rank_congr e))).1 hz⟩)
  refine mem_rank'.2 (nn_intro ⟨ν', mem_upair_left _ _, ?_⟩)
  refine Stable.of_nn (mem_succ.1 ((mem_congr_right (succ_congr (rank_congr e))).1 hz)) fun
    | .inl hz => mem_succ_of_mem (h z hz)
    | .inr e' => (mem_congr_left e').2 ((isOrd_rank ν).mem_succ_of_subset (isOrd_rank ν') h)

theorem rank_mono_of_mem {ν ν' : PSet.{u}} (h : ν ∈ ν') : ∀ z, z ∈ rank ν → z ∈ rank ν' :=
  fun z hz => (isOrd_rank ν').trans _ (rank_mem h) z hz

/-- The standard label set `stdD G = V_{max (rank G, ω) + 1 + ω}`. -/
def stdD (G : PSet.{u}) : PSet.{u} := iUnion (ι := ULift.{u} Nat) fun n => Vl (succN n.down (base G))

theorem mem_stdD {G y : PSet.{u}} : y ∈ stdD G ↔ ¬¬∃ n, rank y ∈ succN n (base G) :=
  mem_iUnion.trans ⟨nn_map fun ⟨n, h⟩ => ⟨n.down, (mem_Vl_ord ((isOrd_base G).succN _)).1 h⟩,
    nn_map fun ⟨n, h⟩ => ⟨⟨n⟩, (mem_Vl_ord ((isOrd_base G).succN _)).2 h⟩⟩

theorem stdD_congr {G G' : PSet.{u}} (e : G ≈ G') : stdD G ≈ stdD G' :=
  ext fun _ => mem_stdD.trans <| .trans (nn_congr <| exists_congr fun n =>
    mem_congr_right (succN_congr (base_congr e) n)) mem_stdD.symm

theorem mem_stdD_of_rank {G y : PSet.{u}} (h : rank y ∈ base G) : y ∈ stdD G :=
  mem_stdD.2 (nn_intro ⟨0, h⟩)

theorem self_mem_stdD (G : PSet.{u}) : G ∈ stdD G := mem_stdD_of_rank (rank_mem (mem_upair_left _ _))

theorem omega_mem_stdD (G : PSet.{u}) : omega ∈ stdD G :=
  mem_stdD_of_rank (rank_mem (mem_upair_right _ _))

theorem stdD_trans {G s x : PSet.{u}} (hs : s ∈ stdD G) (hx : x ∈ s) : x ∈ stdD G :=
  Stable.of_nn (mem_stdD.1 hs) fun ⟨n, h⟩ =>
    mem_stdD.2 (nn_intro ⟨n, ((isOrd_base G).succN n).trans _ h _ (rank_mem hx)⟩)

theorem stdD_mono {ν ν' y : PSet.{u}} (h : ∀ z, z ∈ rank ν → z ∈ rank ν') (hy : y ∈ stdD ν) :
    y ∈ stdD ν' :=
  Stable.of_nn (mem_stdD.1 hy) fun ⟨n, hn⟩ => mem_stdD.2 (nn_intro ⟨n,
    succN_mono (isOrd_base ν) (isOrd_base ν') (base_mono h) n _ hn⟩)

/-- A set whose elements are in `stdD G`, finitely many up to bisimulation, is in `stdD G`. -/
theorem upair_mem_stdD {G a b : PSet.{u}} (ha : a ∈ stdD G) (hb : b ∈ stdD G) :
    upair a b ∈ stdD G := by
  refine Stable.of_nn (mem_stdD.1 ha) fun ⟨m, hm⟩ => Stable.of_nn (mem_stdD.1 hb) fun ⟨n, hn⟩ => ?_
  have hR := (isOrd_base G).succN (m + n)
  refine mem_stdD.2 (nn_intro ⟨m + n + 1, rank_mem_succ hR fun z hz => ?_⟩)
  refine Stable.of_nn (mem_upair.1 hz) ?_
  rintro (e | e)
  · exact (mem_congr_left (rank_congr e)).2 (mem_succN_add hm n)
  · exact (mem_congr_left (rank_congr e)).2 (mem_succN_of_le (Nat.le_add_left n m) hn)

/-- If `rank a ⊆ R` for an ordinal `R`, then `a ∈ stdD R`. -/
theorem mem_stdD_of_subset {R a : PSet.{u}} (hR : IsOrd R) (h : ∀ z, z ∈ rank a → z ∈ R) :
    a ∈ stdD R := by
  have hRb : R ∈ base R := (mem_congr_left hR.rank_equiv).1 (rank_mem (mem_upair_left R omega))
  refine mem_stdD_of_rank (Stable.of_nn ((isOrd_rank a).subset hR h) ?_)
  rintro (h | e)
  · exact (isOrd_base R).trans _ hRb _ h
  · exact (mem_congr_left e).2 hRb

/-! ### Budgets -/

/-- **Budgets.** The properties of the label set used by the definability rule and the model:
extensionality, monotonicity in the source, transitivity, containment of the source and of
`ω`, and closure under unordered pairs. -/
class Budget : Type (u+1) where
  D : PSet.{u} → PSet.{u}
  congr : ∀ {G G' : PSet.{u}}, G ≈ G' → D G ≈ D G'
  mono : ∀ {ν ν' y : PSet.{u}}, ν ∈ ν' → y ∈ D ν → y ∈ D ν'
  trans : ∀ {G s x : PSet.{u}}, s ∈ D G → x ∈ s → x ∈ D G
  self_mem : ∀ G : PSet.{u}, G ∈ D G
  omega_mem : ∀ G : PSet.{u}, omega ∈ D G
  upair_mem : ∀ {G a b : PSet.{u}}, a ∈ D G → b ∈ D G → upair a b ∈ D G
  /-- sets of rank at most an ordinal `R` are in `D R` (the parameter codes of the good-supremum
  argument) -/
  mem_of_subset : ∀ {R a : PSet.{u}}, IsOrd R → (∀ z, z ∈ rank a → z ∈ R) → a ∈ D R

export Budget (D)

/-- The standard budget. -/
instance stdBudget : Budget.{u} where
  D := stdD
  congr := stdD_congr
  mono h := stdD_mono (rank_mono_of_mem h)
  trans := stdD_trans
  self_mem := self_mem_stdD
  omega_mem := omega_mem_stdD
  upair_mem := upair_mem_stdD
  mem_of_subset := mem_stdD_of_subset

section
variable [Budget.{u}]

theorem D_congr {G G' : PSet.{u}} (e : G ≈ G') : D G ≈ D G' := Budget.congr e
theorem D_mono {ν ν' y : PSet.{u}} (h : ν ∈ ν') (hy : y ∈ D ν) : y ∈ D ν' := Budget.mono h hy
theorem D_trans {G s x : PSet.{u}} (hs : s ∈ D G) (hx : x ∈ s) : x ∈ D G := Budget.trans hs hx
theorem self_mem_D (G : PSet.{u}) : G ∈ D G := Budget.self_mem G
theorem omega_mem_D (G : PSet.{u}) : omega ∈ D G := Budget.omega_mem G
theorem upair_mem_D {G a b : PSet.{u}} (ha : a ∈ D G) (hb : b ∈ D G) : upair a b ∈ D G :=
  Budget.upair_mem ha hb
theorem mem_D_of_subset {R a : PSet.{u}} (hR : IsOrd R) (h : ∀ z, z ∈ rank a → z ∈ R) : a ∈ D R :=
  Budget.mem_of_subset hR h

theorem ofNat_mem_D (G : PSet.{u}) (n : Nat) : ofNat n ∈ D G :=
  D_trans (omega_mem_D G) (ofNat_mem_omega n)

theorem empty_mem_D (G : PSet.{u}) : empty ∈ D G := ofNat_mem_D G 0

theorem singleton_mem_D {G a : PSet.{u}} (ha : a ∈ D G) : singleton a ∈ D G :=
  (mem_congr_left (ext fun _ => mem_upair.trans <| .trans
    ⟨fun h => Stable.of_nn h fun h => h.elim id id, fun h => nn_intro (.inl h)⟩
    mem_singleton.symm)).1 (upair_mem_D ha ha)

theorem pair_mem_D {G a b : PSet.{u}} (ha : a ∈ D G) (hb : b ∈ D G) : pair a b ∈ D G :=
  upair_mem_D (singleton_mem_D ha) (upair_mem_D ha hb)

theorem triple_mem_D {G a b c : PSet.{u}} (ha : a ∈ D G) (hb : b ∈ D G) (hc : c ∈ D G) :
    triple a b c ∈ D G :=
  pair_mem_D ha (pair_mem_D hb hc)

end
