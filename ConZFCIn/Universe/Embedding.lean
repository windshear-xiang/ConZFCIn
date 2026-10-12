import Vendor.ConZF.VLevel
/-! Generalizes `ConZF/Lift.lean` from the pinned upstream revision to an arbitrary
common upper universe. New universe instances are checked by Lean. -/
/-!
The generalized universe interface, based on con22 §1.
The structural lift `lift : PSet.{u} → PSet.{max (u+1) v}`
preserves and reflects bisimulation and membership; every member of a lift is a lift
(`mem_lift`); the lift commutes with unions, successor, powerset (`lift_powerset`), rank
(`rank_lift`), and the levels (`lift_Vl`), and preserves and reflects ordinals. An upper subset
of a lifted lower set has a lower representative by Separation on the lower carrier
(`shrink`, `lift_shrink`); the upper parameter occurs only in the separating proposition.

The upper set `U` of all lifts is transitive; its rank `K` is the height of the lower universe:
the members of `K` are exactly the upper ordinals with lower representatives (`mem_K`), and
`U` is the level `V_K` of the upper universe (`mem_U_iff_rank`). `K` has no lower
representative (`K_not_lift`).
-/
universe u v

namespace PSet.Multi

/-- The structural lift into a common higher universe. -/
def lift : PSet.{u} → PSet.{max (u+1) v}
  | ⟨_, A⟩ => ⟨ULift.{max (u+1) v} _, fun a => lift (A a.down)⟩

theorem lift_equiv : ∀ {x y : PSet.{u}}, lift x ≈ lift y ↔ x ≈ y
  | ⟨_, A⟩, ⟨_, B⟩ => by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun a => nn_map (fun ⟨b, e⟩ => ⟨b.down, lift_equiv.1 e⟩) (h1 ⟨a⟩),
             fun b => nn_map (fun ⟨a, e⟩ => ⟨a.down, lift_equiv.1 e⟩) (h2 ⟨b⟩)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun a => nn_map (fun ⟨b, e⟩ => ⟨⟨b⟩, lift_equiv.2 e⟩) (h1 a.down),
             fun b => nn_map (fun ⟨a, e⟩ => ⟨⟨a⟩, lift_equiv.2 e⟩) (h2 b.down)⟩

theorem lift_congr {x y : PSet.{u}} (e : x ≈ y) : lift x ≈ lift y := lift_equiv.2 e

/-- Every member of a lift is the lift of a member. -/
theorem mem_lift : ∀ {x : PSet.{u}} {w : PSet.{max (u+1) v}}, w ∈ lift x ↔ ¬¬∃ z, z ∈ x ∧ w ≈ lift z
  | ⟨_, A⟩, _ =>
    ⟨nn_map fun ⟨b, e⟩ => ⟨A b.down, func_mem ⟨_, A⟩ b.down, e⟩,
     fun h => nn_bind h fun ⟨_, hz, e⟩ => nn_map (fun ⟨a, e'⟩ => ⟨⟨a⟩, e.trans (lift_congr e')⟩) hz⟩

theorem lift_mem {z x : PSet.{u}} : lift z ∈ lift x ↔ z ∈ x :=
  ⟨fun h => Stable.of_nn (mem_lift.1 h) fun ⟨_, hz', e⟩ => (mem_congr_left (lift_equiv.1 e)).2 hz',
   fun h => mem_lift.2 (nn_map (fun ⟨b, e⟩ => ⟨x.Func b, func_mem x b, lift_congr e⟩) h)⟩

theorem lift_mem_of_mem {z x : PSet.{u}} (h : z ∈ x) : lift z ∈ lift x := lift_mem.2 h

/-! ### Commutation with the operations -/

theorem mem_lift_iUnion {ι : Type u} {A : ι → PSet.{u}} {w : PSet.{max (u+1) v}} :
    w ∈ lift (iUnion A) ↔ ¬¬∃ i, w ∈ lift (A i) :=
  mem_lift.trans ⟨fun h => nn_bind h fun ⟨z, hz, e⟩ => nn_map (fun ⟨i, hz⟩ =>
      ⟨i, mem_lift.2 (nn_intro ⟨z, hz, e⟩)⟩) (mem_iUnion.1 hz),
    fun h => nn_bind h fun ⟨i, hw⟩ => nn_map (fun ⟨z, hz, e⟩ =>
      ⟨z, mem_iUnion.2 (nn_intro ⟨i, hz⟩), e⟩) (mem_lift.1 hw)⟩

theorem mem_lift_succ {x : PSet.{u}} {w : PSet.{max (u+1) v}} :
    w ∈ lift (succ x) ↔ ¬¬(w ∈ lift x ∨ w ≈ lift x) :=
  mem_lift.trans ⟨fun h => nn_bind h fun ⟨z, hz, e⟩ => nn_map (fun
      | .inl hz => .inl (mem_lift.2 (nn_intro ⟨z, hz, e⟩))
      | .inr e' => .inr (e.trans (lift_congr e'))) (mem_succ.1 hz),
    fun h => nn_bind h fun
      | .inl hw => nn_map (fun ⟨z, hz, e⟩ => ⟨z, mem_succ_of_mem hz, e⟩) (mem_lift.1 hw)
      | .inr e => nn_intro ⟨x, self_mem_succ x, e⟩⟩

theorem lift_succ (x : PSet.{u}) : lift (succ x) ≈ succ (lift x) :=
  ext fun _ => mem_lift_succ.trans mem_succ.symm

theorem lift_empty : lift empty.{u} ≈ empty :=
  ext fun w => ⟨fun h => Stable.of_nn (mem_lift.1 h) fun ⟨z, hz, _⟩ => (not_mem_empty z hz).elim,
    fun h => (not_mem_empty w h).elim⟩

theorem lift_ofNat : ∀ n, lift (ofNat.{u} n) ≈ ofNat n
  | 0 => lift_empty
  | n+1 => (lift_succ _).trans (succ_congr (lift_ofNat n))

theorem lift_omega : lift omega.{u} ≈ omega := by
  refine ext fun w => ⟨fun h => ?_, fun h => ?_⟩
  · refine Stable.of_nn (mem_lift.1 h) fun ⟨z, hz, e⟩ => ?_
    exact Stable.of_nn (mem_omega.1 hz) fun ⟨n, e'⟩ =>
      mem_omega.2 (nn_intro ⟨n, e.trans ((lift_congr e').trans (lift_ofNat n))⟩)
  · exact Stable.of_nn (mem_omega.1 h) fun ⟨n, e⟩ =>
      mem_lift.2 (nn_intro ⟨ofNat n, ofNat_mem_omega n, e.trans (lift_ofNat n).symm⟩)

/-- The lower representative of an upper subset of a lifted lower set. -/
def shrink (a : PSet.{u}) (Y : PSet.{max (u+1) v}) : PSet.{u} := sep (fun z => lift z ∈ Y) a

theorem mem_shrink {a : PSet.{u}} {Y : PSet.{max (u+1) v}} {z : PSet.{u}} :
    z ∈ shrink a Y ↔ z ∈ a ∧ lift z ∈ Y :=
  mem_sep fun _ _ e h => (mem_congr_left (lift_congr e)).1 h

/-- **Shrinking.** The lift of the lower representative is the upper subset. -/
theorem lift_shrink {a : PSet.{u}} {Y : PSet.{max (u+1) v}} (h : ∀ w, w ∈ Y → w ∈ lift a) :
    lift (shrink a Y) ≈ Y := by
  refine ext fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · exact Stable.of_nn (mem_lift.1 hw) fun ⟨z, hz, e⟩ => (mem_congr_left e).2 (mem_shrink.1 hz).2
  · exact Stable.of_nn (mem_lift.1 (h w hw)) fun ⟨z, hz, e⟩ =>
      mem_lift.2 (nn_intro ⟨z, mem_shrink.2 ⟨hz, (mem_congr_left e).1 hw⟩, e⟩)

theorem powerset_congr {a a' : PSet.{u}} (e : a ≈ a') : powerset a ≈ powerset a' :=
  ext fun _ => mem_powerset.trans ((forall_congr' fun _ => imp_congr_right fun _ =>
    mem_congr_right e).trans mem_powerset.symm)

/-- The lift of a powerset is the powerset of the lift. -/
theorem lift_powerset (a : PSet.{u}) : lift (powerset a) ≈ powerset (lift a) := by
  refine ext fun w => ⟨fun hw => mem_powerset.2 fun z hz => ?_, fun hw => ?_⟩
  · refine Stable.of_nn (mem_lift.1 hw) fun ⟨y, hy, e⟩ => ?_
    refine Stable.of_nn (mem_lift.1 ((mem_congr_right e).1 hz)) fun ⟨z', hz', e'⟩ => ?_
    exact mem_lift.2 (nn_intro ⟨z', mem_powerset.1 hy z' hz', e'⟩)
  · refine mem_lift.2 (nn_intro ⟨shrink a w, mem_powerset.2 fun z hz => (mem_shrink.1 hz).1, ?_⟩)
    exact (lift_shrink (mem_powerset.1 hw)).symm

theorem rank_lift : ∀ x : PSet.{u}, rank (lift x) ≈ lift (rank x)
  | ⟨_, A⟩ => by
    refine ext fun w => (mem_rank (x := lift ⟨_, A⟩)).trans (.trans ?_ mem_lift_iUnion.symm)
    refine nn_congr ⟨fun ⟨a, h⟩ => ⟨a.down, ?_⟩, fun ⟨a, h⟩ => ⟨⟨a⟩, ?_⟩⟩
    · exact (mem_congr_right (lift_succ _)).2
        ((mem_congr_right (succ_congr (rank_lift (A a.down)))).1 h)
    · exact (mem_congr_right (succ_congr (rank_lift (A a)))).2
        ((mem_congr_right (lift_succ _)).1 h)

theorem lift_Vl : ∀ x : PSet.{u}, lift (Vl x) ≈ Vl (lift x)
  | ⟨_, A⟩ => by
    refine ext fun w => (mem_lift_iUnion (A := fun a => powerset (Vl (A a)))).trans
      (.trans ?_ (mem_iUnion (A := fun a : ULift _ => powerset (Vl (lift (A a.down))))).symm)
    refine nn_congr ⟨fun ⟨a, h⟩ => ⟨⟨a⟩, ?_⟩, fun ⟨a, h⟩ => ⟨a.down, ?_⟩⟩
    · exact (mem_congr_right ((lift_powerset _).trans (powerset_congr (lift_Vl (A a))))).1 h
    · exact (mem_congr_right ((lift_powerset _).trans (powerset_congr (lift_Vl (A a.down))))).2 h

theorem trans_lift {x : PSet.{u}} (h : Trans x) : Trans (lift x) := fun _ hy _ hz =>
  Stable.of_nn (mem_lift.1 hy) fun ⟨y', hy', e⟩ =>
    Stable.of_nn (mem_lift.1 ((mem_congr_right e).1 hz)) fun ⟨z', hz', e'⟩ =>
      mem_lift.2 (nn_intro ⟨z', h y' hy' z' hz', e'⟩)

theorem trans_of_lift {x : PSet.{u}} (h : Trans (lift x)) : Trans x := fun _ hy _ hz =>
  lift_mem.1 (h _ (lift_mem_of_mem hy) _ (lift_mem_of_mem hz))

theorem isOrd_lift {x : PSet.{u}} (h : IsOrd x) : IsOrd (lift x) :=
  ⟨trans_lift h.trans, fun _ hy => Stable.of_nn (mem_lift.1 hy) fun ⟨y', hy', e⟩ =>
    (trans_lift (h.mem_trans y' hy')).resp e.symm⟩

theorem isOrd_of_lift {x : PSet.{u}} (h : IsOrd (lift x)) : IsOrd x :=
  ⟨trans_of_lift h.trans, fun _ hy => trans_of_lift (h.mem_trans _ (lift_mem_of_mem hy))⟩

theorem lift_isOrd_iff {x : PSet.{u}} : IsOrd (lift x) ↔ IsOrd x := ⟨isOrd_of_lift, isOrd_lift⟩

/-! ### The lower universe as an upper set, and its height -/

/-- The upper set of all lifts of lower sets. -/
def U : PSet.{max (u+1) v} := range (ι := ULift.{max (u+1) v} PSet.{u}) fun z => lift z.down

theorem mem_U {x : PSet.{max (u+1) v}} : x ∈ U.{u,v} ↔ ¬¬∃ z : PSet.{u}, x ≈ lift z :=
  nn_congr ⟨fun ⟨z, e⟩ => ⟨z.down, e⟩, fun ⟨z, e⟩ => ⟨⟨z⟩, e⟩⟩

theorem lift_mem_U (z : PSet.{u}) : lift z ∈ U.{u,v} := mem_U.2 (nn_intro ⟨z, Equiv.refl _⟩)

theorem U_trans : Trans U.{u,v} := fun _ hy _ hz =>
  Stable.of_nn (mem_U.1 hy) fun ⟨_, e⟩ =>
    Stable.of_nn (mem_lift.1 ((mem_congr_right e).1 hz)) fun ⟨z', _, e'⟩ => mem_U.2 (nn_intro ⟨z', e'⟩)

/-- The height of the lower universe. -/
def K : PSet.{max (u+1) v} := rank U.{u,v}

theorem isOrd_K : IsOrd K.{u,v} := isOrd_rank _

theorem lift_mem_K {η : PSet.{u}} (hη : IsOrd η) : lift η ∈ K.{u,v} :=
  (mem_congr_left ((rank_lift η).trans (lift_congr hη.rank_equiv))).1 (rank_mem (lift_mem_U η))

/-- **The members of `K`** are the upper ordinals with lower representatives. -/
theorem mem_K {α : PSet.{max (u+1) v}} : α ∈ K.{u,v} ↔ ¬¬∃ η : PSet.{u}, IsOrd η ∧ α ≈ lift η := by
  constructor
  · intro h
    refine nn_bind (mem_rank'.1 h) fun ⟨y, hy, hα⟩ => nn_bind (mem_U.1 hy) fun ⟨z, e⟩ => ?_
    have hα' : α ∈ lift (succ (rank z)) :=
      (mem_congr_right ((succ_congr ((rank_congr e).trans (rank_lift z))).trans (lift_succ _).symm)).1 hα
    exact nn_map (fun ⟨η, hη, e'⟩ => ⟨η, (isOrd_rank z).succ.mem hη, e'⟩) (mem_lift.1 hα')
  · exact fun h => Stable.of_nn h fun ⟨η, hη, e⟩ => (mem_congr_left e).2 (lift_mem_K hη)

/-- **`U = V_K`**: the upper sets of rank below `K` are exactly the lifts. -/
theorem mem_U_iff_rank {x : PSet.{max (u+1) v}} : x ∈ U.{u,v} ↔ rank x ∈ K.{u,v} := by
  refine ⟨rank_mem, fun h => ?_⟩
  refine Stable.of_nn (mem_K.1 h) fun ⟨η, hη, e⟩ => ?_
  have hx : x ∈ Vl (lift (succ η)) := by
    refine mem_Vl.2 ((mem_congr_right ((rank_lift _).trans (lift_congr hη.succ.rank_equiv))).2 ?_)
    exact (mem_congr_right (lift_succ η)).2 (mem_succ_of_equiv e)
  exact Stable.of_nn (mem_lift.1 ((mem_congr_right (lift_Vl _).symm).1 hx))
    fun ⟨z, _, e'⟩ => mem_U.2 (nn_intro ⟨z, e'⟩)

/-- `K` has no lower representative. -/
theorem K_not_lift : ¬ ∃ z : PSet.{u}, K.{u,v} ≈ lift z := fun ⟨_, e⟩ =>
  not_mem_self K.{u,v} ((mem_congr_left isOrd_K.rank_equiv).1 (rank_mem (mem_U.2 (nn_intro ⟨_, e⟩))))

end PSet.Multi
