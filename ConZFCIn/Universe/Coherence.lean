import ConZFCIn.Universe.Embedding

/-! Composition of structural lifts and comparison of lower-universe heights.
The heights of successive lower universes strictly increase in a common upper universe. -/
universe u v w

namespace PSet.Multi

theorem lift_lift : ∀ x : PSet.{u},
    lift.{max (u+1) v,w} (lift.{u,v} x) ≈
      lift.{u,max (max (u+1) v + 1) w} x
  | ⟨_, A⟩ =>
    ⟨fun a => nn_intro ⟨⟨a.down.down⟩, lift_lift (A a.down.down)⟩,
     fun a => nn_intro ⟨⟨⟨a.down⟩⟩, lift_lift (A a.down)⟩⟩

theorem lift_U : lift.{max (u+1) v,w} U.{u,v} ≈
    U.{u,max (max (u+1) v + 1) w} := by
  refine ext fun z => mem_lift.trans (.trans ?_ mem_U.symm)
  constructor
  · intro h
    exact nn_bind h fun ⟨y, hy, e⟩ => nn_map
      (fun ⟨a, ea⟩ => ⟨a, e.trans ((lift_congr ea).trans (lift_lift a))⟩)
      (mem_U.1 hy)
  · intro h
    exact nn_map (fun ⟨a, e⟩ => ⟨lift.{u,v} a, lift_mem_U a,
      e.trans (lift_lift a).symm⟩) h

theorem lift_K : lift.{max (u+1) v,w} K.{u,v} ≈
    K.{u,max (max (u+1) v + 1) w} :=
  (rank_lift U.{u,v}).symm.trans (rank_congr lift_U)

/-- The heights of adjacent lower universes strictly increase in any common higher universe. -/
theorem height_strict : K.{u,max (u+2) w} ∈ K.{u+1,w} :=
  (mem_congr_left lift_K.{u,0,w}).1
    (lift_mem_K.{u+1,w} isOrd_K.{u,0})

#print axioms lift_lift
#print axioms height_strict

end PSet.Multi
