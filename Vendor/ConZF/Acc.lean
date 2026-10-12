import Vendor.ConZF.Model
/-!
Accessibility of stable membership. The converse to `accHyp_of_mem_wf` uses
an assignment of all finite membership descents. The remaining lemmas give
constructive cases of accessibility; they do not discharge `AccHyp`.
-/
universe u
namespace PSet

/-- One component for every set, followed by arbitrary finite membership descents. -/
private inductive Chain : Path.{u} → PSet.{u} → Prop
  | start (x : PSet.{u}) : Chain [.c x] x
  | step {p x y} : Chain p x → y ∈ x → Chain (.c y :: p) y

private theorem chain_nil {x : PSet.{u}} : ¬ Chain [] x := by
  intro h
  cases h

private theorem chain_head {l p x} (h : Chain (l :: p) x) : l = .c x := by
  cases h <;> rfl

private theorem chain_func {p x y} (hx : Chain p x) (hy : Chain p y) : x = y := by
  cases p with
  | nil => exact (chain_nil hx).elim
  | cons l p =>
    have e := (chain_head hx).symm.trans (chain_head hy)
    cases e
    rfl

private theorem chain_desc : Desc Chain.{u} := by
  intro l p t t' hc hp
  cases hc with
  | start => exact (chain_nil hp).elim
  | step h hy => exact chain_func h hp ▸ hy

/-- Accessibility of the path computes actual membership accessibility of its target. -/
private theorem mem_acc_of_chain {p : Path.{u}} (ha : Acc (Rel Chain) p) :
    ∀ x, Chain p x → Acc (· ∈ ·) x := by
  induction ha with
  | intro p _ ih =>
    intro x hx
    refine Acc.intro x fun y hy => ?_
    have hc := Chain.step hx hy
    exact ih (.c y :: p) ⟨.c y, rfl, y, hc⟩ y hc

private theorem mem_wf_of_chain_root (ha : Acc (Rel Chain.{u}) []) : ∀ x : PSet.{u}, Acc (· ∈ ·) x :=
  fun x => mem_acc_of_chain (ha.inv ⟨.c x, rfl, x, .start x⟩) x (.start x)

/-- The descent hypothesis is exactly uniform double-negated membership accessibility. -/
theorem accHyp_iff_not_not_mem_wf :
    AccHyp.{u} ↔ ¬¬∀ x : PSet.{u}, Acc (· ∈ ·) x :=
  ⟨fun h => nn_map mem_wf_of_chain_root (h Chain chain_desc), accHyp_of_mem_wf⟩

/-- Only double-negated accessibility follows by specializing `AccHyp`. -/
theorem not_not_acc_of_accHyp (h : AccHyp.{u}) (x : PSet.{u}) : ¬¬Acc (· ∈ ·) x :=
  nn_map (fun wf => wf x) (accHyp_iff_not_not_mem_wf.1 h)

/-- The chain of producers: `AccHyp` gives pointwise accessibility, which gives the bounds. -/
theorem pointwiseHGAcc_of_accHyp (h : AccHyp.{u}) : PointwiseHGAcc.{u} :=
  fun x _ => not_not_acc_of_accHyp h x

theorem acc_of_subset {a b : PSet.{u}} (hb : Acc (· ∈ ·) b)
    (h : ∀ y, y ∈ a → y ∈ b) : Acc (· ∈ ·) a :=
  Acc.intro a (fun y hy => hb.inv (h y hy))

theorem acc_empty : Acc (· ∈ ·) empty.{u} :=
  Acc.intro _ (fun y hy => (not_mem_empty y hy).elim)

theorem acc_powerset {a : PSet.{u}} (h : Acc (· ∈ ·) a) : Acc (· ∈ ·) (powerset a) :=
  Acc.intro _ (fun _ hy => acc_of_subset h (mem_powerset.1 hy))

theorem acc_succ {a : PSet.{u}} (ha : Trans a) (h : Acc (· ∈ ·) a) : Acc (· ∈ ·) (succ a) := by
  refine Acc.intro _ fun y hy => acc_of_subset h fun z hz => ?_
  refine Stable.of_nn (mem_succ.1 hy) ?_
  rintro (hy | e)
  · exact ha y hy z hz
  · exact (mem_congr_right e).1 hz

theorem acc_ofNat : ∀ n, Acc (· ∈ ·) (ofNat.{u} n)
  | 0 => acc_empty
  | n+1 => acc_succ (isOrd_ofNat n).trans (acc_ofNat n)

/-- Every negative member of omega is individually not not accessible.
This is not the shift needed to prove accessibility of omega itself. -/
theorem not_not_acc_of_mem_omega {x : PSet.{u}} (hx : x ∈ omega) : ¬¬Acc (· ∈ ·) x :=
  nn_map (fun ⟨n, e⟩ => acc_of_subset (acc_ofNat n)
    (fun _ hy => (mem_congr_right e).1 hy)) (mem_omega.1 hx)

/-- Accessibility transfers along the rank map, because membership strictly decreases rank. -/
theorem acc_of_rank {x : PSet.{u}} (h : Acc (· ∈ ·) (rank x)) : Acc (· ∈ ·) x := by
  generalize he : rank x = r at h
  induction h generalizing x with
  | intro r _ ih =>
    exact Acc.intro x (fun y hy => ih (rank y) (he ▸ rank_mem hy) rfl)

theorem acc_of_finite_rank {x : PSet.{u}} {n : Nat} (h : rank x ∈ ofNat n) : Acc (· ∈ ·) x :=
  acc_of_rank ((acc_ofNat n).inv h)

/-- info: 'PSet.accHyp_iff_not_not_mem_wf' does not depend on any axioms -/
#guard_msgs in #print axioms accHyp_iff_not_not_mem_wf
/-- info: 'PSet.not_not_acc_of_accHyp' does not depend on any axioms -/
#guard_msgs in #print axioms not_not_acc_of_accHyp
/-- info: 'PSet.acc_powerset' does not depend on any axioms -/
#guard_msgs in #print axioms acc_powerset
/-- info: 'PSet.acc_ofNat' does not depend on any axioms -/
#guard_msgs in #print axioms acc_ofNat
/-- info: 'PSet.acc_of_finite_rank' does not depend on any axioms -/
#guard_msgs in #print axioms acc_of_finite_rank
/-- info: 'PSet.not_not_acc_of_mem_omega' does not depend on any axioms -/
#guard_msgs in #print axioms not_not_acc_of_mem_omega
end PSet
