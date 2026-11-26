import GradientHessian.GeometricDirectionSlots
import GradientHessian.ComparisonControllerReplay

/-! Isolating an actual center or memory factor changes only the tests that
read that raw direction. The normal numerical operation is unchanged for
every state; no good-event or unit-norm hypothesis is needed. -/

noncomputable section
namespace GradientHessian.GeometricRepair
open Classical RawDirection RawHierarchy HigherHierarchy HierarchyAddresses
  ComparisonController ComparisonControllerReplay

def blockDirection {J t : ℕ} (target : Slot J t) (a : Action t (4096*J^2)) : Bool :=
  decide (directionSlot a=some target)

def AgreeOff {L M ell : ℕ} {X A : Type*} (R S : Rules L M ell X A) (blocked : A → Bool) : Prop :=
  (∀ s Z a,blocked a=false → R.trigger s Z a=S.trigger s Z a) ∧
    ∀ s Z,R.hit s Z=S.hit s Z

theorem agreeOff_guardedRun {L M ell : ℕ} {X A : Type*} (R S : Rules L M ell X A)
    (blocked : A → Bool) (hp : R.priority=S.priority) (ht : R.target=S.target)
    (he : AgreeOff R S blocked) (stop : TaskState.State L M ell → Bool)
    (fuel : ℕ) (q : Phase L M ell X A) :
    guardedRun (suppress R blocked) stop fuel q=guardedRun (suppress S blocked) stop fuel q :=
  suppressed_guardedRun_congr R S blocked stop hp ht (fun s _ Z a ha => he.1 s Z a ha)
    (fun s _ Z => he.2 s Z) fuel q

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

theorem leaf_a_eq_of_numerical (t : ℕ) (x y : Raw d n r J E H t)
    (he : ∀ q,RawLeafFactor.leafNumerical t x q=RawLeafFactor.leafNumerical t y q) :
    ∀ q j,(leafData t (assemble P B fallback t x) q).a j=(leafData t (assemble P B fallback t y) q).a j := by
  intro q j
  rw [RawLeafFactor.leaf_a_assemble,RawLeafFactor.leaf_a_assemble,he]

theorem slot_rule_erasure (K : ℝ) (t : ℕ) (x y : Raw d n r J E H t) (target : Slot J t)
    (he : Except t target x y)
    (ha : ∀ q j,(leafData t (assemble P B fallback t x) q).a j=(leafData t (assemble P B fallback t y) q).a j) :
    AgreeOff (rules (ell := ell) K (assemble P B fallback t x))
      (rules K (assemble P B fallback t y)) (blockDirection target) := by
  refine ⟨?_,?_⟩
  · intro s Z a hb
    exact trigger_eq_of_slot P B fallback K t x y target he ha s Z a (of_decide_eq_false hb)
  · exact hit_eq_of_leaf_a P B fallback t x y ha

variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]

theorem center_rule_erasure (K : ℝ) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2) :
    AgreeOff (rules (ell := ell) K (assemble P B fallback (h+1+depth) x))
      (rules K (assemble P B fallback (h+1+depth) y))
      (blockDirection (embed (h+1) depth w (.inr i))) :=
  slot_rule_erasure P B fallback K (h+1+depth) x y _ (center_factor_except h depth w i x y he)
    (fun q j => congrArg (fun a => a.a j) (RawCenterLocality.rest_eq_all_leafData P B fallback h depth w i x y he q))

theorem old_rule_erasure (K : ℝ) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2) :
    AgreeOff (rules (ell := ell) K (assemble P B fallback (0+depth) x))
      (rules K (assemble P B fallback (0+depth) y))
      (blockDirection (embed 0 depth w (.inl (i,j)))) :=
  slot_rule_erasure P B fallback K (0+depth) x y _ (old_factor_except depth w i j x y he)
    (leaf_a_eq_of_numerical P B fallback _ x y (RawMemoryGlobalLocality.old_all_numerical depth w i j x y he))

theorem inner_rule_erasure (K : ℝ) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2) :
    AgreeOff (rules (ell := ell) K (assemble P B fallback (0+depth) x))
      (rules K (assemble P B fallback (0+depth) y))
      (blockDirection (embed 0 depth w (.inr (i,j,k)))) :=
  slot_rule_erasure P B fallback K (0+depth) x y _ (inner_factor_except depth w i j k x y he)
    (leaf_a_eq_of_numerical P B fallback _ x y (RawMemoryGlobalLocality.inner_all_numerical depth w i j k x y he))

theorem center_guarded_replay_eq (K : ℝ) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (stop : TaskState.State (h+1+depth+1) (4096*J^2+1) ell → Bool) (fuel : ℕ)
    (q : Phase (h+1+depth+1) (4096*J^2+1) ell
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (h+1+depth)) (Action (h+1+depth) (4096*J^2))) :
    guardedRun (suppress (rules K (assemble P B fallback (h+1+depth) x))
      (blockDirection (embed (h+1) depth w (.inr i)))) stop fuel q=
    guardedRun (suppress (rules K (assemble P B fallback (h+1+depth) y))
      (blockDirection (embed (h+1) depth w (.inr i)))) stop fuel q :=
  agreeOff_guardedRun (rules K (assemble P B fallback (h+1+depth) x))
    (rules K (assemble P B fallback (h+1+depth) y)) _ rfl rfl
    (center_rule_erasure P B fallback K h depth w i x y he) stop fuel q

theorem old_guarded_replay_eq (K : ℝ) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (stop : TaskState.State (0+depth+1) (4096*J^2+1) ell → Bool) (fuel : ℕ)
    (q : Phase (0+depth+1) (4096*J^2+1) ell
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (0+depth)) (Action (0+depth) (4096*J^2))) :
    guardedRun (suppress (rules K (assemble P B fallback (0+depth) x))
      (blockDirection (embed 0 depth w (.inl (i,j))))) stop fuel q=
    guardedRun (suppress (rules K (assemble P B fallback (0+depth) y))
      (blockDirection (embed 0 depth w (.inl (i,j))))) stop fuel q :=
  agreeOff_guardedRun (rules K (assemble P B fallback (0+depth) x))
    (rules K (assemble P B fallback (0+depth) y)) _ rfl rfl
    (old_rule_erasure P B fallback K depth w i j x y he) stop fuel q

theorem inner_guarded_replay_eq (K : ℝ) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (stop : TaskState.State (0+depth+1) (4096*J^2+1) ell → Bool) (fuel : ℕ)
    (q : Phase (0+depth+1) (4096*J^2+1) ell
      (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) (0+depth)) (Action (0+depth) (4096*J^2))) :
    guardedRun (suppress (rules K (assemble P B fallback (0+depth) x))
      (blockDirection (embed 0 depth w (.inr (i,j,k))))) stop fuel q=
    guardedRun (suppress (rules K (assemble P B fallback (0+depth) y))
      (blockDirection (embed 0 depth w (.inr (i,j,k))))) stop fuel q :=
  agreeOff_guardedRun (rules K (assemble P B fallback (0+depth) x))
    (rules K (assemble P B fallback (0+depth) y)) _ rfl rfl
    (inner_rule_erasure P B fallback K depth w i j k x y he) stop fuel q

end GradientHessian.GeometricRepair
