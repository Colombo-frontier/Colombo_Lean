import GradientHessian.DirectionPolicyErasure
import GradientHessian.ControllerPolicyDriver

/-! Full adaptive policy replay for isolated center and memory factors.
Saved policy states, pending points, normal operations and both replies are
preserved through every internal step before the explicit disclosure stop. -/

noncomputable section
namespace GradientHessian.DirectionPolicyReplay
open Classical HigherHierarchy HierarchyAddresses RawHierarchy CensoredDirection
  FrontierState TaskState GeometricRepair ComparisonController ComparisonControllerReplay RawDirection

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

abbrev Point (d J : ℕ) (E : Type) (H : ℕ → Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (t : ℕ) :=
  Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t

abbrev Ordinary (d J : ℕ) (E : Type) (H : ℕ → Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] (t : ℕ) :=
  ℝ × (Point d J E H t →L[ℝ] ℝ)

abbrev Rich (d J : ℕ) (E : Type) (H : ℕ → Type)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)] (t : ℕ) :=
  ℝ × (Point d J E H t →L[ℝ] ℝ) × (Point d J E H t →L[ℝ] Point d J E H t →L[ℝ] ℝ)

variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable [∀ t,MeasurableSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (Ordinary d J E H t)] [∀ t,MeasurableSpace (Rich d J E H t)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)

def run (t : ℕ) (policy : Machine.Policy Seed S (Point d J E H t) (Ordinary d J E H t) (Rich d J E H t))
    (K : ℝ) (target : Slot J t) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (raw : Raw d n r J E H t) (fuel : ℕ)
    (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (Point d J E H t) (Action t (4096*J^2))) :=
  ControllerPolicyDriver.run policy (suppress (rules K (assemble P B fallback t raw)) (blockDirection target))
    stop (DirectionPolicy.ordinary K t (coefficients P B fallback t raw))
    (DirectionPolicy.rich K t (coefficients P B fallback t raw)) fuel q

theorem run_eq (t : ℕ) (policy : Machine.Policy Seed S (Point d J E H t) (Ordinary d J E H t) (Rich d J E H t))
    (K : ℝ) (target : Slot J t) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (x y : Raw d n r J E H t)
    (hrules : AgreeOff (rules (ell := ell) K (assemble P B fallback t x))
      (rules K (assemble P B fallback t y)) (blockDirection target))
    (hreplies : ∀ before after,stop after=false → ∀ Z,
      DirectionPolicy.ordinary K t (coefficients P B fallback t x) before after Z=
        DirectionPolicy.ordinary K t (coefficients P B fallback t y) before after Z ∧
      DirectionPolicy.rich K t (coefficients P B fallback t x) before after Z=
        DirectionPolicy.rich K t (coefficients P B fallback t y) before after Z)
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (t+1) (4096*J^2+1) ell S (Point d J E H t) (Action t (4096*J^2))) :
    run P B fallback t policy K target stop x fuel q=run P B fallback t policy K target stop y fuel q := by
  unfold run
  apply ControllerPolicyDriver.run_congr policy
    (suppress (rules K (assemble P B fallback t x)) (blockDirection target))
    (suppress (rules K (assemble P B fallback t y)) (blockDirection target)) stop rfl rfl
  · intro s _ Z a
    cases hb : blockDirection target a with
    | true => simp only [suppress,hb,if_true]
    | false => simpa only [suppress,hb,Bool.false_eq_true,if_false] using hrules.1 s Z a hb
  · intro s _ Z
    exact hrules.2 s Z
  · intro before after _ hs Z
    exact (hreplies before after hs Z).1
  · intro before after _ hs Z
    exact (hreplies before after hs Z).2

def centerStop (h depth : ℕ) (w : Word depth) (i : Fin 8) : State (h+1+depth+1) (4096*J^2+1) ell → Bool :=
  DirectionPolicy.nodeStop (child (addressedNode (h+1) depth w) (by dsimp [addressedNode]; omega) i)

def oldStop (depth : ℕ) (w : Word depth) (i : Fin 8) : State (0+depth+1) (4096*J^2+1) ell → Bool :=
  DirectionPolicy.nodeStop (child (addressedNode 0 depth w) (by dsimp [addressedNode]; omega) i)

theorem center_run_eq {K : ℝ} (hK : 0<K) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x y : Raw d n r J E H (h+1+depth))
    (he : (RawCenterFactor.factor h depth w i x).2=(RawCenterFactor.factor h depth w i y).2)
    (policy : Machine.Policy Seed S (Point d J E H (h+1+depth))
      (Ordinary d J E H (h+1+depth)) (Rich d J E H (h+1+depth)))
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (h+1+depth+1) (4096*J^2+1) ell S
      (Point d J E H (h+1+depth)) (Action (h+1+depth) (4096*J^2))) :
    run P B fallback (h+1+depth) policy K (embed (h+1) depth w (.inr i)) (centerStop h depth w i) x fuel q=
      run P B fallback (h+1+depth) policy K (embed (h+1) depth w (.inr i)) (centerStop h depth w i) y fuel q :=
  run_eq P B fallback _ policy K _ _ x y (center_rule_erasure P B fallback K h depth w i x y he)
    (DirectionPolicy.center_replies_eq P B fallback hK h depth w i x y he) fuel q

theorem old_run_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.oldFactor depth w i j x).2=(RawMemoryHierarchyFactor.oldFactor depth w i j y).2)
    (policy : Machine.Policy Seed S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth)) (Rich d J E H (0+depth)))
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (0+depth+1) (4096*J^2+1) ell S
      (Point d J E H (0+depth)) (Action (0+depth) (4096*J^2))) :
    run P B fallback (0+depth) policy K (embed 0 depth w (.inl (i,j))) (oldStop depth w i) x fuel q=
      run P B fallback (0+depth) policy K (embed 0 depth w (.inl (i,j))) (oldStop depth w i) y fuel q :=
  run_eq P B fallback _ policy K _ _ x y (old_rule_erasure P B fallback K depth w i j x y he)
    (DirectionPolicy.old_replies_eq P B fallback hK depth w i j x y he) fuel q

theorem inner_run_eq {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x y : Raw d n r J E H (0+depth))
    (he : (RawMemoryHierarchyFactor.innerFactor depth w i j k x).2=
      (RawMemoryHierarchyFactor.innerFactor depth w i j k y).2)
    (target : Leaf (0+depth+1))
    (hw : ∀ a : Fin depth,target ⟨a.val,by have := a.isLt; omega⟩=w a)
    (hi : target ⟨depth,by omega⟩=i)
    (policy : Machine.Policy Seed S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth)) (Rich d J E H (0+depth)))
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (0+depth+1) (4096*J^2+1) ell S
      (Point d J E H (0+depth)) (Action (0+depth) (4096*J^2))) :
    run P B fallback (0+depth) policy K (embed 0 depth w (.inr (i,j,k))) (taskDisclosed target j) x fuel q=
      run P B fallback (0+depth) policy K (embed 0 depth w (.inr (i,j,k))) (taskDisclosed target j) y fuel q := by
  apply run_eq P B fallback _ policy K _ _ x y (inner_rule_erasure P B fallback K depth w i j k x y he)
  intro before after hs Z
  exact DirectionPolicy.inner_replies_eq P B fallback hK depth w i j k x y he before after target hw hi hs Z

theorem center_run_factors {K : ℝ} (hK : 0<K) (h depth : ℕ) (w : Word depth) (i : Fin 8)
    (x : Raw d n r J E H (h+1+depth))
    (policy : Machine.Policy Seed S (Point d J E H (h+1+depth))
      (Ordinary d J E H (h+1+depth)) (Rich d J E H (h+1+depth)))
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (h+1+depth+1) (4096*J^2+1) ell S
      (Point d J E H (h+1+depth)) (Action (h+1+depth) (4096*J^2))) :
    run P B fallback (h+1+depth) policy K (embed (h+1) depth w (.inr i)) (centerStop h depth w i) x fuel q=
      run P B fallback (h+1+depth) policy K (embed (h+1) depth w (.inr i)) (centerStop h depth w i)
        ((RawCenterFactor.factor h depth w i).symm (0,(RawCenterFactor.factor h depth w i x).2)) fuel q := by
  apply center_run_eq P B fallback hK h depth w i x _ _ policy fuel q
  simp only [MeasurableEquiv.apply_symm_apply]

theorem old_run_factors {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (FirstHeight.depth (4096*J^2+1)+2)) (x : Raw d n r J E H (0+depth))
    (policy : Machine.Policy Seed S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth)) (Rich d J E H (0+depth)))
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (0+depth+1) (4096*J^2+1) ell S
      (Point d J E H (0+depth)) (Action (0+depth) (4096*J^2))) :
    run P B fallback (0+depth) policy K (embed 0 depth w (.inl (i,j))) (oldStop depth w i) x fuel q=
      run P B fallback (0+depth) policy K (embed 0 depth w (.inl (i,j))) (oldStop depth w i)
        ((RawMemoryHierarchyFactor.oldFactor depth w i j).symm
          (0,(RawMemoryHierarchyFactor.oldFactor depth w i j x).2)) fuel q := by
  apply old_run_eq P B fallback hK depth w i j x _ _ policy fuel q
  simp only [MeasurableEquiv.apply_symm_apply]

theorem inner_run_factors {K : ℝ} (hK : 0<K) (depth : ℕ) (w : Word depth) (i : Fin 8)
    (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2)) (x : Raw d n r J E H (0+depth))
    (target : Leaf (0+depth+1))
    (hw : ∀ a : Fin depth,target ⟨a.val,by have := a.isLt; omega⟩=w a)
    (hi : target ⟨depth,by omega⟩=i)
    (policy : Machine.Policy Seed S (Point d J E H (0+depth))
      (Ordinary d J E H (0+depth)) (Rich d J E H (0+depth)))
    (fuel : ℕ) (q : ControllerPolicyDriver.Config (0+depth+1) (4096*J^2+1) ell S
      (Point d J E H (0+depth)) (Action (0+depth) (4096*J^2))) :
    run P B fallback (0+depth) policy K (embed 0 depth w (.inr (i,j,k))) (taskDisclosed target j) x fuel q=
      run P B fallback (0+depth) policy K (embed 0 depth w (.inr (i,j,k))) (taskDisclosed target j)
        ((RawMemoryHierarchyFactor.innerFactor depth w i j k).symm
          (0,(RawMemoryHierarchyFactor.innerFactor depth w i j k x).2)) fuel q := by
  apply inner_run_eq P B fallback hK depth w i j k x _ _ target hw hi policy fuel q
  simp only [MeasurableEquiv.apply_symm_apply]

end GradientHessian.DirectionPolicyReplay
