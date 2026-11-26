import GradientHessian.AugmentedPolicyReplay

/-! Literal augmented-policy repair events reach their suppressed shadow
before the selected datum is disclosed. This is purely chronological and
requires no assumed event bound, oracle agreement, or visibility estimate. -/

noncomputable section
namespace GradientHessian.AugmentedPolicy
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair GeometricDisclosure AugmentedDisclosure ComparisonController ComparisonControllerReplay

def disclosureStop {t m ell : ℕ} : Action t m → State (t+1) (m+1) ell → Bool
  | .futureMark leaf j => markStop leaf j
  | a => actionStop a

theorem disclosureStop_completed_mono {t m ell : ℕ} (a : Action t m)
    (s u : State (t+1) (m+1) ell) (hm : ∀ leaf,(s.completed leaf).val≤(u.completed leaf).val)
    (hs : disclosureStop a s=true) : disclosureStop a u=true := by
  cases a with
  | localized h w i => exact actionStop_completed_mono (.localized h w i) s u hm hs
  | old w i j => exact actionStop_completed_mono (.old w i j) s u hm hs
  | inner leaf j k => exact actionStop_completed_mono (.inner leaf j k) s u hm hs
  | futureMark leaf j => exact markStop_completed_mono leaf j s u hm hs

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)]
variable [∀ t,MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (policy : Machine.Policy (Seed × Packet d J E H t ell) S (DirectionPolicyReplay.Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))

def selectedPoints (K : ℝ) (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) (q : Raw d n r J E H t × Seed) :=
  ControllerAdaptiveExecution.queries policy (rules K (assemble P B fallback t q.1))
    (ordinary P B fallback K t q.1) (rich P B fallback K t q.1) N
    (policy.initial (q.2,view K (assemble P B fallback t q.1) s)) s

def hitBy (K : ℝ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (N fuel : ℕ) (s : State (t+1) (4096*J^2+1) ell) (q : Raw d n r J E H t × Seed) : Prop :=
  ∃ i≤fuel,ControllerPolicyCoupling.BlockedHit (rules K (assemble P B fallback t q.1)) blocked stop
    (trajectory P B fallback t policy K blocked stop N s i q)

theorem hit_initial_open (K : ℝ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (N fuel : ℕ) (s : State (t+1) (4096*J^2+1) ell) (q : Raw d n r J E H t × Seed)
    (h : hitBy P B fallback t policy K blocked stop N fuel s q) : stop s=false := by
  cases hs : stop s with
  | false => rfl
  | true =>
    obtain ⟨i,_,hi⟩ := h
    cases i with
    | zero => simp only [trajectory,run,initial,ControllerPolicyDriver.initial,ControllerPolicyDriver.run,
        ControllerPolicyCoupling.BlockedHit] at hi
    | succ i =>
      simp only [trajectory,run,initial,ControllerPolicyDriver.initial,ControllerPolicyDriver.run,
        ControllerPolicyDriver.step,hs,if_true,ControllerPolicyDriver.run_finished,ControllerPolicyCoupling.BlockedHit] at hi

theorem trigger_stop_false (K : ℝ) (data : Data (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
    (s : State (t+1) (4096*J^2+1) ell) (Z : DirectionPolicyReplay.Point d J E H t)
    (a : Action t (4096*J^2)) (ha : trigger K data s Z a=true) : disclosureStop a s=false := by
  cases a with
  | localized h w i => exact trigger_actionStop_false K data s Z _ ha
  | old w i j => exact trigger_actionStop_false K data s Z _ ha
  | inner leaf j k => exact trigger_actionStop_false K data s Z _ ha
  | futureMark leaf j =>
    simp only [trigger,decide_eq_true_eq] at ha
    exact decide_eq_false ha.2.1

theorem action_hitBy (K : ℝ) (N : ℕ) (s : State (t+1) (4096*J^2+1) ell) (hs : Ready s) (hell : 0<ell)
    (q : Raw d n r J E H t × Seed) (a : Action t (4096*J^2)) (blocked : Action t (4096*J^2) → Bool)
    (hb : blocked a=true)
    (ha : a ∈ ControllerRepairEvents.actions (rules K (assemble P B fallback t q.1))
      (selectedPoints P B fallback t policy K N s q) s) :
    hitBy P B fallback t policy K blocked (disclosureStop a) N ((N+1)*(8^(t+1)+4)) s q := by
  obtain ⟨i,hi,hhit⟩ := ControllerAdaptiveExecution.action_has_shadow_hit policy
    (rules K (assemble P B fallback t q.1)) (ordinary P B fallback K t q.1) (rich P B fallback K t q.1)
    a blocked hb (disclosureStop a)
    (fun s _ b hs => disclosureStop_completed_mono a s _ (VisibilityTaskWindow.retireSet_completed_mono s (subtree (target b))) hs)
    (fun s hs p hstop => disclosureStop_completed_mono a s _ (VisibilityTaskWindow.normal_completed_mono _ p hs) hstop)
    (fun p s hc => trigger_stop_false t K (assemble P B fallback t q.1) s p.point a
      (choose_spec (rules K (assemble P B fallback t q.1)) p s hc).2.1)
    hell N (policy.initial (q.2,view K (assemble P B fallback t q.1) s)) s hs ha
  exact ⟨i,hi.le,hhit⟩

end GradientHessian.AugmentedPolicy
