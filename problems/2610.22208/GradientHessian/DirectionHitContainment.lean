import GradientHessian.DirectionVisibleQueries
import GradientHessian.DirectionStoppedAction

/-! The finite-array containment underlying all three direction families.
The only structural equalities here are supplied by the separately checked
literal raw-factor replay and raw-coordinate test identities. -/

noncomputable section
namespace GradientHessian.DirectionVisibleQueries
open Classical HigherHierarchy HierarchyAddresses RawHierarchy HierarchyParameters
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  ControllerPolicyCoupling RawDirection DirectionPolicyReplay

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (Ordinary d J E H t)] [∀ t,BorelSpace (Ordinary d J E H t)]
  [∀ t,MeasurableSpace (Rich d J E H t)] [∀ t,BorelSpace (Rich d J E H t)]
variable {Seed S V W : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
  [MeasurableSpace V] [MeasurableSpace W]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (target : Slot J t) (stop : State (t+1) (4096*J^2+1) ell → Bool)
  (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
  (policy : Machine.Policy Seed S (Point d J E H t) (Ordinary d J E H t) (Rich d J E H t))

def hitBy (K : ℝ) (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (w : Raw d n r J E H t × Seed) : Prop :=
  ∃ i≤fuel,BlockedHit (rules K (assemble P B fallback t w.1)) (blockDirection target) stop
    (DirectionPolicyReplay.run P B fallback t policy K target stop w.1 i
      (ControllerPolicyDriver.initial policy N w.2 s₀))

theorem hitBy_covered (a : Action t (4096*J^2)) (ha : directionSlot a=some target)
    (v : Node (t+1)) (test : V → Point d J E H t → Prop) (K : ℝ)
    (hfactor : ∀ x i q,DirectionPolicyReplay.run P B fallback t policy K target stop x i q=
      DirectionPolicyReplay.shadow P B fallback t target stop policy e replacement K (e x).2 i q)
    (htrigger : ∀ x (s : State (t+1) (4096*J^2+1) ell) Z,trigger K (assemble P B fallback t x) s Z a=true →
      Visible (TaskState.retired s) v ∧ test (e x).1 Z)
    (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell) (hs : Ready s₀) (hell : 0<ell)
    (w : Raw d n r J E H t × Seed) (hhit : hitBy P B fallback t target stop policy K N fuel s₀ w) :
    ∃ q : Fin (cap (J := J) (ell := ell) t v),
      test (e w.1).1 (query P B fallback t target stop e replacement policy v K N fuel s₀ ((e w.1).2,w.2) q) := by
  obtain ⟨i,hi,hh⟩ := hhit
  cases hq : DirectionPolicyReplay.run P B fallback t policy K target stop w.1 i
      (ControllerPolicyDriver.initial policy N w.2 s₀) with
  | ready remaining b s => simp only [hq,BlockedHit] at hh
  | finished b s => simp only [hq,BlockedHit] at hh
  | pending remaining b output phase =>
    cases phase with
    | normal p s => simp only [hq,BlockedHit] at hh
    | delivered p before after => simp only [hq,BlockedHit] at hh
    | frozen p s => simp only [hq,BlockedHit] at hh
    | repairing p s =>
      rw [hq] at hh
      obtain ⟨_,act,hact,htrigger'⟩ := hh
      rw [blockDirection_eq_single a target ha] at hact
      have he : act=a := of_decide_eq_true hact
      subst act
      have hg := htrigger w.1 s p.point htrigger'
      have ht : trajectory P B fallback t target stop e replacement policy K N s₀ i ((e w.1).2,w.2)=
          .pending remaining b output (.repairing p s) :=
        (hfactor w.1 i (ControllerPolicyDriver.initial policy N w.2 s₀)).symm.trans hq
      obtain ⟨q,hquery⟩ := repairing_covered P B fallback t target stop e replacement policy v K N fuel s₀ hs hell
        ((e w.1).2,w.2) i hi remaining b output p s ht hg.1
      exact ⟨q,hquery.symm ▸ hg.2⟩

theorem original_action_hitBy {K : ℝ} (hK : 0<K) (a : Action t (4096*J^2))
    (ha : directionSlot a=some target) (hell : 0<ell) (N : ℕ) (w : Raw d n r J E H t × Seed)
    (hd : Valid (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t (assemble P B fallback t w.1))
    (hevent : a ∈ ControllerRepairEvents.actions (rules (ell := ell) K (assemble P B fallback t w.1))
      (ControllerPolicyTrace.withOutput policy (JetLocality.ordinaryJet (scalar K t (assemble P B fallback t w.1)))
        (JetLocality.richJet (scalar K t (assemble P B fallback t w.1))) N w.2) TaskState.initial) :
    hitBy P B fallback t target (actionStop (ell := ell) a) policy K N ((N+1)*(8^(t+1)+4)) TaskState.initial w := by
  have hd' : Valid (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t
      (decode t (coefficients P B fallback t w.1)) := by simpa only [decode_coefficients] using hd
  have hevent' := hevent
  rw [← decode_coefficients P B fallback t w.1] at hevent'
  obtain ⟨i,hi,hh⟩ := DirectionStoppedAction.original_action_has_shadow_hit t policy hK
    (coefficients P B fallback t w.1) hd' hell N w.2 a (blockDirection target)
    (by simp only [blockDirection,ha,decide_true]) hevent'
  refine ⟨i,hi.le,?_⟩
  simpa only [decode_coefficients,DirectionPolicyReplay.run] using hh

end GradientHessian.DirectionVisibleQueries
