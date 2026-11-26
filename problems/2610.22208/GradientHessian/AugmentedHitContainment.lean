import GradientHessian.AugmentedVisibleQueries
import GradientHessian.AugmentedPolicyEvents

/-! Every suppressed hit is tested against a finite array depending only on
the actual external factor and seed. Initialization is replayed before the
first point, and closed initial targets have no hit. -/

noncomputable section
namespace GradientHessian.AugmentedVisibleQueries
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState TaskSlots
  GeometricRepair ComparisonController ComparisonControllerReplay ControllerPolicyCoupling AugmentedPolicy
open DirectionPolicyReplay (Point)

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S V W : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
  [MeasurableSpace V] [MeasurableSpace W]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (blocked : Action t (4096*J^2) → Bool) (stop : State (t+1) (4096*J^2+1) ell → Bool)
  (e : Raw d n r J E H t ≃ᵐ V × W) (replacement : V)
  (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t)
    (Ordinary d J E H t ell) (Rich d J E H t ell))

theorem hitBy_covered (a : Action t (4096*J^2)) (ha : ∀ b,blocked b=true → b=a)
    (v : Node (t+1)) (test : V → Point d J E H t → Prop) (K : ℝ)
    (N fuel : ℕ) (s₀ : State (t+1) (4096*J^2+1) ell)
    (hfactor : ∀ x seed i,stop s₀=false → trajectory P B fallback t policy K blocked stop N s₀ i (x,seed)=
      shadowTrajectory P B fallback t policy blocked stop e replacement K N s₀ i ((e x).2,seed))
    (htrigger : ∀ x (s : State (t+1) (4096*J^2+1) ell) Z,trigger K (assemble P B fallback t x) s Z a=true →
      Visible (TaskState.retired s) v ∧ test (e x).1 Z)
    (hs : Ready s₀) (hell : 0<ell) (w : Raw d n r J E H t × Seed)
    (hhit : AugmentedPolicy.hitBy P B fallback t policy K blocked stop N fuel s₀ w) :
    ∃ q : Fin (cap (J := J) (ell := ell) t v),
      test (e w.1).1 (query P B fallback t blocked stop e replacement policy v K N fuel s₀ ((e w.1).2,w.2) q) := by
  have hinit := hit_initial_open P B fallback t policy K blocked stop N fuel s₀ w hhit
  obtain ⟨i,hi,hh⟩ := hhit
  cases hq : trajectory P B fallback t policy K blocked stop N s₀ i w with
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
      have he : act=a := ha act hact
      subst act
      have hg := htrigger w.1 s p.point htrigger'
      have ht : shadowTrajectory P B fallback t policy blocked stop e replacement K N s₀ i ((e w.1).2,w.2)=
          .pending remaining b output (.repairing p s) := (hfactor w.1 w.2 i hinit).symm.trans hq
      obtain ⟨q,hquery⟩ := repairing_covered P B fallback t blocked stop e replacement policy v K N fuel s₀ hs hell
        ((e w.1).2,w.2) i hi remaining b output p s ht hg.1
      exact ⟨q,hquery.symm ▸ hg.2⟩

end GradientHessian.AugmentedVisibleQueries
