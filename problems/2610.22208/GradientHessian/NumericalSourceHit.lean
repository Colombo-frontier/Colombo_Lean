import GradientHessian.NumericalSourceCaches
import GradientHessian.ControllerNormalRealization

noncomputable section
namespace GradientHessian.NumericalSourceCaches
open Classical Matrix HigherHierarchy HierarchyAddresses FrontierState TaskState
  ComparisonController ComparisonControllerReplay GeometricRepair ControllerNormalRealization
open scoped InnerProductSpace

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]

theorem hit_readout {K : ℝ} (x : RawHierarchy.Raw d n r J E H t × Seed)
    (j : Fin (4096*J^2+1)) (p : Pending (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t))
    (u : State (t+1) (4096*J^2+1) ell)
    (hc : TaskState.current u=some leaf) (hj : (u.completed leaf).val=j.val)
    (hh : (rules K (RawHierarchy.assemble P B fallback t x.1)).hit u p.point=true) :
    let w := input t leaf j x
    ForkLifetime.gamma < |⟪UnmarkedReadout.sourceOutput J P w.1.1 B fallback w.2.1,
      BoundedNumericalTest.test (CensoredOracle.numericalMap t p.point)⟫_ℝ| := by
  dsimp only
  change hit (RawHierarchy.assemble P B fallback t x.1) u p.point=true at hh
  rw [hit_current _ u p.point hc] at hh
  have hi : (⟨(u.completed leaf).val,TaskState.current_live u hc⟩ : Fin (4096*J^2+1))=j := Fin.ext hj
  rw [hi] at hh
  rw [target_readout P B fallback t leaf j x]
  simpa only [ForkLifetime.gamma,markReadout,CensoredOracle.numericalMap_eq] using (of_decide_eq_true hh)

end GradientHessian.NumericalSourceCaches
