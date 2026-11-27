import Task003Base
import Nonsmooth.FiniteSupport

noncomputable section
set_option autoImplicit false
namespace Task003Integration
open MeasureTheory Set Task003.OracleSimulation Task003.OracleReduction PaperGeometry
open scoped RealInnerProductSpace

abbrev ZhangEuclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

def zhangHalfRows {d k : ℕ} (a : Nonsmooth.BoundedSupportRows (ZhangEuclidean d) (Fin k)) :
    Fin k → Fin d → ℝ := fun i j => (a i).val j / 2

theorem zhangHalfRows_measurable (d k : ℕ) : Measurable (@zhangHalfRows d k) := by
  unfold zhangHalfRows
  fun_prop

theorem zhangHalfSupport {d k : ℕ} [Nonempty (Fin k)]
    (a : Nonsmooth.BoundedSupportRows (ZhangEuclidean d) (Fin k)) (x : ZhangEuclidean d) :
    sourceSupport (zhangHalfRows a) x = Nonsmooth.boundedFiniteSupport a x / 2 := by
  have hrow (i : Fin k) : rowValue (zhangHalfRows a i) (fromEuclidean x) =
      ⟪(a i).val,x⟫ / 2 := by
    change (∑ j, ((a i).val j / 2) * x j) = _
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  apply le_antisymm
  · change (Finset.univ.sup' Finset.univ_nonempty
      (fun i => rowValue (zhangHalfRows a i) (fromEuclidean x))) ≤ _
    apply (Finset.sup'_le_iff _ _).mpr
    intro i hi
    rw [hrow]
    exact div_le_div_of_nonneg_right (Nonsmooth.finiteSupport_ge (fun i => (a i).val) x i)
      (by norm_num)
  · change Nonsmooth.boundedFiniteSupport a x / 2 ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => rowValue (zhangHalfRows a i) (fromEuclidean x))
    obtain ⟨i,hi⟩ := Nonsmooth.finiteSupport_attained (fun i => (a i).val) x
    have hle := Finset.le_sup' (fun i => rowValue (zhangHalfRows a i) (fromEuclidean x))
      (Finset.mem_univ i)
    rw [hrow] at hle
    exact (by simpa only [Nonsmooth.boundedFiniteSupport,hi] using hle)

theorem zhangHalfOptimum {d k : ℕ} [Nonempty (Fin k)]
    (a : Nonsmooth.BoundedSupportRows (ZhangEuclidean d) (Fin k)) :
    sourceOptimum (sourceSupport (zhangHalfRows a)) =
      Nonsmooth.minimumValue 1 (Nonsmooth.boundedFiniteSupport a) / 2 := by
  have hc : Continuous (Nonsmooth.boundedFiniteSupport a) :=
    Nonsmooth.finiteSupport_joint_continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x,hx,hmin⟩ := (isCompact_closedBall (0 : ZhangEuclidean d) (1:ℝ)).exists_isMinOn
    (⟨0, by simp⟩ : (Metric.closedBall (0 : ZhangEuclidean d) 1).Nonempty) hc.continuousOn
  have hx' : ‖x‖ ≤ (1:ℝ) := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  have hm : ∀ y : ZhangEuclidean d, ‖y‖ ≤ 1 →
      Nonsmooth.boundedFiniteSupport a x ≤ Nonsmooth.boundedFiniteSupport a y := by
    intro y hy
    exact hmin (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy)
  have hs := sourceOptimum_eq_of_min (sourceSupport (zhangHalfRows a)) x hx' (by
    intro y hy
    rw [zhangHalfSupport,zhangHalfSupport]
    exact div_le_div_of_nonneg_right (hm y hy) (by norm_num))
  rw [hs,Nonsmooth.minimumValue_eq hx' hm,zhangHalfSupport]

end Task003Integration
