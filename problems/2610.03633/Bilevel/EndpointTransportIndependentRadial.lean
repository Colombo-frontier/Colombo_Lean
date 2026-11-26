import Bilevel.EndpointTransportRadialChannels
import Bilevel.ChiUniformRadialExtension

/-! Actual physical public-normal budgets at independent source widths.
The final gamma rescaling only decreases both budget contributions. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCurvatureSchedule ChiExtension ChiExtensionCalibration PrimitiveGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem physical_radial_uniform_jets {J s : ℕ} (n D : ℕ) (index : Fin J → Fin s)
    (ρ R : ℕ → ℝ) (d H K : ℝ) (hρ : ∀ i : Fin J,0≤ρ (i.val+1))
    (hR : ∀ i : Fin J,0<R (i.val+1)) (hd : 0<d)
    (hH : ∀ i : Fin J,ρ (i.val+1)*R (i.val+1)≤H) (hK : ∀ i : Fin J,ρ (i.val+1)≤K)
    (z : Full (PhysicalBase E J n D) s) :
    ‖iteratedFDeriv ℝ 2 (radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) d) z‖≤(J:ℝ)*(3*H/d) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) d) z‖≤(J:ℝ)*(9*K/d) := by
  have hb := physical_radial_sum_jets n D index ρ R d hρ hR hd z
  constructor
  · apply hb.1.trans
    calc
      _≤∑ _ : Fin J,3*H/d := by
        apply Finset.sum_le_sum
        intro i _
        have h := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hH i) hd.le) (by norm_num : (0:ℝ)≤3)
        convert h using 1
        ring
      _=_ := by simp
  · apply hb.2.trans
    calc
      _≤∑ _ : Fin J,9*K/d := by
        apply Finset.sum_le_sum
        intro i _
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hK i) (by norm_num)) hd.le
      _=_ := by simp

theorem independent_physical_radial_jets {J s : ℕ} (n D : ℕ) (index : Fin J → Fin s)
    (initial : Scale) (η Kg T ζ CR d : ℝ) (weight : ℕ → ℝ)
    (hl : 0 < initial.curvature) (hb : 0 < initial.width) (hη : 0<η) (hη1 : η≤1)
    (hK : 0<Kg) (hT : 1≤T) (hζ : 0<ζ) (hCR : 0<CR) (hd : 0<d)
    (hw : ∀ j,0<weight j) (hw1 : ∀ j,weight j≤1) (z : Full (PhysicalBase E J n D) s) :
    let parent := fun j => parentScale initial (sourceRatio T) (resolution η Kg) j
    let ρ := fun j => weight j*(ζ*(parent j).curvature)
    let R := fun j => sourceLocalRadius CR (parent j).curvature (parent j).width (sourceRatio T j) (weight j) ζ
    ‖iteratedFDeriv ℝ 2 (radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) d) z‖≤
      3*CR*(initial.force/(Kg*d))*(J:ℝ)*T^(3/8:ℝ) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) d) z‖≤9*ζ*(initial.curvature/d)*(J:ℝ)*T := by
  dsimp only
  let parent := fun j => parentScale initial (sourceRatio T) (resolution η Kg) j
  let ρ := fun j => weight j*(ζ*(parent j).curvature)
  let R := fun j => sourceLocalRadius CR (parent j).curvature (parent j).width (sourceRatio T j) (weight j) ζ
  have hTp : 0<T := by linarith
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg)
    hl hb (sourceRatio_ge_one hT) (base_resolution_positive hη hK)
  have hcurv (i : Fin J) : (parent (i.val+1)).curvature ≤ initial.curvature*T := by
    rw [source_parent_curvature initial hTp]
    exact mul_le_mul_of_nonneg_left (curvature_bounds hT i.val).2 hl.le
  have hprod (i : Fin J) : ρ (i.val+1)*R (i.val+1)≤CR*(initial.force/Kg*T^(3/8:ℝ)) := by
    rw [show ρ (i.val+1)*R (i.val+1)=CR*((parent (i.val+1)).curvature*(parent (i.val+1)).width)*
      Real.sqrt (sourceRatio T (i.val+1)) from source_radial_coefficient_radius (hp (i.val+1)).1 (hw _) hζ]
    have h := mul_le_mul_of_nonneg_left
      (independent_parent_force_bound initial hT hη.le hη1 hK hl.le hb.le i.val) hCR.le
    convert h using 1; dsimp only [parent,Scale.force]; ring
  have hν (i : Fin J) : ρ (i.val+1)≤ζ*(initial.curvature*T) := by
    have hweight := mul_le_mul_of_nonneg_right (hw1 (i.val+1)) (hp (i.val+1)).1.le
    have hval : weight (i.val+1)*(parent (i.val+1)).curvature ≤ initial.curvature*T :=
      hweight.trans (by simpa only [one_mul] using hcurv i)
    have h := mul_le_mul_of_nonneg_left hval hζ.le
    convert h using 1; dsimp only [ρ]; ring
  have hj := physical_radial_uniform_jets n D index ρ R d
    (CR*(initial.force/Kg*T^(3/8:ℝ))) (ζ*(initial.curvature*T))
    (fun i => mul_nonneg (hw _).le (mul_nonneg hζ.le (hp (i.val+1)).1.le))
    (fun i => source_radial_radius_pos hCR (hp (i.val+1)).1 (hp (i.val+1)).2
      (lt_of_lt_of_le zero_lt_one (sourceRatio_ge_one hT _)) (hw _) hζ) hd hprod hν z
  constructor
  · convert hj.1 using 1; ring
  · convert hj.2 using 1; ring

end Bilevel.EndpointTransportResponse
