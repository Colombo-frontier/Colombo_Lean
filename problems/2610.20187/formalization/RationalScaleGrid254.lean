import ScaleGrid254
import RationalUniformStep254

noncomputable section
namespace Paper254

def cappedDyadicScale (D : ℝ) (k : ℕ) : ℝ := min (dyadicScale D k) (D/2)
def rationalCappedVariance (H : ℚ) (k : ℕ) : ℚ := min (H/((2 : ℚ)^k)^2) (H/4)

theorem rationalCappedVariance_cast (D : ℝ) (hD : 0 < D) (H : ℚ) (hH : (H : ℝ)=D^2)
    (k : ℕ) : (rationalCappedVariance H k : ℝ)=(cappedDyadicScale D k)^2 := by
  have ha : 0≤dyadicScale D k := (dyadicScale_pos D hD k).le
  have hb : 0≤D/2 := by positivity
  have hc : (rationalCappedVariance H k : ℝ)=min ((dyadicScale D k)^2) ((D/2)^2) := by
    simp only [rationalCappedVariance,Rat.cast_min,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat,hH]
    norm_num [dyadicScale,div_pow]
  rw [hc]
  unfold cappedDyadicScale
  by_cases hab : dyadicScale D k≤D/2
  · rw [min_eq_left hab,min_eq_left (by nlinarith)]
  · have hba : D/2≤dyadicScale D k := (not_le.mp hab).le
    rw [min_eq_right hba,min_eq_right (by nlinarith)]

theorem cappedDyadicScale_range (D : ℝ) (hD : 0 < D) (T : ℕ) (hT : 2 ≤ T)
    (k : Fin (scaleCount T+1)) : D/T≤cappedDyadicScale D k.val ∧
      0<cappedDyadicScale D k.val ∧ cappedDyadicScale D k.val≤D/2 := by
  have hr := dyadicScale_range D hD T (by omega) k
  have hh := strict_scale_reduction D T (dyadicScale D k.val) hD (by exact_mod_cast hT) hr.1 hr.2
  exact ⟨hh.1,hh.2.1,hh.2.2.1⟩

theorem rationalCappedVariance_range (D : ℝ) (hD : 0 < D) (H : ℚ) (hH : (H : ℝ)=D^2)
    (k : ℕ) : 0<(rationalCappedVariance H k : ℝ) ∧ (rationalCappedVariance H k : ℝ)<(H : ℝ) := by
  rw [rationalCappedVariance_cast D hD H hH k,hH]
  have hp : 0<cappedDyadicScale D k := lt_min (dyadicScale_pos D hD k) (by positivity)
  have hb : cappedDyadicScale D k≤D/2 := min_le_right _ _
  exact ⟨sq_pos_of_pos hp,by nlinarith⟩

theorem cappedDyadicScale_approx (D : ℝ) (hD : 0 < D) (T : ℕ) (hT : 2 ≤ T)
    (tau : ℝ) (hlo : D/T≤tau) (hhi : tau≤D) :
    ∃ k : Fin (scaleCount T+1),tau/2≤cappedDyadicScale D k.val ∧
      cappedDyadicScale D k.val≤2*tau := by
  obtain ⟨k,hklo,hkhi⟩ := dyadic_scale_approx D hD T (by omega) tau hlo hhi
  have htau : 0<tau := (div_pos hD (by exact_mod_cast (show 0<T by omega))).trans_le hlo
  refine ⟨k,le_min (by linarith) (by linarith),?_⟩
  exact (min_le_left _ _).trans hkhi

end Paper254
#print axioms Paper254.rationalCappedVariance_cast
#print axioms Paper254.cappedDyadicScale_approx
