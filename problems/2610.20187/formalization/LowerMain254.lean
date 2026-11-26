import StaticLower254
import LowerEndpoints254
import MiddleDimension254

noncomputable section
open MeasureTheory
namespace Paper254

theorem main_lower : MainLowerStatement := by
  refine ⟨1/1048576,4096,by norm_num,by norm_num,?_⟩
  intro d T hd hT horizon P hP Ω _ μ hμ A hA
  letI : IsProbabilityMeasure μ := hμ
  let F := min (unloggedRate d T P) (min (Real.sqrt ((T : ℝ)*P)) T)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hTbig : (4096 : ℝ) ≤ T := by nlinarith
  have hstaticT : d^2 ≤ T := by
    exact_mod_cast (show (d : ℝ)^2 ≤ T by nlinarith [sq_nonneg (d : ℝ)])
  have hF0 : 0 ≤ F := le_min (unloggedRate_nonneg d T P hP)
    (le_min (Real.sqrt_nonneg _) (Nat.cast_nonneg T))
  have hFc : F ≤ unloggedRate d T P := min_le_left _ _
  have hFs : F ≤ Real.sqrt ((T : ℝ)*P) := (min_le_right _ _).trans (min_le_left _ _)
  have hFt : F ≤ (T : ℝ) := (min_le_right _ _).trans (min_le_right _ _)
  have hfront : normalizedFrontier d T P = (d : ℝ)+F := rfl
  by_cases hsmallF : F ≤ 3*d
  · obtain ⟨s,v,hpath,hreg⟩ := static_dimension_lower hd hstaticT μ A hA
    refine ⟨s,v,by rw [hpath]; exact hP,?_⟩
    rw [hfront]
    nlinarith
  · have hlow : 4*d/Real.sqrt T ≤ P := by
      by_contra hh
      have hc := small_path_rate d T hT P hP (le_of_not_ge hh)
      exact hsmallF (hFc.trans hc)
    have hmoving : ∃ (s : Fin T → Fin d × Bool) (v : Fin T → (ballDomain d).carrier),
        pathLength v ≤ P ∧ F/262144 ≤ ∫ ω, regret (A ω) (hardSequence s) v ∂μ := by
      by_cases hsat : (T : ℝ)/1024 ≤ P
      · obtain ⟨s,v,hpath,hreg⟩ := saturation_lower hd hT hTbig P hsat μ A hA
        exact ⟨s,v,hpath,by linarith⟩
      · have hPsmall : P ≤ T/1024 := le_of_not_ge hsat
        by_cases hdim : P ≤ T/(8*(d : ℝ)^2)
        · obtain ⟨s,v,hpath,hreg⟩ := effective_dimension_lower hd (le_refl d) hT P hP hlow hdim μ A hA
          exact ⟨s,v,hpath,by linarith⟩
        · obtain ⟨m,hm,hmd,hlo,hhi,hrate⟩ := middle_dimension_choice d T hd hT horizon P (lt_of_not_ge hdim) hPsmall
          obtain ⟨s,v,hpath,hreg⟩ := effective_dimension_lower hm hmd hT P hP hlo hhi μ A hA
          exact ⟨s,v,hpath,by linarith⟩
    obtain ⟨s,v,hpath,hreg⟩ := hmoving
    refine ⟨s,v,hpath,?_⟩
    rw [hfront]
    have hh : 3*(d : ℝ) < F := lt_of_not_ge hsmallF
    nlinarith

end Paper254
#print axioms Paper254.main_lower
