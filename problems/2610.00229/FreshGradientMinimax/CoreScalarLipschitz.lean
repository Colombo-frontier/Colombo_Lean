import FreshGradientMinimax.CoreLinkTermDerivative
import Mathlib.Analysis.Calculus.MeanValue

/-! Global scalar Lipschitz estimates obtained from the actual derivatives. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax

theorem scalar_sub_le_of_derivative_bound {f d : ℝ → ℝ} {C : ℝ}
    (hd : ∀ x, HasDerivAt f (d x) x) (hb : ∀ x, |d x| ≤ C) (x y : ℝ) :
    |f x - f y| ≤ C * |x - y| := by
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hd z).hasDerivWithinAt)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hb z)
      (Set.mem_univ y) (Set.mem_univ x)

theorem coreDensity_sub_le (x y : ℝ) : |coreDensity x - coreDensity y| ≤ |x - y| := by
  have h := scalar_sub_le_of_derivative_bound coreDensity_hasDerivAt
    (fun z => by simpa only [abs_mul, abs_neg, abs_of_pos (coreDensity_pos z)] using
      coreDensity_abs_mul_le_one z) x y
  simpa only [one_mul] using h

theorem coreTheta_sub_le (x y : ℝ) : |coreTheta x - coreTheta y| ≤ |x - y| := by
  have h := scalar_sub_le_of_derivative_bound coreTheta_hasDerivAt
    (fun z => by simpa only [abs_of_pos (coreDensity_pos z)] using coreDensity_le_one z) x y
  simpa only [one_mul] using h

theorem coreGate_sub_le (x y : ℝ) : |coreGate x - coreGate y| ≤ 16 * |x - y| :=
  scalar_sub_le_of_derivative_bound (fun z => coreGate_hasDerivAt z) coreGateDeriv_bound x y

theorem coreGateDeriv_sub_le (x y : ℝ) : |coreGateDeriv x - coreGateDeriv y| ≤ 512 * |x - y| :=
  scalar_sub_le_of_derivative_bound coreGateDeriv_hasDerivAt coreGateSecond_bound x y

theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a - c| * |b| + |c| * |b - d| := by
  calc
    _ = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

theorem coreGateDerivTheta_sub_le (a b c d : ℝ) :
    |coreGateDeriv a * coreTheta b - coreGateDeriv c * coreTheta d| ≤
      1536 * |a - c| + 16 * |b - d| := by
  have h := abs_mul_sub_mul_le (coreGateDeriv a) (coreTheta b) (coreGateDeriv c) (coreTheta d)
  have h1 := mul_le_mul (coreGateDeriv_sub_le a c)
    (show |coreTheta b| ≤ 3 by rw [abs_of_pos (coreTheta_pos b)]; exact (coreTheta_lt_three b).le)
    (abs_nonneg _) (by positivity : 0 ≤ 512 * |a - c|)
  have h2 := mul_le_mul (coreGateDeriv_bound c) (coreTheta_sub_le b d)
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 16)
  nlinarith only [h, h1, h2]

theorem coreLinkTermD1_sub_le (a b c d : ℝ) :
    |coreLinkTermD1 a b - coreLinkTermD1 c d| ≤ 3072 * |a - c| + 32 * |b - d| := by
  have hp := coreGateDerivTheta_sub_le a b c d
  have hm := coreGateDerivTheta_sub_le (-a) (-b) (-c) (-d)
  simp only [neg_sub_neg, abs_sub_comm c a, abs_sub_comm d b] at hm
  calc
    _ = |-(coreGateDeriv (-a) * coreTheta (-b) - coreGateDeriv (-c) * coreTheta (-d)) -
        (coreGateDeriv a * coreTheta b - coreGateDeriv c * coreTheta d)| := by
      unfold coreLinkTermD1; congr 1; ring
    _ ≤ |coreGateDeriv (-a) * coreTheta (-b) - coreGateDeriv (-c) * coreTheta (-d)| +
        |coreGateDeriv a * coreTheta b - coreGateDeriv c * coreTheta d| := by
      simpa only [abs_neg] using abs_sub
        (-(coreGateDeriv (-a) * coreTheta (-b) - coreGateDeriv (-c) * coreTheta (-d)))
        (coreGateDeriv a * coreTheta b - coreGateDeriv c * coreTheta d)
    _ ≤ _ := by linarith only [hp, hm]

theorem coreLinkTermD2_sub_le (a b c d : ℝ) :
    |coreLinkTermD2 a b - coreLinkTermD2 c d| ≤ 32 * |a - c| + 6 * |b - d| := by
  have hg : |(coreGate (-a) + coreGate a) - (coreGate (-c) + coreGate c)| ≤ 32 * |a - c| := by
    have hp := coreGate_sub_le a c
    have hm := coreGate_sub_le (-a) (-c)
    simp only [neg_sub_neg, abs_sub_comm c a] at hm
    have ht := abs_add_le (coreGate (-a) - coreGate (-c)) (coreGate a - coreGate c)
    have he : (coreGate (-a) + coreGate a) - (coreGate (-c) + coreGate c) =
      (coreGate (-a) - coreGate (-c)) + (coreGate a - coreGate c) := by ring
    rw [he]; linarith only [hp, hm, ht]
  have hv : |coreGate (-c) + coreGate c| ≤ 6 := by
    rw [abs_of_nonneg (add_nonneg (coreGate_nonneg _) (coreGate_nonneg _))]
    linarith [coreGate_le_three (-c), coreGate_le_three c]
  have h := abs_mul_sub_mul_le (coreGate (-a) + coreGate a) (coreDensity b)
    (coreGate (-c) + coreGate c) (coreDensity d)
  have h1 := mul_le_mul hg
    (show |coreDensity b| ≤ 1 by rw [abs_of_pos (coreDensity_pos b)]; exact coreDensity_le_one b)
    (abs_nonneg _) (by positivity : 0 ≤ 32 * |a - c|)
  have h2 := mul_le_mul hv (coreDensity_sub_le b d) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
  have he : coreLinkTermD2 a b - coreLinkTermD2 c d =
      -((coreGate (-a) + coreGate a) * coreDensity b - (coreGate (-c) + coreGate c) * coreDensity d) := by
    unfold coreLinkTermD2; ring
  rw [he, abs_neg]
  nlinarith only [h, h1, h2]

end FreshGradientMinimax
