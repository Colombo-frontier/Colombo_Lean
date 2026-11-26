import ExplicitRate254
import ScaledGradient254

noncomputable section
namespace Paper254
set_option maxHeartbeats 1000000

theorem cube_ge_one (x : ℝ) (hx : 1 ≤ x) : 1 ≤ x^3 := by
  nlinarith only [hx, mul_nonneg (show 0 ≤ x-1 by linarith) (sq_nonneg x)]

theorem outside_scale_comparison (A B E γ G D T P U : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E) (hγ : 0 ≤ γ)
    (hG : 0 ≤ G) (hD : 0 ≤ D) (hT : 0 ≤ T) (hP : 0 ≤ P) (hU : 0 ≤ U)
    (hAB : 1 ≤ γ*A) (hBB : 1 ≤ γ*B)
    (hE3 : E^3 = B^2*γ*G^2*T*P^2)
    (hthreshold : γ*G^2*T*D^3 ≤ B*P)
    (hU2 : U^2 = G^2*T*(D^2+D*P)) : U ≤ A+2*E := by
  let a2 := G^2*D^2*T
  let b2 := G^2*T*D*P
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have hb2 : 0 ≤ b2 := by dsimp [b2]; positivity
  have hbcube : b2^3 ≤ (E^2)^3 := by
    have hh := mul_le_mul_of_nonneg_left hthreshold
      (show 0 ≤ γ^2*B^3*G^4*T^2*P^3 by positivity)
    have he := congrArg (fun x : ℝ => x^2) hE3
    have hscaled : (γ*B)^3*b2^3 ≤ (E^2)^3 := by
      dsimp [b2]
      nlinarith only [hh,he]
    have hm := mul_le_mul_of_nonneg_right (cube_ge_one (γ*B) hBB) (pow_nonneg hb2 3)
    nlinarith only [hm,hscaled]
  have hb : b2 ≤ E^2 := nonneg_le_of_cube_le _ _ hb2 (sq_nonneg E) hbcube
  have hacube : a2^3 ≤ (A*E)^3 := by
    have hs : (γ*G^2*T*D^3)^2 ≤ (B*P)^2 := by
      have hp := mul_nonneg (sub_nonneg.mpr hthreshold)
        (show 0 ≤ B*P+γ*G^2*T*D^3 by positivity)
      nlinarith only [hp]
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ γ*A^3*G^2*T by positivity)
    have he := congrArg (fun x : ℝ => A^3*x) hE3
    have hscaled : (γ*A)^3*a2^3 ≤ (A*E)^3 := by
      dsimp [a2]
      nlinarith only [hh,he]
    have hm := mul_le_mul_of_nonneg_right (cube_ge_one (γ*A) hAB) (pow_nonneg ha2 3)
    nlinarith only [hm,hscaled]
  have ha : a2 ≤ A*E := nonneg_le_of_cube_le _ _ ha2 (mul_nonneg hA hE) hacube
  have hu : U^2 = a2+b2 := by dsimp [a2,b2]; nlinarith only [hU2]
  by_contra hn
  have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hn))
    (show 0 < U+(A+2*E) by linarith)
  nlinarith only [hu,ha,hb,hp,sq_nonneg A,sq_nonneg E,mul_nonneg hA hE]

end Paper254
#print axioms Paper254.outside_scale_comparison
