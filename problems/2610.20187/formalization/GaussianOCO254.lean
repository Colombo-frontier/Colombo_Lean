import GaussianBirth254
import SurrogateCurvature254
import Energy254

noncomputable section
open scoped Matrix BigOperators RealInnerProductSpace
open Matrix
namespace Paper254

theorem coordinate_inner {d : ℕ} (g x : Space d) :
    (g : Coordinates d) ⬝ᵥ (x : Coordinates d) = ⟪g,x⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  exact dotProduct_comm _ _

theorem coordinate_surrogate_eq {d : ℕ} (γ : ℝ) (g w x : Space d) :
    coordinateSurrogate γ g w x = rankOneSurrogate γ g w x := by
  have he : (g : Coordinates d) ⬝ᵥ ((x : Coordinates d)-(w : Coordinates d)) = ⟪g,x-w⟫ :=
    coordinate_inner g (x-w)
  simp only [coordinateSurrogate, rankOneSurrogate, he]

theorem coordinate_curvature_bound {d : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (g : Space d) (hg : ‖g‖ ≤ G)
    (m w : W.carrier) :
    |curvature D G η*((g : Coordinates d) ⬝ᵥ ((m.val : Coordinates d)-(w.val : Coordinates d)))| ≤ 1/4 := by
  have hγ := curvature_pos D G η hD hG hη
  have he : (g : Coordinates d) ⬝ᵥ ((m.val : Coordinates d)-(w.val : Coordinates d)) =
      ⟪g,m.val-w.val⟫ := coordinate_inner g (m.val-w.val)
  rw [he, abs_mul, abs_of_pos hγ]
  exact le_trans (mul_le_mul_of_nonneg_left
    (gradient_inner_bound W hG.le hg w.property m.property) hγ.le)
    (curvature_times_radius D G η hD hG)

def gaussianHistory {d : ℕ} {D : ℝ} (W : Domain d D) (hD : 0 < D)
    (w0 : W.carrier) (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q)
    (g : ℕ → Space d) (w : ℕ → W.carrier) : ℕ → PrecisionGaussian d
  | 0 => isotropicGaussian w0.val D hD
  | t+1 => (gaussianHistory W hD w0 lam q hlam hq g w t).historyUpdate W lam q hlam hq (g t) (w t).val

theorem gaussianHistory_feasible {d : ℕ} {D : ℝ} (W : Domain d D) (hD : 0 < D)
    (w0 : W.carrier) (lam q : ℝ) (hlam : 0 ≤ lam) (hq : 0 < q)
    (g : ℕ → Space d) (w : ℕ → W.carrier) (t : ℕ) :
    WithLp.toLp 2 (gaussianHistory W hD w0 lam q hlam hq g w t).mean ∈ W.carrier := by
  cases t with
  | zero => exact w0.property
  | succ t => exact PrecisionGaussian.historyUpdate_feasible _ W lam q hlam hq _ _

theorem gaussianHistory_drawdown {d : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier) (q : ℝ) (hq : 0 < q)
    (g : ℕ → Space d) (w u : ℕ → W.carrier) (n : ℕ) (H : ℝ)
    (hg : ∀ t ≤ n, ‖g t‖ ≤ G)
    (hdraw : let γ := curvature D G η
      let lam := γ/2
      let P := gaussianHistory W hD w0 lam q
        (le_of_lt (div_pos (curvature_pos D G η hD hG hη) (by norm_num))) hq g w
      let r := fun t => coordinateSurrogate γ (g t) (w t).val (P t).mean-
        smoothedCoordinateSurrogate γ q (g t) (w t).val (u t).val
      ∀ k ≤ n+1, -H ≤ cumulative r k) :
    let γ := curvature D G η
    let lam := γ/2
    let P := gaussianHistory W hD w0 lam q
      (le_of_lt (div_pos (curvature_pos D G η hD hG hη) (by norm_num))) hq g w
    let r := fun t => coordinateSurrogate γ (g t) (w t).val (P t).mean-
      smoothedCoordinateSurrogate γ q (g t) (w t).val (u t).val
    cumulative r (n+1) ≤
      (Real.sqrt (birthBudget d D q+lam*H)+
        (∑ t ∈ Finset.range n, ‖(u (t+1)).val-(u t).val‖)/(Real.sqrt 2*Real.sqrt q))^2/lam-H := by
  let γ := curvature D G η
  have hγ : 0 < γ := curvature_pos D G η hD hG hη
  let lam := γ/2
  have hlam : 0 < lam := by dsimp [lam]; positivity
  let P := gaussianHistory W hD w0 lam q hlam.le hq g w
  let r := fun t => coordinateSurrogate γ (g t) (w t).val (P t).mean-
    smoothedCoordinateSurrogate γ q (g t) (w t).val (u t).val
  change cumulative r (n+1) ≤ _
  change ∀ k ≤ n+1, -H ≤ cumulative r k at hdraw
  have htwo : 2*lam = γ := by dsimp [lam]; ring
  have hstep (t : ℕ) (ht : t ≤ n) : lam*r t ≤
      (P t).potential q (u t).val-(P (t+1)).potential q (u t).val := by
    have hm := gaussianHistory_feasible W hD w0 lam q hlam.le hq g w t
    have hb := coordinate_curvature_bound W hD hG hη (g t) (hg t ht)
      ⟨WithLp.toLp 2 (P t).mean, hm⟩ (w t)
    have hs := (P t).history_one_step W lam q hlam.le hq (g t) (w t).val (u t)
      (by rw [htwo]; exact hb)
    rw [htwo] at hs
    exact hs
  have hmove (t : ℕ) (_ht : t < n) :
      Real.sqrt ((P (t+1)).potential q (u (t+1)).val) ≤
      Real.sqrt ((P (t+1)).potential q (u t).val)+
        ‖(u (t+1)).val-(u t).val‖/(Real.sqrt 2*Real.sqrt q) :=
    (P t).history_movement W lam q hlam.le hq (g t) (w t).val (u t).val (u (t+1)).val
  have hh := shifted_drawdown_bound n r
    (fun t => (P t).potential q (u t).val) (fun t => (P (t+1)).potential q (u t).val)
    (fun t => ‖(u (t+1)).val-(u t).val‖/(Real.sqrt 2*Real.sqrt q))
    lam H (birthBudget d D q) hlam
    (fun t _ => (P t).potential_nonneg q hq _) (fun t _ => (P (t+1)).potential_nonneg q hq _)
    (fun t _ => by positivity) (isotropicGaussian_birth_bound W hD w0 (u 0) q hq)
    hdraw hstep hmove
  simpa only [← Finset.sum_div] using hh

end Paper254
#print axioms Paper254.gaussianHistory_drawdown
