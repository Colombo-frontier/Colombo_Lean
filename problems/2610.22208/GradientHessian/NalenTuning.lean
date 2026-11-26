import GradientHessian.NalenConvergence

/-! Explicit absolute parameter choices for the proved NALEN
convergence bound. The averaging length remains an integer. -/

noncomputable section
namespace GradientHessian.Nalen
open scoped InnerProductSpace

def stepRadius (q : ℕ) : ℝ := 1/(64*(q : ℝ))
def stepSize (m q : ℕ) : ℝ := 4*(q : ℝ)/(m : ℝ)

theorem stepRadius_pos {q : ℕ} (hq : 1 ≤ q) : 0 < stepRadius q := by
  have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  unfold stepRadius
  positivity

theorem stepSize_pos {m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) : 0 < stepSize m q := by
  have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  unfold stepSize
  positivity

theorem stepSize_stable {m q : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) :
    8*(stepSize m q)^2*(2*(m : ℝ)*stepRadius q)^2 ≤ 1 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have he : 8*(stepSize m q)^2*(2*(m : ℝ)*stepRadius q)^2=(1 : ℝ)/8 := by
    unfold stepSize stepRadius
    field_simp
    ring
  rw [he]
  norm_num

theorem tuning_bound {m q K : ℕ} (hm : 1 ≤ m) (hq : 1 ≤ q) (hK : 1 ≤ K)
    (hmq : m ≤ q^3) {T : ℝ} (hTK : 256*T ≤ (K : ℝ)) :
    T/(stepRadius q*(K : ℝ)*(q : ℝ))+3*stepRadius q/(stepSize m q*(q : ℝ))+
      (stepRadius q)^2/4+(q : ℝ)^2*(stepRadius q)^2 ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hqpos : (0 : ℝ) < q := by linarith
  have hmqR : (m : ℝ) ≤ (q : ℝ)^3 := by exact_mod_cast hmq
  have he : T/(stepRadius q*(K : ℝ)*(q : ℝ))+3*stepRadius q/(stepSize m q*(q : ℝ))+
      (stepRadius q)^2/4+(q : ℝ)^2*(stepRadius q)^2 =
      64*T/(K : ℝ)+3*(m : ℝ)/(256*(q : ℝ)^3)+1/(16384*(q : ℝ)^2)+(1 : ℝ)/4096 := by
    unfold stepRadius stepSize
    field_simp
    ring
  rw [he]
  have h₁ : 64*T/(K : ℝ) ≤ (1 : ℝ)/4 := by
    apply (div_le_iff₀ hKpos).2
    linarith only [hTK]
  have h₂ : 3*(m : ℝ)/(256*(q : ℝ)^3) ≤ (3 : ℝ)/256 := by
    apply (div_le_iff₀ (show (0 : ℝ) < 256*(q : ℝ)^3 by positivity)).2
    nlinarith only [hmqR]
  have h₃ : (1 : ℝ)/(16384*(q : ℝ)^2) ≤ (1 : ℝ)/16384 := by
    apply (div_le_iff₀ (show (0 : ℝ) < 16384*(q : ℝ)^2 by positivity)).2
    nlinarith only [hqR]
  linarith only [h₁,h₂,h₃]

theorem output_stationary {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {N : ℕ} {s : Iterates E} {m q K : ℕ}
    (hs : ValidSteps f (stepRadius q) (stepSize m q) N s) (hf : ContDiff ℝ 2 f)
    (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) (hm : 1 ≤ m) (hq : 1 ≤ q)
    (hK : 1 ≤ K) (hmq : m ≤ q^3) (hKq : K*q ≤ N)
    (hBsym : ∀ n < N,∀ u v,⟪s.B n u,v⟫_ℝ=⟪u,s.B n v⟫_ℝ)
    (hB : ∀ n < N,‖s.B n-hessianOperator f (s.extrapolated (snapshotIndex m n))‖ ≤
      (m : ℝ)*stepRadius q)
    (out : E) (houtput : ∀ k < K,‖gradient f out‖ ≤ ‖gradient f (s.candidate q k)‖)
    {T : ℝ} (hbounded : BddBelow (Set.range f)) (hgap : f (s.x 0)-sInf (Set.range f) ≤ T)
    (hTK : 256*T ≤ (K : ℝ)) : ‖gradient f out‖ ≤ 1 :=
  (hs.output_gradient_bound hf hL m hm (stepSize_pos hm hq) (stepSize_stable hm hq)
    hBsym hB (stepRadius_pos hq) q K hq hK hKq out houtput hbounded hgap).trans
      (tuning_bound hm hq hK hmq hTK)

end GradientHessian.Nalen
