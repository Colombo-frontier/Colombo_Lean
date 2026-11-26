import GradientHessian.NalenAveraging
import GradientHessian.NalenBlockEnergy
import GradientHessian.NalenPrediction
import GradientHessian.NalenDirection

/-! Actual online-to-nonconvex conversion for the NALEN iterates. The
bound follows from proved block regret, midpoint descent, and averaging;
no convergence or stationarity conclusion is assumed. -/

noncomputable section
namespace GradientHessian.Nalen
open Set
open scoped InnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {D η : ℝ} {N : ℕ} {s : Iterates E}
variable (hs : ValidSteps f D η N s) (hf : ContDiff ℝ 2 f)
  (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) (m : ℕ) (hm : 1 ≤ m)
  (hη : 0 < η) (hstep : 8*η^2*(2*(m : ℝ)*D)^2 ≤ 1)
  (hBsym : ∀ n < N,∀ u v,⟪s.B n u,v⟫_ℝ=⟪u,s.B n v⟫_ℝ)
  (hB : ∀ n < N,‖s.B n-hessianOperator f (s.extrapolated (snapshotIndex m n))‖ ≤ (m : ℝ)*D)

include hs hf hL hm hη hstep hBsym hB in
theorem ValidSteps.block_stationarity (q k : ℕ) (hq : 1 ≤ q) (hkq : k*q+q ≤ N) :
    D*(q : ℝ)*‖gradient f (s.candidate q k)‖ ≤
      3*D^2/η+f (s.x (k*q))-f (s.x (k*q+q))+(q : ℝ)*D^3/4+(q : ℝ)^3*D^3 := by
  let G := ∑ j ∈ Finset.range q,gradient f (s.queryPoint (k*q+j))
  let u := descentDirection D G
  have hu : ‖u‖ ≤ D := descentDirection_norm hs.radius_nonneg G
  have hr := hs.block_regret hf hL m hm hη hstep hBsym hB (k*q) q hkq u hu
  have he : (∑ j ∈ Finset.range q,⟪gradient f (s.queryPoint (k*q+j)),s.δ (k*q+j+1)-u⟫_ℝ)=
      (∑ j ∈ Finset.range q,⟪gradient f (s.queryPoint (k*q+j)),s.δ (k*q+j+1)⟫_ℝ)+D*‖G‖ := by
    simp only [inner_sub_right,Finset.sum_sub_distrib,← sum_inner]
    change _-⟪G,descentDirection D G⟫_ℝ=_
    rw [descentDirection_inner]
    ring
  rw [he] at hr
  have henergy := hs.block_energy hf hL (k*q) q hkq
  have havg := mul_le_mul_of_nonneg_left (hs.candidate_gradient_norm hf hL q k hq hkq) hs.radius_nonneg
  change D*((q : ℝ)*‖gradient f (s.candidate q k)‖) ≤ D*(‖G‖+(q : ℝ)^3*D^2) at havg
  nlinarith only [hr,henergy,havg]

include hs hf hL hm hη hstep hBsym hB in
theorem ValidSteps.total_stationarity (q K : ℕ) (hq : 1 ≤ q) (hKq : K*q ≤ N) :
    D*(q : ℝ)*(∑ k ∈ Finset.range K,‖gradient f (s.candidate q k)‖) ≤
      (K : ℝ)*(3*D^2/η+(q : ℝ)*D^3/4+(q : ℝ)^3*D^3)+
        f (s.x 0)-f (s.x (K*q)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hk : K*q+q ≤ N := by simpa only [Nat.succ_mul] using hKq
    have hprev := ih (by omega)
    have hnext := hs.block_stationarity hf hL m hm hη hstep hBsym hB q K hq hk
    rw [Finset.sum_range_succ]
    simp only [Nat.cast_add,Nat.cast_one,Nat.succ_mul] at hprev hnext ⊢
    nlinarith only [hprev,hnext]

include hs hf hL hm hη hstep hBsym hB in
theorem ValidSteps.output_gradient_bound (hD : 0 < D) (q K : ℕ) (hq : 1 ≤ q)
    (hK : 1 ≤ K) (hKq : K*q ≤ N) (out : E)
    (houtput : ∀ k < K,‖gradient f out‖ ≤ ‖gradient f (s.candidate q k)‖)
    {T : ℝ} (hbounded : BddBelow (range f)) (hgap : f (s.x 0)-sInf (range f) ≤ T) :
    ‖gradient f out‖ ≤ T/(D*(K : ℝ)*(q : ℝ))+3*D/(η*(q : ℝ))+D^2/4+(q : ℝ)^2*D^2 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hsum : (K : ℝ)*‖gradient f out‖ ≤ ∑ k ∈ Finset.range K,‖gradient f (s.candidate q k)‖ := by
    have h := Finset.sum_le_sum (s := Finset.range K) (fun k hk => houtput k (Finset.mem_range.mp hk))
    simpa using h
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ D*(q : ℝ) by positivity)
  have ht := hs.total_stationarity hf hL m hm hη hstep hBsym hB q K hq hKq
  have hl : sInf (range f) ≤ f (s.x (K*q)) := csInf_le hbounded (mem_range_self _)
  have he : T/(D*(K : ℝ)*(q : ℝ))+3*D/(η*(q : ℝ))+D^2/4+(q : ℝ)^2*D^2 =
      (T+(K : ℝ)*(3*D^2/η+(q : ℝ)*D^3/4+(q : ℝ)^3*D^3))/(D*(K : ℝ)*(q : ℝ)) := by
    field_simp
    ring
  rw [he]
  apply (le_div_iff₀ (show 0 < D*(K : ℝ)*(q : ℝ) by positivity)).2
  nlinarith only [hmul,ht,hl,hgap]

end GradientHessian.Nalen
