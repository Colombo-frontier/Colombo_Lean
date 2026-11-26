import GradientHessian.SelectorPortJets
import GradientHessian.SelectorPartitions

/-! Dimension-independent bounds for actual Bernoulli mass derivatives of
the literal selector ports. -/

namespace GradientHessian.SelectorMassBounds
open SelectorBernoulli SelectorProductDerivatives SelectorRawProduct SelectorProfileBounds
  SelectorPortBounds SelectorCoordinateBounds SelectorPortJets SelectorChainRule SelectorPartitions
open Classical
open scoped BigOperators
noncomputable section

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def partitionTerm (R : ℝ) (v : ι → E) (A : ι → F →L[ℝ] E) (x : F)
    {n : ℕ} (w : Fin n → F) (c : OrderedFinpartition n) (ω : ι → Bool) : ℝ :=
  iteratedFDeriv ℝ c.length (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
    (bitVector (coordinatePort R v A) ω x) (fun l i => bitSign (ω i)*
      iteratedFDeriv ℝ (c.partSize l) (coordinatePort R v A i) x (w ∘ c.emb l))

theorem regular_partition_bound {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A) (x : F)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → F) (c : OrderedFinpartition n)
    (hc : ∀ l, c.partSize l ≤ 2) :
    (∑ ω, |partitionTerm R v A x w c ω|) ≤
      6*portConstant^3/R^n*(∏ l, ‖w l‖) := by
  let p : ι → ℝ := fun i => coordinatePort R v A i x
  let a : Fin c.length → ι → ℝ := fun l i =>
    iteratedFDeriv ℝ (c.partSize l) (coordinatePort R v A i) x (w ∘ c.emb l)/varianceRoot (p i)
  let B : ℝ := portConstant^c.length/R^n*(∏ l, ‖w l‖)
  have hC : 0 ≤ portConstant := zero_le_one.trans portConstant_ge_one
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1 := coordinatePort_mem R v A x
  have hfactor (l : Fin c.length) (i : ι) : varianceRoot (p i)*a l i =
      iteratedFDeriv ℝ (c.partSize l) (coordinatePort R v A i) x (w ∘ c.emb l) := by
    exact (variance_div_factor (by positivity)
      (port_jet_relative hR v hv A x (c.partSize_pos l) (hc l) (w ∘ c.emb l) i)).1
  have he (ω : ι → Bool) : partitionTerm R v A x w c ω =
      iteratedFDeriv ℝ c.length (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
        (fun i => bitMass (p i) (ω i)) (fun l i => varianceRoot (p i)*a l i*bitSign (ω i)) := by
    unfold partitionTerm
    congr 1
    funext l i
    rw [hfactor]
    ring
  have hs : (∏ l, ∑ i, (a l i)^2) ≤ B^2 := by
    calc
      _ ≤ ∏ l, (portConstant/R^(c.partSize l))^2*(∏ j, ‖w (c.emb l j)‖)^2 := by
        apply Finset.prod_le_prod
        · intro l _
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        · intro l _
          exact port_jet_normalized_square_sum hR v hv A hA x (c.partSize_pos l) (hc l) (w ∘ c.emb l)
      _ = _ := by
        simp_rw [← mul_pow]
        rw [Finset.prod_pow, partition_scale_product c portConstant R (fun l => ‖w l‖)]
  simp_rw [he]
  refine (product_iteratedFDeriv_normalized_bound hp c.length a).trans ?_
  calc
    _ ≤ Real.sqrt (36*B^2) := Real.sqrt_le_sqrt
      (mul_le_mul (small_chaos_constant (c.length_le.trans hn)) hs
        (Finset.prod_nonneg (fun l _ => Finset.sum_nonneg (fun i _ => sq_nonneg _))) (by norm_num))
    _ = 6*B := by rw [show (36:ℝ)*B^2 = (6*B)^2 by ring, Real.sqrt_sq (by positivity)]
    _ ≤ _ := by
      have hpow : portConstant^c.length ≤ portConstant^3 :=
        pow_le_pow_right₀ portConstant_ge_one (c.length_le.trans hn)
      have h : 6*(portConstant^c.length/R^n*(∏ l, ‖w l‖)) ≤
          6*(portConstant^3/R^n*(∏ l, ‖w l‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (pow_nonneg hR.le _))
          (show 0 ≤ ∏ l, ‖w l‖ from Finset.prod_nonneg (fun l _ => norm_nonneg (w l))))
          (by norm_num : (0:ℝ) ≤ 6)
      convert h using 1; dsimp [B]; ring

theorem first_raw_general {p : ι → ℝ} (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    {k : ℕ} (hk : k = 1) (a : Fin k → ι → ℝ) {B : ℝ}
    (ha : ∀ l, (∑ i, |a l i|) ≤ B) :
    (∑ ω : ι → Bool, |iteratedFDeriv ℝ k (ContinuousMultilinearMap.mkPiAlgebra ℝ ι ℝ)
      (fun i => bitMass (p i) (ω i)) (fun l i => bitSign (ω i)*a l i)|) ≤ 2*B := by
  subst k
  have he (ω : ι → Bool) : (fun l i => bitSign (ω i)*a l i) =
      (fun _ : Fin 1 => fun i => a 0 i*bitSign (ω i)) := by
    funext l i
    rw [Subsingleton.elim l 0, mul_comm]
  simp_rw [he]
  exact (product_first_raw_bound hp (a 0)).trans (mul_le_mul_of_nonneg_left (ha 0) (by norm_num))

theorem third_sum_of_eq {R : ℝ} (hR : 0 < R) (v : ι → E) (hv : ∀ i, ‖v i‖ = 1)
    (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A) (x : F)
    {n : ℕ} (hn : n = 3) (w : Fin n → F) :
    (∑ i, |iteratedFDeriv ℝ n (coordinatePort R v A i) x w|) ≤
      portConstant/R^n*(∏ l, ‖w l‖) := by
  subst n
  exact port_jet_third_sum hR v hv A hA x w

theorem exceptional_partition_bound {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A) (x : F)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → F) (c : OrderedFinpartition n)
    (hc : ¬∀ l, c.partSize l ≤ 2) :
    (∑ ω, |partitionTerm R v A x w c ω|) ≤
      6*portConstant^3/R^n*(∏ l, ‖w l‖) := by
  obtain ⟨l, hl⟩ := not_forall.mp hc
  obtain ⟨rfl, hlen⟩ := big_part_singleton hn c l (by omega)
  have ha (j : Fin c.length) :
      (∑ i, |iteratedFDeriv ℝ (c.partSize j) (coordinatePort R v A i) x (w ∘ c.emb j)|) ≤
      portConstant/R^3*(∏ l, ‖w l‖) := by
    have hs := singleton_partSize c hlen j
    have h := third_sum_of_eq hR v hv A hA x hs (w ∘ c.emb j)
    simpa only [hs, Function.comp_apply, singleton_prod c hlen j (fun l => ‖w l‖)] using h
  have h := first_raw_general (coordinatePort_mem R v A x) hlen
    (fun l i => iteratedFDeriv ℝ (c.partSize l) (coordinatePort R v A i) x (w ∘ c.emb l)) ha
  refine h.trans ?_
  have hC := portConstant_ge_one
  have hp : 2*portConstant ≤ 6*portConstant^3 := by nlinarith [sq_nonneg portConstant]
  have ht : (2*portConstant/R^3)*(∏ l, ‖w l‖) ≤
      (6*portConstant^3/R^3)*(∏ l, ‖w l‖) := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hp (pow_nonneg hR.le 3))
      (show 0 ≤ ∏ l, ‖w l‖ from Finset.prod_nonneg (fun l _ => norm_nonneg (w l)))
  convert ht using 1; ring

def massConstant (n : ℕ) : ℝ := (Fintype.card (OrderedFinpartition n):ℝ)*6*portConstant^3

theorem mass_derivative_sum_bound {R : ℝ} (hR : 0 < R) (v : ι → E)
    (hv : ∀ i, ‖v i‖ = 1) (A : ι → F →L[ℝ] E) (hA : CoordinateContraction A) (x : F)
    {n : ℕ} (hn : n ≤ 3) (w : Fin n → F) :
    (∑ ω : ι → Bool, |iteratedFDeriv ℝ n
      (fun y => mass (fun i => coordinatePort R v A i y) ω) x w|) ≤
      massConstant n/R^n*(∏ l, ‖w l‖) := by
  simp_rw [mass_iteratedFDeriv (coordinatePort R v A) (coordinatePort_contDiff R v A) _ hn]
  calc
    _ ≤ ∑ ω : ι → Bool, ∑ c : OrderedFinpartition n, |partitionTerm R v A x w c ω| :=
      Finset.sum_le_sum (fun ω _ => Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ c : OrderedFinpartition n, ∑ ω : ι → Bool, |partitionTerm R v A x w c ω| := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _c : OrderedFinpartition n, 6*portConstant^3/R^n*(∏ l, ‖w l‖) := by
      apply Finset.sum_le_sum
      intro c _
      by_cases hc : ∀ l, c.partSize l ≤ 2
      · exact regular_partition_bound hR v hv A hA x hn w c hc
      · exact exceptional_partition_bound hR v hv A hA x hn w c hc
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, massConstant]; ring

end
end GradientHessian.SelectorMassBounds
