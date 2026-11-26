import Bilevel.ChiBoundedChainReceiverShapes

/-! Uniform derivatives of normalized receiver slopes for arbitrary scale
ratio in [0,1]. Weighted cutoff jets avoid any hp/h loss. -/
noncomputable section
namespace Bilevel.ChiBoundedChain.ReceiverJets

structure ProfileControl (B : ℝ) : Prop where
  one_le : 1≤B
  val : ∀ i t,|profile i t|≤B
  first : ∀ i t,|deriv (profile i) t|≤B
  second : ∀ i t,|iteratedDeriv 2 (profile i) t|≤B
  weighted_first : ∀ i t,|t*deriv (profile i) t|≤3*B
  weighted_second : ∀ i t,|t*iteratedDeriv 2 (profile i) t|≤3*B

theorem profile_control_exists : ∃ B : ℝ,ProfileControl B := by
  obtain ⟨B,hB,hb,hw⟩ := profiles_common_bound
  refine ⟨B,⟨hB,fun i t => ?_,fun i t => ?_,fun i t => ?_,fun i t => ?_,fun i t => ?_⟩⟩
  · simpa only [Fin.val_zero,iteratedDeriv_zero] using hb i 0 t
  · simpa only [Fin.val_one,iteratedDeriv_one] using hb i 1 t
  · exact hb i 2 t
  · simpa only [iteratedDeriv_one] using hw i 1 (by norm_num) (by norm_num) t
  · exact hw i 2 (by norm_num) (by norm_num) t

theorem product_bound (x y X Y : ℝ) (hX : 0≤X) (hx : |x|≤X) (hy : |y|≤Y) :
    |x*y|≤X*Y := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) hX

theorem weighted_affine_bound (a δ t y B : ℝ) (_hB : 0≤B)
    (ha : 0≤a) (ha1 : a≤1) (hδ : 0≤δ) (hδ1 : δ≤1)
    (hy : |y|≤B) (hweight : |(δ*t)*y|≤3*B) : |((a*t+1)*δ)*y|≤4*B := by
  have he : ((a*t+1)*δ)*y=a*((δ*t)*y)+δ*y := by ring
  rw [he]
  have h₁ := product_bound a ((δ*t)*y) 1 (3*B) zero_le_one (by simpa only [abs_of_nonneg ha] using ha1) hweight
  have h₂ := product_bound δ y 1 B zero_le_one (by simpa only [abs_of_nonneg hδ] using hδ1) hy
  exact (abs_add _ _).trans (by linarith)

theorem weighted_affine_square_bound (a δ t y B : ℝ) (hB : 0≤B)
    (ha : 0≤a) (ha1 : a≤1) (hδ : 0≤δ) (hδ1 : δ≤1)
    (hy : |y|≤B) (hweight : |(δ*t)*y|≤3*B) : |((a*t+1)*δ^2)*y|≤4*B := by
  have he : ((a*t+1)*δ^2)*y=δ*(((a*t+1)*δ)*y) := by ring
  rw [he]
  simpa only [one_mul] using product_bound δ (((a*t+1)*δ)*y) 1 (4*B) zero_le_one
    (by simpa only [abs_of_nonneg hδ] using hδ1)
    (weighted_affine_bound a δ t y B hB ha ha1 hδ hδ1 hy hweight)

theorem positiveShapeFirst_bound {B : ℝ} (h : ProfileControl B) (a δ t : ℝ)
    (ha : 0≤a) (ha1 : a≤1) (hδ : 0≤δ) (hδ1 : δ≤1) :
    |positiveShapeFirst a δ t|≤9*B^2 := by
  have hB : 0≤B := by linarith [h.one_le]
  have hj : |(a*t+1)*deriv (profile 0) t|≤4*B := by
    simpa only [one_mul,mul_one] using weighted_affine_bound a 1 t (deriv (profile 0) t) B hB ha ha1
      zero_le_one le_rfl (h.first 0 t) (by simpa only [one_mul] using h.weighted_first 0 t)
  have hk := weighted_affine_bound a δ t (deriv (profile 1) (δ*t)) B hB ha ha1 hδ hδ1
    (h.first 1 (δ*t)) (h.weighted_first 1 (δ*t))
  have h₀ : |a*profile 0 t*profile 1 (δ*t)|≤B^2 := by
    have hm := product_bound a (profile 0 t) 1 B zero_le_one
      (by simpa only [abs_of_nonneg ha] using ha1) (h.val 0 t)
    have hp := product_bound (a*profile 0 t) (profile 1 (δ*t)) B B hB (by simpa using hm) (h.val 1 (δ*t))
    simpa only [pow_two] using hp
  have h₁ : |(a*t+1)*deriv (profile 0) t*profile 1 (δ*t)|≤4*B^2 := by
    convert product_bound _ _ (4*B) B (by positivity) hj (h.val 1 (δ*t)) using 1
    ring
  have h₂ : |(a*t+1)*profile 0 t*δ*deriv (profile 1) (δ*t)|≤4*B^2 := by
    have he : (a*t+1)*profile 0 t*δ*deriv (profile 1) (δ*t)=profile 0 t*(((a*t+1)*δ)*deriv (profile 1) (δ*t)) := by ring
    rw [he]
    convert product_bound _ _ B (4*B) hB (h.val 0 t) hk using 1
    ring
  have ht₀ := abs_add (a*profile 0 t*profile 1 (δ*t)) ((a*t+1)*deriv (profile 0) t*profile 1 (δ*t))
  have ht₁ := abs_add (a*profile 0 t*profile 1 (δ*t)+(a*t+1)*deriv (profile 0) t*profile 1 (δ*t))
    ((a*t+1)*profile 0 t*δ*deriv (profile 1) (δ*t))
  unfold positiveShapeFirst
  linarith only [h₀,h₁,h₂,ht₀,ht₁]

theorem unit_product_bound (a x y B : ℝ) (hB : 0≤B) (ha : |a|≤1) (hx : |x|≤B) (hy : |y|≤B) :
    |a*x*y|≤B^2 := by
  have hax := product_bound a x 1 B zero_le_one ha hx
  have hh := product_bound (a*x) y B B hB (by simpa using hax) hy
  simpa only [pow_two] using hh

theorem double_bound (x B : ℝ) (hx : |x|≤B) : |2*x|≤2*B := by
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  exact mul_le_mul_of_nonneg_left hx (by norm_num)

theorem sum_bound (x y B C : ℝ) (hx : |x|≤B) (hy : |y|≤C) : |x+y|≤B+C :=
  (abs_add _ _).trans (add_le_add hx hy)

theorem positiveShapeSecond_bound {B : ℝ} (h : ProfileControl B) (a δ t : ℝ)
    (ha : 0≤a) (ha1 : a≤1) (hδ : 0≤δ) (hδ1 : δ≤1) :
    |positiveShapeSecond a δ t|≤20*B^2 := by
  have hB : 0≤B := by linarith [h.one_le]
  have habs : |a|≤1 := by simpa only [abs_of_nonneg ha] using ha1
  have hδabs : |δ|≤1 := by simpa only [abs_of_nonneg hδ] using hδ1
  have hj₁ : |(a*t+1)*deriv (profile 0) t|≤4*B := by
    simpa only [one_mul,mul_one] using weighted_affine_bound a 1 t (deriv (profile 0) t) B hB ha ha1
      zero_le_one le_rfl (h.first 0 t) (by simpa only [one_mul] using h.weighted_first 0 t)
  have hj₂ : |(a*t+1)*iteratedDeriv 2 (profile 0) t|≤4*B := by
    simpa only [one_mul,mul_one] using weighted_affine_bound a 1 t (iteratedDeriv 2 (profile 0) t) B hB ha ha1
      zero_le_one le_rfl (h.second 0 t) (by simpa only [one_mul] using h.weighted_second 0 t)
  have hk₁ : |δ*deriv (profile 1) (δ*t)|≤B := by
    simpa only [one_mul] using product_bound δ _ 1 B zero_le_one hδabs (h.first 1 (δ*t))
  have hk₂ := weighted_affine_square_bound a δ t (iteratedDeriv 2 (profile 1) (δ*t)) B hB ha ha1 hδ hδ1
    (h.second 1 (δ*t)) (h.weighted_second 1 (δ*t))
  have h₀ : |2*a*deriv (profile 0) t*profile 1 (δ*t)|≤2*B^2 := by
    convert double_bound _ _ (unit_product_bound a _ _ B hB habs (h.first 0 t) (h.val 1 (δ*t))) using 1
    ring
  have h₁ : |2*a*profile 0 t*δ*deriv (profile 1) (δ*t)|≤2*B^2 := by
    convert double_bound _ _ (unit_product_bound a _ _ B hB habs (h.val 0 t) hk₁) using 1
    ring
  have h₂ : |(a*t+1)*iteratedDeriv 2 (profile 0) t*profile 1 (δ*t)|≤4*B^2 := by
    convert product_bound _ _ (4*B) B (by positivity) hj₂ (h.val 1 (δ*t)) using 1
    ring
  have h₃ : |2*(a*t+1)*deriv (profile 0) t*δ*deriv (profile 1) (δ*t)|≤8*B^2 := by
    convert double_bound _ _ (product_bound _ _ (4*B) B (by positivity) hj₁ hk₁) using 1 <;> ring
  have h₄ : |(a*t+1)*profile 0 t*δ^2*iteratedDeriv 2 (profile 1) (δ*t)|≤4*B^2 := by
    convert product_bound _ _ B (4*B) hB (h.val 0 t) hk₂ using 1 <;> ring
  have hs := sum_bound _ _ _ _ (sum_bound _ _ _ _ (sum_bound _ _ _ _ (sum_bound _ _ _ _ h₀ h₁) h₂) h₃) h₄
  change |positiveShapeSecond a δ t|≤_ at hs
  exact hs.trans_eq (by ring)

theorem negativeShapeFirst_bound {B : ℝ} (h : ProfileControl B) (δ t : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) : |negativeShapeFirst δ t|≤2*B^2 := by
  have hB : 0≤B := by linarith [h.one_le]
  have h₀ := product_bound _ _ B B hB (h.first 0 t) (h.val 2 (δ*t))
  have h₁ := unit_product_bound δ (profile 0 t) (deriv (profile 2) (δ*t)) B hB
    (by simpa only [abs_of_nonneg hδ] using hδ1) (h.val 0 t) (h.first 2 (δ*t))
  have he : profile 0 t*δ*deriv (profile 2) (δ*t)=δ*profile 0 t*deriv (profile 2) (δ*t) := by ring
  unfold negativeShapeFirst
  rw [he]
  exact (sum_bound _ _ _ _ h₀ h₁).trans_eq (by ring)

theorem negativeShapeSecond_bound {B : ℝ} (h : ProfileControl B) (δ t : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) : |negativeShapeSecond δ t|≤4*B^2 := by
  have hB : 0≤B := by linarith [h.one_le]
  have hδabs : |δ|≤1 := by simpa only [abs_of_nonneg hδ] using hδ1
  have hδsq : |δ^2|≤1 := by rw [abs_of_nonneg (sq_nonneg _)];exact pow_le_one₀ hδ hδ1
  have h₀ := product_bound _ _ B B hB (h.second 0 t) (h.val 2 (δ*t))
  have h₁ : |2*deriv (profile 0) t*δ*deriv (profile 2) (δ*t)|≤2*B^2 := by
    convert double_bound _ _ (unit_product_bound δ _ _ B hB hδabs (h.first 0 t) (h.first 2 (δ*t))) using 1
    ring
  have h₂ : |profile 0 t*δ^2*iteratedDeriv 2 (profile 2) (δ*t)|≤B^2 := by
    convert unit_product_bound (δ^2) _ _ B hB hδsq (h.val 0 t) (h.second 2 (δ*t)) using 1
    ring
  have hs := sum_bound _ _ _ _ (sum_bound _ _ _ _ h₀ h₁) h₂
  change |negativeShapeSecond δ t|≤_ at hs
  exact hs.trans_eq (by ring)

end Bilevel.ChiBoundedChain.ReceiverJets
