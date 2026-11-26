import Geode.ScalarPersistence

/-!
Scalar part of small-latitude contact routing (`prop:cd-small-latitude`).
The explicit hypotheses below are the Euclidean norm, inner-product and
normal-reserve facts that must be supplied by the geometric construction.
These results do not assert existence of a contact or of a convex carrier.
-/
namespace Geode
noncomputable section

/-- The norm identities and the lower Cauchy bound yield the reserve size. -/
theorem normal_reserve_size {μ a α β u v γ : ℝ}
    (hμ : 0 < μ) (ha : 1 ≤ a) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu2 : u ^ 2 = 1 - 1 / a ^ 2) (hv2 : v ^ 2 + β ^ 2 = 1)
    (hCauchy : -v * u ≤ γ)
    (hnorm : α ^ 2 = v ^ 2 + μ ^ 2 * u ^ 2 + 2 * μ * γ) :
    1 - μ ≤ α + β := by
  have hu1 : u ≤ 1 := by
    have : 0 ≤ 1 / a ^ 2 := by positivity
    nlinarith
  have hvβ : 1 ≤ v + β := by nlinarith [mul_nonneg hv hβ]
  have hdiff : v - μ * u ≤ α := by
    by_contra hn
    have hd : α < v - μ * u := lt_of_not_ge hn
    have hm := mul_nonneg (le_of_lt hμ) (show 0 ≤ γ + v * u by linarith)
    nlinarith [sq_nonneg (v - μ * u - α)]
  have hmu := mul_le_mul_of_nonneg_left hu1 hμ.le
  linarith

theorem eta_reserve_gt_mu {μ : ℝ} (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) :
    μ < eta μ * (1 - μ) := by
  have hd : 0 < 1 - μ ^ 2 := by nlinarith [mu_sq_lt_one hμ hμmax]
  unfold eta
  rw [div_mul_eq_mul_div, lt_div_iff₀ hd]
  have hp := mul_pos hμ (show 0 < (1 - μ) ^ 2 by nlinarith)
  nlinarith

/-- Current scalar certificate, derived directly from normal reserve and norms.
`u,v` are the norms of `u_V,q_V`; `γ` is their inner product.
The upper angle bound is the Cauchy bound for the two full unit vectors. -/
theorem routing_from_normal_reserve {μ θ a α β u v γ : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (ha : 1 ≤ a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu2 : u ^ 2 = 1 - 1 / a ^ 2) (hv2 : v ^ 2 + β ^ 2 = 1)
    (hCauchy : -v * u ≤ γ)
    (hnorm : α ^ 2 = v ^ 2 + μ ^ 2 * u ^ 2 + 2 * μ * γ)
    (hreserve : eta μ * α ≤ -a * (γ + μ * u ^ 2))
    (hangle : θ = -γ + β * eta μ / a) (hθhi : θ ≤ 1) :
    μ < θ ∧ eta μ ≤ ratio μ θ a := by
  have ha0 : a ≠ 0 := by linarith
  have hap : 0 < a := by linarith
  have he := eta_pos hμ hμmax
  have hsum := normal_reserve_size hμ ha hα hβ hu hv hu2 hv2 hCauchy hnorm
  have hB : angleB μ θ a = -a * (γ + μ * u ^ 2) + β * eta μ := by
    unfold angleB
    rw [hangle, hu2]
    field_simp
    ring
  have hBb : eta μ * (α + β) ≤ angleB μ θ a := by rw [hB]; nlinarith
  have hR : radicand μ θ a = α ^ 2 + β ^ 2 - 2 * μ * β * eta μ / a := by
    unfold radicand angleA
    rw [hnorm, hangle, hu2]
    have hvrewrite : v ^ 2 = 1 - β ^ 2 := by linarith
    rw [hvrewrite]
    field_simp
    ring
  have hRle : radicand μ θ a ≤ (α + β) ^ 2 := by
    rw [hR]
    have hm : 0 ≤ 2 * μ * β * eta μ / a := by positivity
    nlinarith [mul_nonneg hα hβ]
  have hmu_a : μ / a ≤ μ := div_le_self hμ.le ha
  have hBs : μ < angleB μ θ a := by
    have hm := mul_le_mul_of_nonneg_left hsum he.le
    linarith [eta_reserve_gt_mu hμ hμmax]
  have hθlo : μ < θ := by
    unfold angleB at hBs
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn)) hap.le
    linarith
  refine ⟨hθlo, (ratio_ge_iff hμ hμmax hθlo hθhi ha).2 ?_⟩
  have hBb2 := mul_self_le_mul_self (by positivity : 0 ≤ eta μ * (α + β)) hBb
  have hRmul := mul_le_mul_of_nonneg_left hRle (sq_nonneg (eta μ))
  nlinarith

/-- An interior zero normal gives an angle above the reference angle.
This proof uses only algebra and square-root-free norm identities. -/
theorem interior_angle_ge_tau {μ θ a β u : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (ha : 1 ≤ a)
    (ha' : a ≤ 1 / kappa μ) (hβ : 0 ≤ β)
    (hβ2 : β ^ 2 = 1 - μ ^ 2 * u ^ 2)
    (hangle : θ = μ * u ^ 2 + β * eta μ / a) :
    tau μ ≤ θ := by
  have hk := kappa_pos hμ hμmax
  have he := eta_pos hμ hμmax
  have ht := lt_trans hμ (tau_gt_mu hμ hμmax)
  have ht1 := tau_le_one hμ hμmax
  have hβ1 : β ≤ 1 := by nlinarith [sq_nonneg (μ * u)]
  have hβlower : 1 - μ ^ 2 * u ^ 2 ≤ β := by
    nlinarith [mul_nonneg hβ (show 0 ≤ 1 - β by linarith)]
  have het : eta μ * kappa μ = tau μ := by
    have hd : 1 - μ ^ 2 ≠ 0 := by nlinarith [mu_sq_lt_one hμ hμmax]
    have hp : 1 + μ ^ 2 ≠ 0 := by positivity
    unfold eta kappa tau
    field_simp
  have hka : a * kappa μ ≤ 1 := (le_div_iff₀ hk).1 ha'
  have hta : tau μ ≤ eta μ / a := by
    apply (le_div_iff₀ (by linarith : 0 < a)).2
    rw [← het]
    have := mul_le_mul_of_nonneg_left hka he.le
    nlinarith
  have hterm := mul_le_mul_of_nonneg_left hta hβ
  have hbterm := mul_le_mul_of_nonneg_left hβlower ht.le
  have hmut : μ * tau μ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left ht1 hμ.le
    linarith
  have hpos := mul_nonneg (show 0 ≤ μ * u ^ 2 by positivity)
    (show 0 ≤ 1 - μ * tau μ by linarith)
  rw [hangle]
  have hid : β * eta μ / a = β * (eta μ / a) := by ring
  rw [hid]
  nlinarith

/-- Zero public normal forces the source-gradient norm identities. -/
theorem zero_normal_identities {μ α β u v γ : ℝ} (hμ : 0 < μ)
    (hv2 : v ^ 2 + β ^ 2 = 1) (hCauchy : -v * u ≤ γ)
    (hnorm : α ^ 2 = v ^ 2 + μ ^ 2 * u ^ 2 + 2 * μ * γ) (hzero : α = 0) :
    β ^ 2 = 1 - μ ^ 2 * u ^ 2 ∧ γ = -μ * u ^ 2 := by
  have hm := mul_nonneg hμ.le (show 0 ≤ γ + v * u by linarith)
  have hs : (v - μ * u) ^ 2 = 0 := by rw [hzero] at hnorm; nlinarith [sq_nonneg (v - μ * u)]
  have hv : v = μ * u := sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
  have hg : μ * (γ + μ * u ^ 2) = 0 := by rw [hzero, hv] at hnorm; nlinarith
  have hg' : γ + μ * u ^ 2 = 0 := (mul_eq_zero.mp hg).resolve_left (ne_of_gt hμ)
  constructor
  · rw [hv] at hv2
    nlinarith
  · linarith

/-- Complete scalar future-persistence conclusion of small-latitude routing.
The strict-interior zero-normal property is an explicit geometric input. -/
theorem routing_all_future {μ θ a α β u v γ : ℝ}
    (hμ : 0 < μ) (hμmax : μ ≤ 1 / 16) (ha : 1 ≤ a)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu2 : u ^ 2 = 1 - 1 / a ^ 2) (hv2 : v ^ 2 + β ^ 2 = 1)
    (hCauchy : -v * u ≤ γ)
    (hnorm : α ^ 2 = v ^ 2 + μ ^ 2 * u ^ 2 + 2 * μ * γ)
    (hreserve : eta μ * α ≤ -a * (γ + μ * u ^ 2))
    (hangle : θ = -γ + β * eta μ / a) (hθhi : θ ≤ 1)
    (hInterior : a < 1 / kappa μ → α = 0) :
    μ < θ ∧ ∀ a' : ℝ, a ≤ a' → eta μ ≤ ratio μ θ a' := by
  obtain ⟨hθlo, hcurrent⟩ := routing_from_normal_reserve hμ hμmax ha hα hβ hu hv
    hu2 hv2 hCauchy hnorm hreserve hangle hθhi
  refine ⟨hθlo, ?_⟩
  intro a' haa'
  by_cases hright : 1 / kappa μ ≤ a
  · exact right_branch_persistence hμ hμmax hθlo hθhi hright hcurrent haa'
  · have hint : a < 1 / kappa μ := lt_of_not_ge hright
    obtain ⟨hb2, hg⟩ := zero_normal_identities hμ hv2 hCauchy hnorm (hInterior hint)
    have hangle' : θ = μ * u ^ 2 + β * eta μ / a := by rw [hangle, hg]; ring
    have ht := interior_angle_ge_tau hμ hμmax ha hint.le hβ hb2 hangle'
    exact angle_threshold hμ hμmax ht hθhi (ha.trans haa')

end
end Geode

