import SparseBranches254

noncomputable section
namespace Paper254

theorem restart_budget_normalization (a B γ L Λ d₁ : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hγ : 0 < γ) (hL : 0 ≤ L)
    (hΛ : 0 ≤ Λ) (hd : 1 ≤ d₁)
    (hLmax : L ≤ 2*Λ) (haMax : a*(γ/2) ≤ 2*Λ) (hBmax : B ≤ d₁*Λ) :
    γ*restartThreshold L a B (γ/2) ≤ 1536*d₁*Λ^2 := by
  have hsum : a*(γ/2)+B ≤ 3*d₁*Λ := by
    nlinarith [mul_nonneg (show 0 ≤ d₁-1 by linarith) hΛ]
  have hsum0 : 0 ≤ a*(γ/2)+B := by positivity
  have he : γ*restartThreshold L a B (γ/2) = 256*L*(a*(γ/2)+B) := by
    unfold restartThreshold
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul hLmax hsum hsum0 (show 0 ≤ 2*Λ by positivity)
  nlinarith

theorem restart_static_normalization (a B γ L Λ d₁ : ℝ)
    (ha : 0 ≤ a) (hB : 0 ≤ B) (hγ : 0 < γ) (hL : 0 ≤ L)
    (hΛ : 0 ≤ Λ) (hd : 1 ≤ d₁)
    (hLmax : L ≤ 2*Λ) (haMax : a*(γ/2) ≤ 2*Λ) (hBmax : B ≤ d₁*Λ) :
    restartThreshold L a B (γ/2)/64 ≤ 24*d₁*Λ^2/γ := by
  have hh := restart_budget_normalization a B γ L Λ d₁ ha hB hγ hL hΛ hd hLmax haMax hBmax
  apply (le_div_iff₀ hγ).mpr
  nlinarith

theorem restart_root_ratio (H C γ Λ d₁ : ℝ)
    (hH : 0 ≤ H) (hC : 0 < C) (hγ : 0 < γ) (hΛ : 0 ≤ Λ) (hd : 0 ≤ d₁)
    (hHmax : γ*H ≤ 1536*d₁*Λ^2) (henergy : γ*H ≤ 2*C) :
    H/Real.sqrt C ≤ 64*Real.sqrt d₁*Λ/γ := by
  have hh0 : 0 ≤ γ*H := mul_nonneg hγ.le hH
  have h1 := mul_le_mul_of_nonneg_right hHmax hh0
  have h2 := mul_le_mul_of_nonneg_left henergy (show 0 ≤ 1536*d₁*Λ^2 by positivity)
  have he : (64*Real.sqrt d₁*Λ*Real.sqrt C)^2 = 4096*d₁*Λ^2*C := by
    simp only [mul_pow, Real.sq_sqrt hd, Real.sq_sqrt hC.le]
    ring
  have hs : (γ*H)^2 ≤ (64*Real.sqrt d₁*Λ*Real.sqrt C)^2 := by
    rw [he]
    nlinarith [mul_nonneg (show 0 ≤ 1024*d₁*Λ^2 by positivity) hC.le]
  have hroot : γ*H ≤ 64*Real.sqrt d₁*Λ*Real.sqrt C :=
    (sq_le_sq₀ hh0 (by positivity)).mp hs
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hC) hγ).mpr
  nlinarith

theorem restart_movement_normalization (a B γ L Λ d₁ τ : ℝ)
    (ha : 0 ≤ a) (hB : 0 < B) (hγ : 0 < γ) (hL : 0 < L)
    (hΛ : 0 ≤ Λ) (hd : 1 ≤ d₁) (hτ : 0 < τ)
    (hLmax : L ≤ 2*Λ) (haMax : a*(γ/2) ≤ 2*Λ) (hBmax : B ≤ d₁*Λ) :
    (restartThreshold L a B (γ/2)/64)/variationThreshold L a B (γ/2) (τ^2) ≤
      1024*Real.sqrt d₁*Λ^2/(γ*τ) := by
  let H := restartThreshold L a B (γ/2)
  let C := B+(γ/2)*H
  have hH : 0 < H := by dsimp [H, restartThreshold]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hHmax := restart_budget_normalization a B γ L Λ d₁ ha hB.le hγ hL.le hΛ hd hLmax haMax hBmax
  have henergy : γ*H ≤ 2*C := by dsimp [C]; nlinarith
  have hr := restart_root_ratio H C γ Λ d₁ hH.le hC hγ hΛ (by linarith) hHmax henergy
  have he : (H/64)/variationThreshold L a B (γ/2) (τ^2) = (8*L/τ)*(H/Real.sqrt C) := by
    unfold variationThreshold
    rw [Real.sqrt_sq hτ.le]
    change (H/64)/(τ*Real.sqrt C/(512*L)) = _
    field_simp
    ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 8*L/τ by positivity)
  have hl := mul_le_mul_of_nonneg_right hLmax (show 0 ≤ 512*Real.sqrt d₁*Λ/(γ*τ) by positivity)
  calc
    _ ≤ (8*L/τ)*(64*Real.sqrt d₁*Λ/γ) := hm
    _ ≤ 1024*Real.sqrt d₁*Λ^2/(γ*τ) := by
      convert hl using 1 <;> field_simp <;> ring

end Paper254
#print axioms Paper254.restart_static_normalization
#print axioms Paper254.restart_movement_normalization
