import Bilevel.CachedOuterCostBound
import Bilevel.CachedParameterCost

/-! Explicit cost comparison with the source's general cached-gradient rate.
The natural algorithm counts and initialization logarithm are retained. -/
noncomputable section
namespace Bilevel.CachedCostRate
open CachedOuterProcedure CachedParameterChoice CachedBudgetCalibration

private theorem weighted_components {N B s sa bg bf d v w g f : ℝ}
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hBN : B ≤ 2*N) (hd : 0 ≤ d) (hv : 0 ≤ v)
    (hs : s ≤ d+v) (hsa : sa ≤ d+v+w) (hg : bg ≤ 1+g) (hf : bf ≤ 1+f) :
    N*(2*s+2*bg)+2560*B*(sa+bf) ≤
      N*(5122*d+5122*v+2+2*g)+2560*B*(1+f+w) := by
  have h1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*N)
  have h2 := mul_le_mul_of_nonneg_left hsa (by positivity : 0 ≤ 2560*B)
  have h3 := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ 2*N)
  have h4 := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2560*B)
  have h5 := mul_le_mul_of_nonneg_right hBN hd
  have h6 := mul_le_mul_of_nonneg_right hBN hv
  nlinarith

theorem refresh_factor_le_twice_count {Λ La Δ ε : ℝ}
    (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) :
    1+La*Δ/ε^2 ≤ 2*(outerCount Λ Δ ε:ℝ) := by
  have hN : (1:ℝ) ≤ outerCount Λ Δ ε := by exact_mod_cast outerCount_pos Λ Δ ε
  have hh := outerCount_horizon (Λ := Λ) (Δ := Δ) hε
  have hd := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hLaΛ hΔ) (sq_nonneg ε)
  have hratio : Λ*Δ/ε^2 ≤ (outerCount Λ Δ ε:ℝ)/32 := by
    apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  linarith

def core (μ Lf Lg E Λ La Δ ε D σf σg : ℝ) : ℝ :=
  let k := Lg/μ
  let a := anchorRadius Lf Lg k E ε
  (1+Λ*Δ/ε^2)*(1+Real.sqrt k*CachedOracleCost.initializationLog μ Lg D a+
      k^2*σg^2/(ε^2*(tilt E ε)^2)) +
    (1+La*Δ/ε^2)*(1+(1+k)^2*σf^2/ε^2+(1+k)^2*Lf^2*σg^2/(μ^2*ε^2))

theorem publicCost_explicit {μ Lf Lg E Λ La Δ ε D σf σg : ℝ}
    (hμ : 0 < μ) (hμg : μ ≤ Lg) (hLf : 0 ≤ Lf) (hE : 0 ≤ E)
    (hLa : 0 ≤ La) (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (q : ℕ) :
    let k := Lg/μ
    let r := lowerRadius Lg E ε
    let a := anchorRadius Lf Lg k E ε
    let C := Real.log 4+1
    let d := 2*C*CachedOracleCost.initializationLog μ Lg D a*Real.sqrt k
    let v := 4608*C*σg^2/(μ^2*r^2)
    let w := 4608*C*(4096*(1+k)^2*Lf^2*σg^2/(μ^2*ε^2))
    publicCost μ Lg σf σg D r a (gradientRadius E ε) (upperRadius k ε) Λ La Δ ε q ≤
      q*((outerCount Λ Δ ε:ℝ)*(5122*d+5122*v+2+288*σg^2/(gradientRadius E ε)^2) +
        2560*(1+La*Δ/ε^2)*(1+144*σf^2/(upperRadius k ε)^2+w)) := by
  dsimp only
  let k := Lg/μ
  let r := lowerRadius Lg E ε
  let a := anchorRadius Lf Lg k E ε
  let C := Real.log 4+1
  let d := 2*C*CachedOracleCost.initializationLog μ Lg D a*Real.sqrt k
  let v := 4608*C*σg^2/(μ^2*r^2)
  let w := 4608*C*(4096*(1+k)^2*Lf^2*σg^2/(μ^2*ε^2))
  have hLg : 0 < Lg := hμ.trans_le hμg
  have hk : 0 ≤ k := div_nonneg hLg.le hμ.le
  have ha : 0 < a := anchorRadius_pos hLf hLg hk hE hε
  have har : a ≤ r := anchorRadius_le_lower Lf Lg k E ε
  obtain ⟨hα,hα1,hrel⟩ := AcceleratedInner.square_root_parameter hμ hμg
  have hC : 0 ≤ C := by dsimp [C]; have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); linarith
  have hd : 0 ≤ d := by
    have := CachedOracleCost.initializationLog_nonneg (R := D) (a := a) hμ hLg.le
    dsimp [d]
    positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hdet : 2*(Real.log 4+1)*CachedOracleCost.initializationLog μ Lg D a / Real.sqrt (μ/Lg) = d := by
    dsimp [d,C,k]
    rw [div_eq_mul_inv,← Real.sqrt_inv,inv_div]
  have hs := CachedOracleCost.solve_cost (σ := σg) (R := D) hμ hLg hμg hα hα1 hrel ha har
  have hsa := CachedOracleCost.solve_cost (σ := σg) (R := D) hμ hLg hμg hα hα1 hrel ha le_rfl
  rw [hdet] at hs hsa
  have hvA := mul_le_mul_of_nonneg_left (anchor_variance_split Lf Lg k E ε μ σg)
    (by positivity : 0 ≤ 4608*C)
  have hsa' : (StatefulAccelerated.solveCalls μ Lg (Real.sqrt (μ/Lg)) σg D (a/12):ℝ) ≤ d+v+w := by
    have hvA' : 4608*C*σg^2/(μ^2*a^2) ≤ v+w := by
      convert hvA using 1
      · dsimp [a]; ring
      · dsimp [v,w,r]; ring
    exact hsa.trans ((add_le_add_left hvA' d).trans (by ring_nf; rfl))
  have hg := CachedOracleCost.batch_cost σg (gradientRadius E ε)
  have hf := CachedOracleCost.batch_cost σf (upperRadius k ε)
  have hh := weighted_components (N := (outerCount Λ Δ ε:ℝ))
    (B := 1+La*Δ/ε^2) (d := d) (v := v) (w := w)
    (Nat.cast_nonneg _) (by positivity) (refresh_factor_le_twice_count hLaΛ hΔ hε)
    hd hv hs hsa' hg hf
  have hq := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg q)
  unfold publicCost estimatorCalls anchorCalls
  push_cast
  convert hq using 1 <;> ring

private theorem coefficients_bound {N A B C I Z W U V : ℝ}
    (hN : 0 ≤ N) (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : N ≤ 32*A)
    (hC : C ≤ 4) (hI : 0 ≤ I) (hZ : 0 ≤ Z) (hW : W ≤ Z)
    (hU : 0 ≤ U) (hV : 0 ≤ V) :
    N*(5122*(2*C*I)+5122*(4608*C*4096*Z)+2+288*4096*W) +
      2560*B*(1+144*4096*U+4608*C*4096*V) ≤
      100000000000000*(A*(1+I+Z)+B*(1+U+V)) := by
  have hCI := mul_le_mul_of_nonneg_right hC hI
  have hCZ := mul_le_mul_of_nonneg_right hC hZ
  have hCV := mul_le_mul_of_nonneg_right hC hV
  have hfirst : 5122*(2*C*I)+5122*(4608*C*4096*Z)+2+288*4096*W ≤
      400000000000*(1+I+Z) := by nlinarith
  have hsecond : 1+144*4096*U+4608*C*4096*V ≤ 80000000*(1+U+V) := by nlinarith
  have h1 := mul_le_mul_of_nonneg_left hfirst hN
  have h2 := mul_le_mul_of_nonneg_left hsecond (by positivity : 0 ≤ 2560*B)
  have h3 := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 400000000000*(1+I+Z))
  have h4 : 0 ≤ A*(1+I+Z) := by positivity
  have h5 : 0 ≤ B*(1+U+V) := by positivity
  nlinarith

/-- Actual public call budget has exactly the source general-rate structure.
The constant is deliberately loose and numerical. Initialization enters only
through the deterministic logarithm in `core`. -/
theorem publicCost_le_core {μ Lf Lg E Λ La Δ ε D σf σg : ℝ}
    (hμ : 0 < μ) (hμg : μ ≤ Lg) (hLf : 0 ≤ Lf) (hE : 0 ≤ E)
    (hΛ : 0 < Λ) (hLa : 0 ≤ La) (hLaΛ : La ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (q : ℕ) :
    publicCost μ Lg σf σg D (lowerRadius Lg E ε) (anchorRadius Lf Lg (Lg/μ) E ε)
      (gradientRadius E ε) (upperRadius (Lg/μ) ε) Λ La Δ ε q ≤
        100000000000000*q*core μ Lf Lg E Λ La Δ ε D σf σg := by
  let k := Lg/μ
  let a := anchorRadius Lf Lg k E ε
  let I := Real.sqrt k*CachedOracleCost.initializationLog μ Lg D a
  let Z := k^2*σg^2/(ε^2*(tilt E ε)^2)
  let W := σg^2/(ε^2*(tilt E ε)^2)
  let U := (1+k)^2*σf^2/ε^2
  let V := (1+k)^2*Lf^2*σg^2/(μ^2*ε^2)
  have hLg : 0 < Lg := hμ.trans_le hμg
  have hk : 1 ≤ k := (one_le_div hμ).mpr hμg
  have hI : 0 ≤ I := mul_nonneg (Real.sqrt_nonneg _)
    (CachedOracleCost.initializationLog_nonneg hμ hLg.le)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : W ≤ Z := by
    have hh := mul_le_mul_of_nonneg_right (one_le_pow₀ hk : 1 ≤ k^2) (sq_nonneg σg)
    exact div_le_div_of_nonneg_right (by simpa only [one_mul] using hh) (by positivity)
  have hn : (outerCount Λ Δ ε:ℝ) ≤ 32*(1+Λ*Δ/ε^2) :=
    (outerCount_upper hΛ hΔ hε).trans (by ring_nf; linarith)
  have hC : Real.log 4+1 ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
    linarith
  have hc := coefficients_bound (N := (outerCount Λ Δ ε:ℝ))
    (A := 1+Λ*Δ/ε^2) (B := 1+La*Δ/ε^2) (C := Real.log 4+1)
    (I := I) (Z := Z) (W := W) (U := U) (V := V)
    (Nat.cast_nonneg _) (by positivity) (by positivity) hn hC hI hZ hW hU hV
  have hq := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg q)
  have hp := publicCost_explicit (σf := σf) (σg := σg) (D := D) hμ hμg hLf hE hLa hLaΛ hΔ hε q
  dsimp only at hp
  have hlow := lower_variance_identity Lg E ε μ σg
  have hgrad := gradient_variance_identity E ε σg
  have hupp := upper_variance_identity k ε σf
  have hv : 4608*(Real.log 4+1)*σg^2/(μ^2*(lowerRadius Lg E ε)^2) =
      4608*(Real.log 4+1)*4096*Z := by
    rw [show 4608*(Real.log 4+1)*σg^2/(μ^2*(lowerRadius Lg E ε)^2) =
      4608*(Real.log 4+1)*(σg^2/(μ^2*(lowerRadius Lg E ε)^2)) by ring,hlow]
    dsimp [Z,k]
    ring
  have hg : 288*σg^2/(gradientRadius E ε)^2 = 288*4096*W := by
    rw [show 288*σg^2/(gradientRadius E ε)^2 = 288*(σg^2/(gradientRadius E ε)^2) by ring,hgrad]
    dsimp [W]
    ring
  have hf : 144*σf^2/(upperRadius (Lg/μ) ε)^2 = 144*4096*U := by
    rw [show 144*σf^2/(upperRadius (Lg/μ) ε)^2 = 144*(σf^2/(upperRadius k ε)^2) by dsimp [k]; ring,hupp]
    dsimp [U]
    ring
  rw [hv,hg,hf] at hp
  apply hp.trans
  convert hq using 1 <;> dsimp [core,I,Z,W,U,V,a,k] <;> ring

end Bilevel.CachedCostRate
