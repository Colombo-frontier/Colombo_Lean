import Bilevel.ChiFineCouplingBounds
import Bilevel.ChiCoarseGradient

/-! Fine normal-coupling estimates for any actual finite data object with
the source schedule. This allows the proved ancestor-selected data to use
the same mixed-derivative argument as the latent frontier. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainSchedule SmallGapLiftSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem generic_couplingTerm_bounds (P : Parameters) (D : CompensatedMean.Data (E:=E))
    (hJ : D.J=levels P.θ) (hwidth : ∀ i,D.w i=width P.c P.β P.θ i) (B : ℝ) (hB : 1 ≤ B) (j : ℕ) (hj : j ≤ levels P.θ)
    (y : CompensatedMean.LowerSpace E)
    (hb : |D.e j (CompensatedMean.uProj E y)| ≤ B*P.amplitude*P.θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (D.e j) (CompensatedMean.uProj E y)‖ ≤
        B*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ j)^k.val)) :
    ‖iteratedFDeriv ℝ 2 (D.couplingTerm j) y‖ ≤ 4*C*B*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 (D.couplingTerm j) y‖ ≤ 8*C*B*P.ℓ*P.θ/P.c^2 := by
  have hjD : j ≤ D.J := by rw [hJ]; exact hj
  let d := pieceResolution P.c 1 P.θ j
  let w := width P.c 1 P.θ j
  let e := P.θ^(-amplitudeExponent j)
  have hd : 0 < d := pieceResolution_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  have hw : 0 < w := width_pos P.c 1 P.θ P.c_pos (by norm_num) P.θ_ge_one j
  have hβ := P.β_pos
  have ha := P.amplitude_nonneg
  have hℓ := P.ell_nonneg
  have hB0 : 0 ≤ B := by linarith
  have hC := C_pos
  have he : 0 ≤ e := Real.rpow_nonneg (by linarith [P.θ_ge_one]) _
  have hdp : pieceResolution P.c P.β P.θ j = P.β*d := by dsimp [d,pieceResolution]; ring
  have hwp : D.w j = P.β*w := by rw [hwidth j]; dsimp [w,width]; ring
  have h1 : ‖iteratedFDeriv ℝ 1 (D.e j) (CompensatedMean.uProj E y)‖ ≤ B*P.amplitude/P.β := by
    simpa only [Fin.val_zero,zero_add,pow_zero,mul_one] using hb.2 0
  have h2 : ‖iteratedFDeriv ℝ 2 (D.e j) (CompensatedMean.uProj E y)‖ ≤ B*P.amplitude/(P.β*(P.β*d)) := by
    simpa only [Fin.val_one,pow_one,hdp] using hb.2 1
  have h3 : ‖iteratedFDeriv ℝ 3 (D.e j) (CompensatedMean.uProj E y)‖ ≤ B*P.amplitude/(P.β*(P.β*d)^2) := by
    simpa only [hdp] using hb.2 2
  have ht2 := D.couplingTerm_second_bound j hjD y (B*P.amplitude*e) (B*P.amplitude/P.β)
    (B*P.amplitude/(P.β*(P.β*d))) (by positivity) (by positivity) (by positivity) hb.1 h1 h2
  have ht3 := D.couplingTerm_third_bound j hjD y (B*P.amplitude*e) (B*P.amplitude/P.β)
    (B*P.amplitude/(P.β*(P.β*d))) (B*P.amplitude/(P.β*(P.β*d)^2))
    (by positivity) (by positivity) (by positivity) (by positivity) hb.1 h1 h2 h3
  rw [hwp] at ht2 ht3
  have hs2 := second_weight_sum P.c P.θ P.c_pos (by linarith [P.c_small]) P.θ_ge_one j hj
  have hs3 := third_weight_sum P.c P.θ P.c_pos (by linarith [P.c_small]) P.θ_ge_one j hj
  change e/w+2+w/d ≤ 4*Real.sqrt P.θ/P.c at hs2
  change e/w^2+3/w+3/d+w/d^2 ≤ 8*P.θ/P.c^2 at hs3
  constructor
  · have hid : C*(B*P.amplitude*e/(P.β*w)+2*(B*P.amplitude/P.β)+
        B*P.amplitude/(P.β*(P.β*d))*(P.β*w)) =
        (C*B*P.ℓ*P.β)*(e/w+2+w/d) := by
      dsimp [Parameters.amplitude]
      field_simp
      ring
    rw [hid] at ht2
    exact ht2.trans ((mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ C*B*P.ℓ*P.β)).trans_eq (by ring))
  · have hid : C*(B*P.amplitude*e/(P.β*w)^2+3*(B*P.amplitude/P.β)/(P.β*w)+
        3*(B*P.amplitude/(P.β*(P.β*d)))+B*P.amplitude/(P.β*(P.β*d)^2)*(P.β*w)) =
        (C*B*P.ℓ)*(e/w^2+3/w+3/d+w/d^2) := by
      dsimp [Parameters.amplitude]
      field_simp
      ring
    rw [hid] at ht3
    exact ht3.trans ((mul_le_mul_of_nonneg_left hs3 (by positivity : 0 ≤ C*B*P.ℓ)).trans_eq (by ring))


theorem generic_coupling_bounds (P : Parameters) (D : CompensatedMean.Data (E:=E))
    (hJ : D.J=levels P.θ) (hwidth : ∀ i,D.w i=width P.c P.β P.θ i)
    (B : ℝ) (hB : 1≤B)
    (hb : ∀ j,j≤D.J → ∀ x,|D.e j x|≤B*P.amplitude*P.θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (D.e j) x‖≤
        B*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ j)^k.val))
    (hoverlap : ∀ x,(D.activePieces x).card≤3) (y : CompensatedMean.LowerSpace E) :
    ‖iteratedFDeriv ℝ 1 D.coupling y‖≤6*C*B*P.ℓ*P.β^2 ∧
    ‖iteratedFDeriv ℝ 2 D.coupling y‖≤12*C*B*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
    ‖iteratedFDeriv ℝ 3 D.coupling y‖≤24*C*B*P.ℓ*P.θ/P.c^2 := by
  have hB0 : 0≤B := by linarith
  have hell := P.ell_nonneg
  have hβ := P.β_pos
  have hc := P.c_pos
  have hθ : 0≤P.θ := by linarith [P.θ_ge_one]
  have hC := C_pos
  have ha := P.amplitude_nonneg
  have ht (j : ℕ) (hj : j≤D.J) := generic_couplingTerm_bounds P D hJ hwidth B hB j
    (by rwa [← hJ]) y (hb j hj _)
  have hfirst (j : ℕ) (hj : j≤D.J) : ‖iteratedFDeriv ℝ 1 (D.couplingTerm j) y‖≤2*C*B*P.amplitude := by
    have hh := hb j hj (CompensatedMean.uProj E y)
    have he : 0≤amplitudeExponent j := by
      unfold amplitudeExponent
      split_ifs
      · exact le_rfl
      · exact aExponent_nonneg _
    have hp : P.θ^(-amplitudeExponent j)≤1 :=
      Real.rpow_le_one_of_one_le_of_nonpos P.θ_ge_one (neg_nonpos.mpr he)
    have h0 : |D.e j (CompensatedMean.uProj E y)|≤B*P.amplitude :=
      hh.1.trans (mul_le_of_le_one_right (mul_nonneg hB0 P.amplitude_nonneg) hp)
    have h1 : ‖iteratedFDeriv ℝ 1 (D.e j) (CompensatedMean.uProj E y)‖≤B*P.amplitude/P.β := by
      simpa only [Fin.val_zero,zero_add,pow_zero,mul_one] using hh.2 0
    have hwβ : D.w j≤P.β := by
      rw [hwidth]
      linarith [P.normal_width_small j]
    have hr := ChiCoarse.extension_first_jet (D.e_smooth j) (D.w_pos j hj)
      (by positivity) (by positivity) y h0 h1
    apply hr.trans
    have hm : (B*P.amplitude/P.β)*D.w j≤B*P.amplitude := by
      apply (mul_le_mul_of_nonneg_left hwβ (by positivity : 0≤B*P.amplitude/P.β)).trans_eq
      field_simp
    have hh := mul_le_mul_of_nonneg_left (show B*P.amplitude+(B*P.amplitude/P.β)*D.w j≤
      2*(B*P.amplitude) by linarith) C_pos.le
    exact hh.trans_eq (by ring)
  constructor
  · exact (D.coupling_jet_bound y 1 (by norm_num) (2*C*B*P.amplitude)
      (by have := P.amplitude_nonneg; positivity) (hoverlap _) hfirst).trans_eq
      (by dsimp [Parameters.amplitude];ring)
  constructor
  · exact (D.coupling_jet_bound y 2 (by norm_num) (4*C*B*P.ℓ*P.β*Real.sqrt P.θ/P.c)
      (by positivity) (hoverlap _) (fun j hj => (ht j hj).1)).trans_eq (by ring)
  · exact (D.coupling_jet_bound y 3 (by norm_num) (8*C*B*P.ℓ*P.θ/P.c^2)
      (by positivity) (hoverlap _) (fun j hj => (ht j hj).2)).trans_eq (by ring)

end Bilevel.ChiFine
