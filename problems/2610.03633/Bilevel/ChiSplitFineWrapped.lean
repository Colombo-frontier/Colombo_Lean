import Bilevel.ChiSplitFineData
import Bilevel.ChiSplitWrappedJets
import Bilevel.ChiCarrierFineEnvelope

/-! Actual split fine pieces under a full-vector radial wrapper and a bounded
endpoint readout. The bound retains amplitude separately from positive jets. -/
noncomputable section
namespace Bilevel.ChiSplitFine
open ChiCarrier ChiBoundedChain RadialWrapper ZeroChainSchedule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_fine_readout_bound {n : ℕ} {f : Latent n → ℝ}
    (hf : ContDiff ℝ 3 f) (P : E →L[ℝ] Latent n) (hP : ‖P‖≤3)
    (B a M δ R : ℝ) (hB : 0≤B) (ha : 0≤a) (hM : 0≤M) (hδ : 0<δ) (hδR : δ≤R)
    (hb : ∀ k,k≤3 → ∀ z,‖iteratedFDeriv ℝ k f z‖≤B*fineScale a M δ k)
    (x : E) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (f ∘ P ∘ compress R) x‖≤207*B*fineScale a M δ k := by
  have hR : 0<R := hδ.trans_le hδR
  have hraw := ChiSplitChain.carried_split_jets f hf P hP (B*M) (B*M/δ) (B*M/δ^2) R
    (by positivity) (by positivity) (by positivity) hR
    (fun z => by simpa only [fineScale,pow_zero,div_one] using hb 1 (by norm_num) z)
    (fun z => by simpa only [fineScale,pow_one,mul_div_assoc] using hb 2 (by norm_num) z)
    (fun z => by simpa only [fineScale,mul_div_assoc] using hb 3 (by norm_num) z) x
  have hdiv : B*M/R≤B*M/δ := div_le_div_of_nonneg_left (by positivity) hδ hδR
  have hdiv₂ : B*M/R^2≤B*M/δ^2 := div_le_div_of_nonneg_left (by positivity)
    (sq_pos_of_pos hδ) (pow_le_pow_left₀ hδ.le hδR 2)
  have hcross : (B*M/δ)/R≤B*M/δ^2 := by
    calc
      _≤(B*M/δ)/δ := div_le_div_of_nonneg_left (by positivity) hδ hδR
      _=_ := by rw [div_div,pow_two]
  interval_cases k
  · rw [norm_iteratedFDeriv_zero]
    have hz := hb 0 (by norm_num) (P (compress R x))
    rw [norm_iteratedFDeriv_zero] at hz
    exact hz.trans (by dsimp [fineScale];nlinarith only [mul_nonneg hB ha])
  · dsimp only [fineScale]
    simp only [pow_zero,div_one]
    nlinarith only [hraw.1,mul_nonneg hB hM]
  · dsimp only [fineScale]
    simp only [pow_one]
    have he : 9*(B*M/δ)+12*(B*M)/R=9*(B*M/δ)+12*(B*M/R) := by ring
    rw [he] at hraw
    rw [show 207*B*(M/δ)=207*(B*M/δ) by ring]
    nlinarith only [hraw.2.1,hdiv,show 0≤B*M/δ by positivity]
  · dsimp only [fineScale]
    have he : 27*(B*M/δ^2)+108*(B*M/δ)/R+72*(B*M)/R^2=
        27*(B*M/δ^2)+108*((B*M/δ)/R)+72*(B*M/R^2) := by ring
    have ht := hraw.2.2
    rw [he] at ht
    rw [show 207*B*(M/δ^2)=207*(B*M/δ^2) by ring]
    nlinarith only [ht,hdiv₂,hcross]

def wrappedPiece {n : ℕ} (P : ChiFine.Parameters) (A : E →L[ℝ] Latent n)
    (R : ℝ) (j : ℕ) : E → ℝ := pieces P n j ∘ A ∘ compress R

theorem wrappedPiece_contDiff {n : ℕ} (P : ChiFine.Parameters) (A : E →L[ℝ] Latent n)
    (R : ℝ) (j : ℕ) : ContDiff ℝ 3 (wrappedPiece P A R j) :=
  (pieces_contDiff P n j).comp (A.contDiff.comp (compress_contDiff R 3))

theorem actual_wrapped_piece_bounds : ∃ B : ℝ,1≤B ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (n : ℕ) (P : ChiFine.Parameters) (A : F →L[ℝ] Latent n),‖A‖≤3 →
      ∀ (R : ℝ),P.β≤R → ∀ (j : ℕ),j≤levels P.θ → ∀ (x : F) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (wrappedPiece P A R j) x‖≤
        B*fineScale (P.amplitude*P.θ^(-amplitudeExponent j)) (P.ℓ*P.β)
          (pieceResolution P.c P.β P.θ j) k := by
  obtain ⟨B,hB,hb⟩ := actual_piece_budgets
  refine ⟨207*B,by linarith,fun F _ _ n P A hA R hR j hj x k hk => ?_⟩
  let δ := pieceResolution P.c P.β P.θ j
  have hβ := P.β_pos
  have hℓ := P.ell_nonneg
  have hamp := P.amplitude_nonneg
  have hθ : 0<P.θ := by linarith [P.θ_ge_one]
  have hδ : 0<δ := pieceResolution_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j
  have hδR : δ≤R := (pieceResolution_le P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one j hj).trans
    ((mul_le_of_le_one_left P.β_pos.le (show P.c≤1 by linarith [P.c_small])).trans hR)
  apply radial_fine_readout_bound (pieces_contDiff P n j) A hA B _ _ δ R
    (by linarith) (by positivity) (by positivity) hδ hδR _ x k hk
  intro q hq z
  have hz := hb P n j hj z
  cases q with
  | zero =>
    rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    exact hz.1.trans_eq (by dsimp [fineScale];ring)
  | succ q =>
    apply (hz.2 ⟨q,by omega⟩).trans_eq
    dsimp only [fineScale,ChiFine.Parameters.amplitude,δ]
    field_simp [hβ.ne',hδ.ne']
    ring

end Bilevel.ChiSplitFine

