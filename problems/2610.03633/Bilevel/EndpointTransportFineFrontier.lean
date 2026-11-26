import Bilevel.EndpointTransportFineLedger

/-! The actual selected physical frontier has the coarse derivative scale.
This follows from the already verified fine family at the exact one-level
schedule theta=1; no fine-resolution loss is retained in the final bound. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ZeroChainSchedule

theorem fineScale_small_width {a M β : ℝ} (ha : 0≤a) (hM : 0≤M) (hβ : 0<β)
    (k : ℕ) (hk : k≤3) : fineScale a M (β/128) k≤16384*fineScale a M β k := by
  cases k with
  | zero => dsimp [fineScale];linarith
  | succ k =>
    have he : fineScale a M (β/128) (k+1)=(128:ℝ)^k*fineScale a M β (k+1) := by
      simp only [fineScale,div_pow,div_div_eq_mul_div]
      ring
    rw [he]
    have hk2 : k≤2 := by omega
    have hc : (128:ℝ)^k≤16384 := by interval_cases k <;> norm_num
    exact mul_le_mul_of_nonneg_right hc (fineScale_nonneg ha hM hβ.le _)

theorem selected_physical_frontier_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D m : ℕ) (G : Geometry (Block D)),(∀ k I,NodeJetAdmissible (G k I)) →
      ∀ (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ),
      (∀ k I,k<j+d → P.β≤(G k I).width) → (∀ I,P.β≤(G (j+d) I).radius) →
      ∀ (x : X) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (selectedPhysicalFineFrontier m G A B Q P d j I) x‖≤
        C^(d+1)*fineScale P.amplitude (P.ℓ*P.β) P.β q := by
  obtain ⟨Cb,hCb,hb⟩ := selected_physical_fine_ledger
  have hCb0 : 0≤Cb := by linarith
  refine ⟨16384*Cb,by linarith,fun X _ _ n D m G hadm A B hA hB Q P d j I hw hR x q hq => ?_⟩
  let P₁ : ChiFine.Parameters := ⟨P.ℓ,P.β,1,1/128,P.ell_nonneg,P.β_pos,le_rfl,by norm_num,le_rfl⟩
  have hl : levels P₁.θ=0 := by norm_num [P₁,levels,Real.logb]
  have he : selectedPhysicalFinePiece m G A B Q P₁ 0 d j I=
      selectedPhysicalFineFrontier m G A B Q P d j I := by
    funext y
    have hs := selected_physical_fine_decomposition m G A B Q P₁ d j I y
    simpa only [hl,Nat.zero_add,Finset.sum_range_one] using hs
  have hraw := hb X n D m G hadm A B hA hB Q P₁ d j I hw hR 0 (by rw [hl]) x q hq
  rw [he] at hraw
  have hr : pieceResolution P₁.c P₁.β P₁.θ 0=P.β/128 := by
    simp only [pieceResolution,P₁,Real.one_rpow]
    ring
  have he0 : P₁.θ^(-amplitudeExponent 0)=1 := by simp [P₁]
  rw [hr,he0,mul_one] at hraw
  have hamp := P.amplitude_nonneg
  have hM : 0≤P.ℓ*P.β := mul_nonneg P.ell_nonneg P.β_pos.le
  have hs := mul_le_mul_of_nonneg_left (fineScale_small_width hamp hM P.β_pos q hq)
    (pow_nonneg hCb0 (d+1))
  have hfactor : 16384*Cb^(d+1)≤(16384*Cb)^(d+1) := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hCb0 _)
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤16384) (by omega : 1≤d+1)
  apply hraw.trans
  apply hs.trans
  have hlast := mul_le_mul_of_nonneg_right hfactor (fineScale_nonneg hamp hM P.β_pos.le q)
  convert hlast using 1
  ring

end Bilevel.EndpointTransportResponse
