import Bilevel.EndpointTransportOuterSelection
import Bilevel.EndpointTransportFineFrontier

/-! Actual physical fine frontier and pieces under one-sided macro
selection, including the complete mixed derivative envelopes. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ZeroChainSchedule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def outerPhysicalFineFrontier {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d : ℕ) : X → ℝ :=
  macroSelected M macroP (fun i => selectedPhysicalFineFrontier m G A B Q P d 0 [i.val])

def outerPhysicalFinePiece {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (p d : ℕ) : X → ℝ :=
  macroSelected M macroP (fun i => selectedPhysicalFinePiece m G A B Q P p d 0 [i.val])

theorem outerPhysicalFineFrontier_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d : ℕ) : ContDiff ℝ 3 (outerPhysicalFineFrontier m Q M macroP G A B P d) :=
  macroSelected_contDiff M macroP _ (fun i => selectedPhysicalFineFrontier_contDiff m G A B Q P d 0 [i.val])

theorem outerPhysicalFinePiece_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (p d : ℕ) : ContDiff ℝ 3 (outerPhysicalFinePiece m Q M macroP G A B P p d) :=
  macroSelected_contDiff M macroP _ (fun i => selectedPhysicalFinePiece_contDiff m G A B Q P p d 0 [i.val])

theorem outer_physical_fine_decomposition {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d : ℕ) (x : X) :
    (∑ p ∈ Finset.range (levels P.θ+1),outerPhysicalFinePiece m Q M macroP G A B P p d x)=
      outerPhysicalFineFrontier m Q M macroP G A B P d x := by
  unfold outerPhysicalFinePiece outerPhysicalFineFrontier macroSelected
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum,selected_physical_fine_decomposition]

theorem outer_physical_fine_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D m : ℕ) (M : Node E) (macroP : X →L[ℝ] E),‖macroP‖≤1 → 0<M.width → M.width≤M.radius →
      ∀ (G : Geometry (Block D)),(∀ k I,NodeJetAdmissible (G k I)) →
      ∀ (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (P : ChiFine.Parameters) (d : ℕ),P.β≤M.width →
      (∀ k I,k<d → P.β≤(G k I).width) → (∀ I,P.β≤(G d I).radius) →
      ∀ (x : X) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (outerPhysicalFineFrontier m Q M macroP G A B P d) x‖≤
        C^(d+2)*fineScale P.amplitude (P.ℓ*P.β) P.β q ∧
      ∀ p,p≤levels P.θ →
      ‖iteratedFDeriv ℝ q (outerPhysicalFinePiece m Q M macroP G A B P p d) x‖≤
        C^(d+2)*fineScale (P.amplitude*P.θ^(-amplitudeExponent p)) (P.ℓ*P.β)
          (pieceResolution P.c P.β P.θ p) q := by
  obtain ⟨Cf,hCf,hfront⟩ := selected_physical_frontier_ledger
  obtain ⟨Cp,hCp,hpiece⟩ := selected_physical_fine_ledger
  obtain ⟨Co,hCo,houter⟩ := constructed_macro_fine_step
  let C := Cf+Cp+Co
  have hC : 1≤C := by dsimp [C];linarith
  have hC0 : 0≤C := by linarith
  refine ⟨C,hC,fun E _ _ _ X _ _ n D m M macroP hm hh hhR G hadm A B hA hB Q P d hβM hw hR x q hq => ?_⟩
  have transport (Ci : ℝ) (hCi : 1≤Ci) (hCiC : Ci≤C)
      (f : Fin (M.n+1) → X → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
      (a δ : ℝ) (ha : 0≤a) (hδ : 0<δ) (hδβ : δ≤P.β) (haβ : a≤(P.ℓ*P.β)*P.β)
      (hb : ∀ i k,k≤q → ‖iteratedFDeriv ℝ k (f i) x‖≤Ci^(d+1)*fineScale a (P.ℓ*P.β) δ k) :
      ‖iteratedFDeriv ℝ q (macroSelected M macroP f) x‖≤C^(d+2)*fineScale a (P.ℓ*P.β) δ q := by
    have hCi0 : 0≤Ci := by linarith
    have hV : 0≤P.ℓ*P.β := mul_nonneg P.ell_nonneg P.β_pos.le
    have hs := houter E X M macroP hm hh hhR f hf (Ci^(d+1)) a (P.ℓ*P.β) δ
      (by positivity) ha hV hδ (hδβ.trans hβM)
      (haβ.trans (mul_le_mul_of_nonneg_left hβM hV)) x q hq hb
    have hcoef : Co*Ci^(d+1)≤C^(d+2) := by
      calc
        _≤C*C^(d+1) := mul_le_mul (by dsimp [C];linarith) (pow_le_pow_left₀ hCi0 hCiC _) (by positivity) hC0
        _=_ := by rw [show d+2=(d+1)+1 by omega,pow_succ];ring
    exact hs.trans (mul_le_mul_of_nonneg_right hcoef (fineScale_nonneg ha hV hδ.le q))
  constructor
  · apply transport Cf hCf (by dsimp [C];linarith) _
      (fun i => selectedPhysicalFineFrontier_contDiff m G A B Q P d 0 [i.val]) P.amplitude P.β
      P.amplitude_nonneg P.β_pos le_rfl (by dsimp [ChiFine.Parameters.amplitude];ring_nf;exact le_rfl)
    intro i k hk
    simpa only [Nat.zero_add] using hfront X n D m G hadm A B hA hB Q P d 0 [i.val]
      (fun k I hk => hw k I (by omega)) (fun I => by simpa only [Nat.zero_add] using hR I) x k (by omega)
  · intro p hp
    have hδ := pieceResolution_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one p
    have hδβ := (pieceResolution_le P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one p hp).trans
      (mul_le_of_le_one_left P.β_pos.le (show P.c≤1 by linarith [P.c_small]))
    have he : 0≤amplitudeExponent p := by
      unfold amplitudeExponent
      split_ifs
      · norm_num
      · exact aExponent_nonneg _
    have hp1 := Real.rpow_le_one_of_one_le_of_nonpos P.θ_ge_one (neg_nonpos.mpr he)
    have haβ : P.amplitude*P.θ^(-amplitudeExponent p)≤(P.ℓ*P.β)*P.β := by
      apply (mul_le_of_le_one_right P.amplitude_nonneg hp1).trans_eq
      dsimp [ChiFine.Parameters.amplitude]
      ring
    apply transport Cp hCp (by dsimp [C];linarith) _
      (fun i => selectedPhysicalFinePiece_contDiff m G A B Q P p d 0 [i.val])
      (P.amplitude*P.θ^(-amplitudeExponent p)) (pieceResolution P.c P.β P.θ p)
      (mul_nonneg P.amplitude_nonneg (Real.rpow_nonneg (by linarith [P.θ_ge_one]) _)) hδ hδβ haβ
    intro i k hk
    simpa only [Nat.zero_add] using hpiece X n D m G hadm A B hA hB Q P d 0 [i.val]
      (fun k I hk => hw k I (by omega)) (fun I => by simpa only [Nat.zero_add] using hR I) p hp x k (by omega)

end Bilevel.EndpointTransportResponse
