import Bilevel.EndpointTransportFineSelection

/-! Full mixed jets of the actual physical selected fine family. Only scalar
width ordering and actual node admissibility remain as source-scale inputs. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ZeroChainSchedule

theorem selected_physical_fine_ledger : ∃ C : ℝ,1≤C ∧
    ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (n D m : ℕ) (G : Geometry (Block D)),(∀ k I,NodeJetAdmissible (G k I)) →
      ∀ (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ),
      (∀ k I,k<j+d → P.β≤(G k I).width) → (∀ I,P.β≤(G (j+d) I).radius) →
      ∀ p,p≤levels P.θ → ∀ (x : X) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (selectedPhysicalFinePiece m G A B Q P p d j I) x‖≤
        C^(d+1)*fineScale (P.amplitude*P.θ^(-amplitudeExponent p)) (P.ℓ*P.β)
          (pieceResolution P.c P.β P.θ p) q := by
  obtain ⟨Cs,hCs,hs⟩ := ChiLiftedCarrier.constructed_fine_selection_bound
  obtain ⟨Cp,hCp,hp⟩ := physical_fine_piece_bounds
  let C := Cs+Cp
  have hC : 1≤C := by dsimp [C];linarith
  have hCs0 : 0≤Cs := by linarith
  have hCp0 : 0≤Cp := by linarith
  have hC0 : 0≤C := by linarith
  refine ⟨C,hC,fun X _ _ n D m G hadm A B hA hB Q P d j I hwidth hR p hpidx x q hq => ?_⟩
  let δ := pieceResolution P.c P.β P.θ p
  have hδ : 0<δ := pieceResolution_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one p
  have hδβ : δ≤P.β := (pieceResolution_le P.c P.β P.θ P.c_pos.le P.β_pos.le P.θ_ge_one p hpidx).trans
    (mul_le_of_le_one_left P.β_pos.le (show P.c≤1 by linarith [P.c_small]))
  have hβ := P.β_pos
  have hℓ := P.ell_nonneg
  have hamp := P.amplitude_nonneg
  have hθ : 0<P.θ := by linarith [P.θ_ge_one]
  have he : 0≤amplitudeExponent p := by
    unfold amplitudeExponent
    split_ifs
    · norm_num
    · exact aExponent_nonneg _
  have ht : P.θ^(-amplitudeExponent p)≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos P.θ_ge_one (neg_nonpos.mpr he)
  have haM : P.amplitude*P.θ^(-amplitudeExponent p)≤(P.ℓ*P.β)*P.β := by
    apply (mul_le_of_le_one_right hamp ht).trans_eq
    dsimp [ChiFine.Parameters.amplitude]
    ring
  have hleaf (k : ℕ) (J : List ℕ) := (physicalFinePiece_contDiff Q (G k J) P p).comp B.contDiff
  have hbase (J : List ℕ) (z : X) (k : ℕ) (hk : k≤3) :
      ‖iteratedFDeriv ℝ k (physicalFinePiece Q (G (j+d) J) P p ∘ B) z‖≤
        Cp*fineScale (P.amplitude*P.θ^(-amplitudeExponent p)) (P.ℓ*P.β) δ k :=
    (linear_jet_contraction B hB (physicalFinePiece_contDiff Q (G (j+d) J) P p) z k hk).trans
      (hp n D Q (G (j+d) J) P (hR J) p hpidx (B z) k hk)
  have hsel := hs (Block D) X m G A hA hadm _ hleaf (j+d) Cp
    (P.amplitude*P.θ^(-amplitudeExponent p)) (P.ℓ*P.β) δ hCp0 (by positivity) (by positivity) hδ
    (fun k J hk => ⟨hδβ.trans (hwidth k J hk),
      haM.trans (mul_le_mul_of_nonneg_left (hwidth k J hk) (by positivity))⟩)
    hbase d j rfl I x q hq
  have hcoef : Cs^d*Cp≤C^(d+1) := by
    calc
      _≤C^d*C := mul_le_mul (pow_le_pow_left₀ hCs0 (by dsimp [C];linarith) d)
        (by dsimp [C];linarith) hCp0 (pow_nonneg hC0 d)
      _=_ := (pow_succ C d).symm
  exact hsel.trans (mul_le_mul_of_nonneg_right hcoef (fineScale_nonneg (by positivity) (by positivity) hδ.le q))

end Bilevel.EndpointTransportResponse
