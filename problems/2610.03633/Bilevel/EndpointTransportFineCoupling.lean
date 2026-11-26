import Bilevel.EndpointTransportFineLedger
import Bilevel.ChiFineGeneric

/-! Actual ancestor-selected physical fine normal coupling and full mixed
derivative budgets. The construction retains the physical predecessor selector. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ZeroChainSchedule SmallGapLiftSupport
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def physicalFineData {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) : CompensatedMean.Data (E:=X) where
  μ := 1
  L := 1
  J := levels P.θ
  r := selectedPhysicalFineFrontier m G A B Q P d j I
  A := fun _ => 0
  e := fun p => selectedPhysicalFinePiece m G A B Q P p d j I
  w := width P.c P.β P.θ
  r_smooth := selectedPhysicalFineFrontier_contDiff m G A B Q P d j I
  A_smooth := contDiff_const
  e_smooth := fun p => selectedPhysicalFinePiece_contDiff m G A B Q P p d j I
  w_pos := fun p _ => width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one p
  decomposition := selected_physical_fine_decomposition m G A B Q P d j I

theorem physicalFineData_overlap {n D : ℕ} (m : ℕ) (G : Geometry (Block D))
    (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ) (x : X) :
    ((physicalFineData m G A B Q P d j I).activePieces x).card≤3 :=
  selected_physical_fine_overlap m G A B Q P d j I x

theorem selected_physical_coupling_jets : ∃ Cb : ℝ,1≤Cb ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (n D m : ℕ) (G : Geometry (Block D)),(∀ k I,NodeJetAdmissible (G k I)) →
      ∀ (A : F →L[ℝ] Blocks m (Block D)) (B : F →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (P : ChiFine.Parameters) (d j : ℕ) (I : List ℕ),
      (∀ k I,k<j+d → P.β≤(G k I).width) → (∀ I,P.β≤(G (j+d) I).radius) →
      ∀ y : CompensatedMean.LowerSpace F,
      ‖iteratedFDeriv ℝ 1 (physicalFineData m G A B Q P d j I).coupling y‖≤6*C*Cb^(d+1)*P.ℓ*P.β^2 ∧
      ‖iteratedFDeriv ℝ 2 (physicalFineData m G A B Q P d j I).coupling y‖≤12*C*Cb^(d+1)*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 (physicalFineData m G A B Q P d j I).coupling y‖≤24*C*Cb^(d+1)*P.ℓ*P.θ/P.c^2 := by
  obtain ⟨Cb,hCb,hb⟩ := selected_physical_fine_ledger
  refine ⟨Cb,hCb,fun F _ _ n D m G hadm A B hA hB Q P d j I hw hR y => ?_⟩
  let S := physicalFineData m G A B Q P d j I
  have hβ := P.β_pos
  have hbound : ∀ p,p≤S.J → ∀ x,|S.e p x|≤Cb^(d+1)*P.amplitude*P.θ^(-amplitudeExponent p) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (S.e p) x‖≤
        Cb^(d+1)*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ p)^k.val) := by
    intro p hp x
    have hjets (q : ℕ) (hq : q≤3) := hb F n D m G hadm A B hA hB Q P d j I hw hR p hp x q hq
    constructor
    · have ht := hjets 0 (by norm_num)
      rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at ht
      exact ht.trans_eq (by dsimp [fineScale];ring)
    · intro k
      have hδ := pieceResolution_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one p
      apply (hjets (k.val+1) (by omega)).trans_eq
      dsimp only [fineScale,ChiFine.Parameters.amplitude]
      field_simp [hβ.ne',hδ.ne']
      ring
  exact ChiFine.generic_coupling_bounds P S rfl (fun _ => rfl) (Cb^(d+1))
    (one_le_pow₀ hCb) hbound (physicalFineData_overlap m G A B Q P d j I) y

end Bilevel.EndpointTransportResponse
