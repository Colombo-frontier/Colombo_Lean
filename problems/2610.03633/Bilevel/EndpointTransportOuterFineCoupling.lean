import Bilevel.EndpointTransportOuterOverlap
import Bilevel.EndpointTransportFineCoupling

/-! Actual fully selected physical fine normal coupling. Mixed normal and
tangential jets use the proved overlap 3, including the one-sided macro. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter ZeroChainSchedule SmallGapLiftSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def outerPhysicalFineData {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d : ℕ) : CompensatedMean.Data (E:=X) where
  μ := 1
  L := 1
  J := levels P.θ
  r := outerPhysicalFineFrontier m Q M macroP G A B P d
  A := fun _ => 0
  e := fun p => outerPhysicalFinePiece m Q M macroP G A B P p d
  w := width P.c P.β P.θ
  r_smooth := outerPhysicalFineFrontier_contDiff m Q M macroP G A B P d
  A_smooth := contDiff_const
  e_smooth := fun p => outerPhysicalFinePiece_contDiff m Q M macroP G A B P p d
  w_pos := fun p _ => width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one p
  decomposition := outer_physical_fine_decomposition m Q M macroP G A B P d

theorem outerPhysicalFineData_overlap {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (macroP : X →L[ℝ] E)
    (G : Geometry (Block D)) (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D)
    (P : ChiFine.Parameters) (d : ℕ) (x : X) :
    ((outerPhysicalFineData m Q M macroP G A B P d).activePieces x).card≤3 :=
  outer_physical_fine_overlap m Q M macroP G A B P d x

theorem outer_physical_coupling_jets : ∃ Cb : ℝ,1≤Cb ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
      (n D m : ℕ) (M : Node E) (macroP : X →L[ℝ] E),‖macroP‖≤1 → 0<M.width → M.width≤M.radius →
      ∀ (G : Geometry (Block D)),(∀ k I,NodeJetAdmissible (G k I)) →
      ∀ (A : X →L[ℝ] Blocks m (Block D)) (B : X →L[ℝ] Physical n D),‖A‖≤1 → ‖B‖≤1 →
      ∀ (Q : Rotations n D) (P : ChiFine.Parameters) (d : ℕ),P.β≤M.width →
      (∀ k I,k<d → P.β≤(G k I).width) → (∀ I,P.β≤(G d I).radius) →
      ∀ y : CompensatedMean.LowerSpace X,
      ‖iteratedFDeriv ℝ 1 (outerPhysicalFineData m Q M macroP G A B P d).coupling y‖≤6*C*Cb^(d+2)*P.ℓ*P.β^2 ∧
      ‖iteratedFDeriv ℝ 2 (outerPhysicalFineData m Q M macroP G A B P d).coupling y‖≤12*C*Cb^(d+2)*P.ℓ*P.β*Real.sqrt P.θ/P.c ∧
      ‖iteratedFDeriv ℝ 3 (outerPhysicalFineData m Q M macroP G A B P d).coupling y‖≤24*C*Cb^(d+2)*P.ℓ*P.θ/P.c^2 := by
  obtain ⟨Cb,hCb,hb⟩ := outer_physical_fine_ledger
  refine ⟨Cb,hCb,fun E _ _ _ X _ _ n D m M macroP hm hh hhR G hadm A B hA hB Q P d hβM hw hR y => ?_⟩
  let S := outerPhysicalFineData m Q M macroP G A B P d
  have hβ := P.β_pos
  have hbound : ∀ p,p≤S.J → ∀ x,|S.e p x|≤Cb^(d+2)*P.amplitude*P.θ^(-amplitudeExponent p) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (S.e p) x‖≤
        Cb^(d+2)*P.amplitude/(P.β*(pieceResolution P.c P.β P.θ p)^k.val) := by
    intro p hp x
    have hjets (q : ℕ) (hq : q≤3) :=
      (hb E X n D m M macroP hm hh hhR G hadm A B hA hB Q P d hβM hw hR x q hq).2 p hp
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
  exact ChiFine.generic_coupling_bounds P S rfl (fun _ => rfl) (Cb^(d+2))
    (one_le_pow₀ hCb) hbound (outerPhysicalFineData_overlap m Q M macroP G A B P d) y

end Bilevel.EndpointTransportResponse
