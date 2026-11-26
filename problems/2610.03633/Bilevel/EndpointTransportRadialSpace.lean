import Bilevel.EndpointTransportHybridOperators
import Bilevel.ChiCarrierBlockSlice
import Bilevel.ChiExtensionSpace
import Bilevel.EndpointTransportOuterTrace

/-! Ordinary and physical public bowls in one common Hilbert codomain.
The isometric embeddings let the actual normal sum use its existing mixed
derivative and trace theorems without identifying different physical spaces. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry PartialLegendre ChiCarrier RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev PhysicalBase (E : Type*) (J n D : ℕ) := Joint E (HybridTangent (Blocks J (Block D)) n D)

def baseMacroProjection (J n D : ℕ) : PhysicalBase E J n D →L[ℝ] E := jointFstLinear

def baseOrdinaryProjection (J n D : ℕ) : PhysicalBase E J n D →L[ℝ] Blocks J (Block D) :=
  jointFstLinear.comp jointSndLinear

def basePhysicalProjection (J n D : ℕ) : PhysicalBase E J n D →L[ℝ] Physical n D :=
  jointSndLinear.comp jointSndLinear

theorem baseMacroProjection_norm_le (J n D : ℕ) : ‖baseMacroProjection (E:=E) J n D‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z.fst‖≤1*‖z‖
  rw [one_mul]
  exact WithLp.norm_fst_le E z

theorem baseOrdinaryProjection_norm_le (J n D : ℕ) : ‖baseOrdinaryProjection (E:=E) J n D‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z.snd.fst‖≤1*‖z‖
  rw [one_mul]
  exact (WithLp.norm_fst_le (Blocks J (Block D)) z.snd).trans
    (WithLp.norm_snd_le E z)

theorem basePhysicalProjection_norm_le (J n D : ℕ) : ‖basePhysicalProjection (E:=E) J n D‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z.snd.snd‖≤1*‖z‖
  rw [one_mul]
  exact (WithLp.norm_snd_le (Blocks J (Block D)) z.snd).trans
    (WithLp.norm_snd_le E z)

def ordinaryRadialProjection {J n D : ℕ} (i : Fin J) :
    PhysicalBase E J n D →L[ℝ] HybridTangent (Blocks J (Block D)) n D :=
  let A : PhysicalBase E J n D →L[ℝ] Blocks J (Block D) :=
    (insertion J i).toContinuousLinearMap.comp
      ((PiLp.proj 2 (fun _ : Fin J => Block D) i).comp (baseOrdinaryProjection J n D))
  packLinear.comp (A.prod 0)

def physicalRadialProjection (J n D : ℕ) :
    PhysicalBase E J n D →L[ℝ] HybridTangent (Blocks J (Block D)) n D :=
  packLinear.comp ((0 : PhysicalBase E J n D →L[ℝ] Blocks J (Block D)).prod (basePhysicalProjection J n D))

theorem ordinaryRadialProjection_apply {J n D : ℕ} (i : Fin J) (z : PhysicalBase E J n D) :
    ordinaryRadialProjection i z=pack (insertion J i (z.snd.fst i)) (0:Physical n D) := rfl

theorem physicalRadialProjection_apply (J n D : ℕ) (z : PhysicalBase E J n D) :
    physicalRadialProjection J n D z=pack (0:Blocks J (Block D)) z.snd.snd := rfl

theorem ordinaryRadialProjection_norm {J n D : ℕ} (i : Fin J) (z : PhysicalBase E J n D) :
    ‖ordinaryRadialProjection i z‖=‖z.snd.fst i‖ := by
  rw [ordinaryRadialProjection_apply,norm_pack_zero_right,LinearIsometry.norm_map]

theorem physicalRadialProjection_norm (J n D : ℕ) (z : PhysicalBase E J n D) :
    ‖physicalRadialProjection J n D z‖=‖z.snd.snd‖ := by
  rw [physicalRadialProjection_apply,norm_pack_zero_left]

theorem ordinaryRadialProjection_norm_le {J n D : ℕ} (i : Fin J) :
    ‖ordinaryRadialProjection (E:=E) (n:=n) (D:=D) i‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul,ordinaryRadialProjection_norm]
  exact (PiLp.norm_apply_le z.snd.fst i).trans
    ((WithLp.norm_fst_le (Blocks J (Block D)) z.snd).trans (WithLp.norm_snd_le E z))

theorem physicalRadialProjection_norm_le (J n D : ℕ) :
    ‖physicalRadialProjection (E:=E) J n D‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  rw [one_mul,physicalRadialProjection_norm]
  exact (WithLp.norm_snd_le (Blocks J (Block D)) z.snd).trans (WithLp.norm_snd_le E z)

theorem ordinary_radial_bowl {J n D : ℕ} (i : Fin J) (ν R : ℝ) (z : PhysicalBase E J n D) :
    bowl ν R (ordinaryRadialProjection i z)=bowl ν R (z.snd.fst i) := by
  simp only [bowl,ordinaryRadialProjection_norm]

theorem physical_radial_bowl (J n D : ℕ) (ν R : ℝ) (z : PhysicalBase E J n D) :
    bowl ν R (physicalRadialProjection J n D z)=bowl ν R z.snd.snd := by
  simp only [bowl,physicalRadialProjection_norm]

theorem physicalPublic_sum {n D : ℕ} (ρ R : ℕ → ℝ) (d j : ℕ)
    (u : ℕ → Block D) (Y : Physical n D) :
    physicalPublic ρ R d j u Y=
      (∑ i : Fin d,bowl (ρ (j+i.val)) (R (j+i.val)) (u (j+i.val)))+
        bowl (ρ (j+d)/EndpointTransportMatrix.gamma n^2) (EndpointTransportMatrix.gamma n*R (j+d)) Y := by
  induction d generalizing j with
  | zero => simp only [physicalPublic,Fin.sum_univ_zero,zero_add,Nat.add_zero]
  | succ d ih =>
    rw [physicalPublic,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_zero]
    have he : (∑ i : Fin d,bowl (ρ (j+1+i.val)) (R (j+1+i.val)) (u (j+1+i.val)))=
        ∑ i : Fin d,bowl (ρ (j+(i.val+1))) (R (j+(i.val+1))) (u (j+(i.val+1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show j+1+i.val=j+(i.val+1) by omega]
    rw [he,show j+1+d=j+(d+1) by omega]
    ring

end Bilevel.EndpointTransportResponse
