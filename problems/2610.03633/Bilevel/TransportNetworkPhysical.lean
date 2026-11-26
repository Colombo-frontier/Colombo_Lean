import Bilevel.TransportNetworkGauge
import Bilevel.EndpointTransportReadout

/-! Canonical physical rotations from the actual random path network.
The last physical rotation is identity, so endpoint coupling is public.
Terminal latent frames are based at the last network frame, and every
physical endpoint column is exactly the corresponding network column. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportHierarchy
open EuclideanGaussian TransportNetwork OrthogonalAction EndpointTransportResponse

set_option maxHeartbeats 600000

def physicalRotations {n D : ℕ} (z : Latent (n+1) D) : Rotations n D :=
  fun v => isometry D (orientation z v.val*(orientation z (n+1))⁻¹)

theorem physicalRotations_apply {n D : ℕ} (z : Latent (n+1) D) (v : EndpointTransportMatrix.Index n) (x : Space D) :
    physicalRotations z v x=(orientation z v.val*(orientation z (n+1))⁻¹) • x := rfl

theorem physicalRotations_last {n D : ℕ} (z : Latent (n+1) D) :
    physicalRotations z (Fin.last (n+1))=LinearIsometryEquiv.refl ℝ (Space D) := by
  ext x
  rw [physicalRotations_apply]
  simp only [Fin.val_last,mul_inv_cancel,one_smul]
  rfl

theorem physicalRotations_symm_apply {n D : ℕ} (z : Latent (n+1) D)
    (v : EndpointTransportMatrix.Index n) (x : Space D) :
    (physicalRotations z v).symm x=(orientation z v.val*(orientation z (n+1))⁻¹)⁻¹ • x := by
  apply (physicalRotations z v).injective
  rw [LinearIsometryEquiv.apply_symm_apply,physicalRotations_apply,smul_inv_smul]

theorem physicalRotations_forward {n D : ℕ} (z : Latent (n+1) D)
    (e : Edge (n+1)) (x : Space D) :
    physicalRotations z (dst e) x=z.2 e • physicalRotations z (src e) x := by
  simp only [physicalRotations_apply,src,dst,Fin.val_succ,Fin.coe_castSucc,orientation,dif_pos e.isLt]
  rw [mul_assoc,mul_smul]

theorem physicalRotations_edge {n D : ℕ} (z : Latent (n+1) D)
    (e : Edge (n+1)) (x : Space D) :
    physicalRotations z (dst e) ((physicalRotations z (src e)).symm x)=z.2 e • x := by
  rw [physicalRotations_forward,LinearIsometryEquiv.apply_symm_apply]

theorem physicalRotations_apply_measurable (n D : ℕ) (v : EndpointTransportMatrix.Index n) :
    Measurable (fun p : Latent (n+1) D × Space D => physicalRotations p.1 v p.2) := by
  have h : Continuous (fun p : Latent (n+1) D × Space D =>
      orientation p.1 v.val*(orientation p.1 (n+1))⁻¹) :=
    ((orientation_continuous (n+1) D v.val).comp continuous_fst).mul
    (((orientation_continuous (n+1) D (n+1)).comp continuous_fst).inv)
  exact h.measurable.smul measurable_snd

def terminalBaseFrame {n D r : ℕ} (z : Latent (n+1) D)
    (U : ChiBoundedChain.Space r →ₗᵢ[ℝ] Space D) : ChiBoundedChain.Space r →ₗᵢ[ℝ] Space D :=
  (isometry D (orientation z (n+1))).toLinearIsometry.comp U

theorem physical_terminal_frame {n D r : ℕ} (z : Latent (n+1) D)
    (U : ChiBoundedChain.Space r →ₗᵢ[ℝ] Space D) (v : EndpointTransportMatrix.Index n)
    (x : ChiBoundedChain.Space r) :
    physicalRotations z v (terminalBaseFrame z U x)=orientation z v.val • U x := by
  change (orientation z v.val*(orientation z (n+1))⁻¹) • (orientation z (n+1) • U x)=_
  rw [mul_smul,inv_smul_smul]

theorem physical_lower_public_coupling {n D : ℕ} (δ c : ℝ) (z : Latent (n+1) D)
    (v : Block D) (Y : Configuration n D) :
    lower δ c (physicalRotations z) v Y=
      δ/2*(∑ d : Fin D,EndpointTransportMatrix.quadratic n (EndpointTransportMatrix.matrix n)
        (coordinates (physicalRotations z) Y d))-c*⟪v,Y (Fin.last (n+1))⟫ := by
  rw [lower_physical_formula,physicalRotations_last]
  rfl

end Bilevel.TransportHierarchy
