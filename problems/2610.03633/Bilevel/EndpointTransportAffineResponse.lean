import Bilevel.EndpointTransportLower

/-! The concrete physical endpoint response is a continuous linear map. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix

def responseLinear {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) : Block D →ₗ[ℝ] Physical n D where
  toFun := physicalResponse δ c Q
  map_add' x y := by
    ext i d
    simp [physicalResponse,physical,response,map_add,smul_add]
    ring
  map_smul' a x := by
    ext i d
    simp [physicalResponse,physical,response,map_smul,smul_smul,mul_comm]
    ring

def physicalResponseCLM {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) : Block D →L[ℝ] Physical n D :=
  LinearMap.toContinuousLinearMap (responseLinear δ c Q)

theorem physicalResponseCLM_apply {n D : ℕ} (δ c : ℝ) (Q : Rotations n D) (x : Block D) :
    physicalResponseCLM δ c Q x=physicalResponse δ c Q x := rfl

end Bilevel.EndpointTransportResponse
