import Bilevel.EndpointTransportQuadraticCore
import Bilevel.EndpointTransportOneBlockCoordinates
import Bilevel.EndpointTransportLower

/-! Exact quadratic-core response trace and the actual upper scalar on the
full query. The unused outer endpoint block is only a spectator of f. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem quadraticCore_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (x : Joint E (Block D)) :
    quadraticCore Q M ν G (ρ 0) (R 0) (pack x.fst (physicalResponse δ c Q x.snd))=
      jointOuter 1 M ν G ρ R 0 (gain n δ c) (oneBlockCoordinates x) := by
  let u := padded (gain n δ c • (oneBlockCoordinates x).snd)
  have hu : u 0=gain n δ c • x.snd := by
    change block 1 0 (gain n δ c • (oneBlockCoordinates x).snd)=_
    rw [block,dif_pos (by decide : 0<1),PiLp.proj_apply,PiLp.smul_apply]
    rw [show (⟨0,by decide⟩:Fin 1)=0 from rfl,oneBlockCoordinates_zero_block]
  rw [quadraticCore_eq_physicalOuter Q M ν G ρ R x.fst _ u,
    physical_outer_response δ c Q M ν G ρ R 0 x.fst u x.snd hu]
  rfl

theorem source_quadraticCore_response {D : ℕ} {L κ : ℝ} (hL : 0<L) (hκ : 3200≤κ)
    (Q : Rotations (EndpointTransportNormalization.interiors κ) D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (x : Joint E (Block D)) :
    quadraticCore Q M ν G (ρ 0) (R 0) (pack x.fst (physicalResponse (L/16) (L/4) Q x.snd))=
      jointOuter 1 M ν G ρ R 0 (EndpointTransportNormalization.gain κ) (oneBlockCoordinates x) := by
  rw [quadraticCore_response,source_physical_gain hL hκ]

def quadraticUpperProjection (n D : ℕ) :
    Joint (Joint E (Block D)) (Physical n D) →L[ℝ] Joint E (Physical n D) :=
  packLinear.comp ((jointFstLinear.comp jointFstLinear).prod jointSndLinear)

omit [CompleteSpace E] in
theorem quadraticUpperProjection_norm (n D : ℕ) :
    ‖(quadraticUpperProjection (E:=E) n D)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  change ‖pack q.fst.fst q.snd‖≤1*‖q‖
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [norm_sq]
  change ‖q.fst.fst‖^2+‖q.snd‖^2≤(‖q.fst.fst‖^2+‖q.fst.snd‖^2)+‖q.snd‖^2
  nlinarith only [sq_nonneg ‖q.fst.snd‖]

def quadraticFullCore {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) :
    Joint (Joint E (Block D)) (Physical n D) → ℝ :=
  quadraticCore Q M ν G ρ R ∘ quadraticUpperProjection n D

theorem quadraticFullCore_contDiff {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) : ContDiff ℝ 3 (quadraticFullCore Q M ν G ρ R) :=
  (quadraticCore_contDiff Q M ν G ρ R).comp (quadraticUpperProjection (E:=E) n D).contDiff

theorem quadraticFullCore_second_bound {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R B : ℝ)
    (hb : ∀ z,‖iteratedFDeriv ℝ 2 (quadraticCore Q M ν G ρ R) z‖≤B)
    (z : Joint (Joint E (Block D)) (Physical n D)) :
    ‖iteratedFDeriv ℝ 2 (quadraticFullCore Q M ν G ρ R) z‖≤B :=
  (linear_jet_contraction (quadraticUpperProjection (E:=E) n D) (quadraticUpperProjection_norm n D)
    (quadraticCore_contDiff Q M ν G ρ R) z 2 (by norm_num)).trans (hb _)

theorem quadraticFullCore_lower_gradient {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℝ) (x : Joint E (Block D)) (Y : Physical n D) :
    gradient (fun v => quadraticFullCore Q M ν G ρ R (pack x v)) Y=
      gradient (fun v => quadraticCore Q M ν G ρ R (pack x.fst v)) Y := rfl

end Bilevel.EndpointTransportResponse
