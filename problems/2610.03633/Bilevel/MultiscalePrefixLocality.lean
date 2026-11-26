import Bilevel.WrappedPrefixLocality
import Bilevel.MultiscaleInactiveFormula

/-! Prefix locality for the actual radially carried multiscale ingredients.
The subspace includes the query vector, accounting for the radial component. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.MultiscaleMean
open ZeroChain WrappedChain RadialWrapper ZeroChainSchedule CompensatedMean
  WrappedPrefixLocality ZeroChainResidualScaled ZeroChainFlatteningBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E := E) n)

theorem inactiveResidual_gradient_mem (r : ℕ) (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U u j| ≤ P.signalResolution) :
    gradient P.inactiveResidual u ∈ V :=
  carried_flat_gradient_mem n r P.amplitude P.β P.signalResolution P.R
    P.signalResolution_pos (P.β_pos.trans_le P.β_le_R) P.U u V hu hU hz

theorem flatApproximation_gradient_mem (r j : ℕ) (hj : j < levels P.θ)
    (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ i : Fin (n+1), i.val < r → P.U (basis i) ∈ V)
    (hz : ∀ i : Fin (n+1), r ≤ i.val →
      |coordinates n P.R P.U u i| ≤ P.signalResolution) :
    gradient (P.flatApproximation j) u ∈ V := by
  apply carried_flat_gradient_mem n r P.amplitude P.β (resolution P.c P.β P.θ j) P.R
    (resolution_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j)
    (P.β_pos.trans_le P.β_le_R) P.U u V hu hU
  exact fun i hi => (hz i hi).trans (P.signalResolution_le_resolution j hj)

theorem residual_gradient_mem (r : ℕ) (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r+1 → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U u j| ≤ P.signalResolution) :
    gradient P.residual u ∈ V := by
  apply carried_residual_gradient_mem n r P.amplitude P.β P.R P.β_pos
    (P.β_pos.trans_le P.β_le_R) P.U u V hu hU
  intro j hj
  exact (hz j hj).trans (P.signalResolution_small.trans (by linarith [P.β_pos]))

theorem revealed_wrapped : P.revealed =
    wrapped P.ν P.R (A n P.amplitude P.β) P.U.toContinuousLinearMap.adjoint := by
  funext u
  have h := exact_split n P.amplitude P.β (coordinates n P.R P.U u)
  dsimp [revealed, outer, WrappedChain.value, residual, ZeroChainWrappedResidual.residual,
    wrapped, coordinates] at *
  linarith

theorem revealed_gradient_mem (r : ℕ) (u : E) (V : Submodule ℝ E) (hu : u ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U u j| ≤ P.signalResolution) :
    gradient P.revealed u ∈ V := by
  rw [P.revealed_wrapped]
  have hg := wrapped_hasGradientAt P.ν P.R (P.β_pos.trans_le P.β_le_R)
    (A n P.amplitude P.β) P.U.toContinuousLinearMap.adjoint u
    (gradient (A n P.amplitude P.β) (coordinates n P.R P.U u))
    ((A_contDiff n P.amplitude P.β).differentiable (by norm_num) _).hasGradientAt
  rw [hg.gradient]
  simp only [ContinuousLinearMap.adjoint_adjoint, LinearIsometry.coe_toContinuousLinearMap]
  apply V.add_mem _ (V.smul_mem _ hu)
  apply V.smul_mem
  apply frame_mem_of_support P.U V hU
  intro j hj
  apply A_gradient_support n r P.amplitude P.β P.β_pos _ _ j hj
  exact fun i hi => (hz i hi).trans (P.signalResolution_small.trans (by linarith [P.β_pos]))

theorem signalU_mem (r : ℕ) (y : LowerSpace E) (V : Submodule ℝ E)
    (hu : uProj E y ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r+1 → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U (uProj E y) j| ≤ P.signalResolution) :
    P.signalU y ∈ V := by
  have hr := P.residual_gradient_mem r _ V hu hU hz
  have ht := P.inactiveResidual_gradient_mem r _ V hu (fun j hj => hU j (by omega)) hz
  have hd : gradient P.residualDifference (uProj E y) ∈ V := by
    rw [P.residualDifference_gradient]
    exact V.sub_mem hr ht
  exact V.sub_mem (V.smul_mem _ (V.add_mem (V.smul_mem _ hr) (V.smul_mem _ hd)))
    (V.smul_mem _ hd)

theorem inactiveU_formula (y : LowerSpace E) :
    P.data.perturbationU y - P.signalU y =
      (P.μ/P.L^2*P.inactiveResidual (uProj E y)) • gradient P.inactiveResidual (uProj E y) -
        (P.μ/P.L) • (SmallGapProfiles.normal P.finalWidth (sProj E y) •
          gradient P.inactiveResidual (uProj E y) +
          ∑ j ∈ Finset.range (levels P.θ),
            (SmallGapProfiles.normal (width P.c P.β P.θ j) (sProj E y) -
              SmallGapProfiles.normal (width P.c P.β P.θ (j+1)) (sProj E y)) •
                gradient (P.flatApproximation j) (uProj E y)) := by
  have hr := ((P.inactiveResidual_contDiff.differentiable (by norm_num) _).hasGradientAt.hasFDerivAt).comp y
    (uProj E).hasFDerivAt
  have hf (j : ℕ) := ((P.flatApproximation_contDiff j).differentiable
    (by norm_num) (uProj E y)).hasGradientAt.hasFDerivAt.comp y (uProj E).hasFDerivAt
  have hq (j : ℕ) := ((SmallGapProfiles.normal_contDiff (width P.c P.β P.θ j)
    (width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one j)).differentiable
      (by norm_num) (sProj E y)).hasDerivAt.hasFDerivAt.comp y (sProj E).hasFDerivAt
  have hfinal := ((SmallGapProfiles.normal_contDiff P.finalWidth P.finalWidth_pos).differentiable
    (by norm_num) (sProj E y)).hasDerivAt.hasFDerivAt.comp y (sProj E).hasFDerivAt
  have hsum := HasFDerivAt.sum (fun j (_ : j ∈ Finset.range (levels P.θ)) =>
    (hf j).mul ((hq j).sub (hq (j+1))))
  have hnew := ((hr.mul hr).const_mul (P.μ/(2*P.L^2))).sub
    (((hr.mul hfinal).add hsum).const_mul (P.μ/P.L))
  have hold := (P.data.perturbation_hasGradientAt y).hasFDerivAt.sub
    (P.signal_hasGradientAt y).hasFDerivAt
  have he : (fun v => P.data.perturbation v - P.signal v) =
      fun v => P.μ/(2*P.L^2)*(P.inactiveResidual (uProj E v)*P.inactiveResidual (uProj E v)) -
        P.μ/P.L*(P.inactiveResidual (uProj E v)*SmallGapProfiles.normal P.finalWidth (sProj E v) +
          ∑ j ∈ Finset.range (levels P.θ), P.flatApproximation j (uProj E v)*
            (SmallGapProfiles.normal (width P.c P.β P.θ j) (sProj E v) -
              SmallGapProfiles.normal (width P.c P.β P.θ (j+1)) (sProj E v))) := by
    funext v
    simpa only [pow_two] using P.inactivePerturbation_flat_formula v
  rw [he] at hold
  have hd := hold.unique hnew
  apply ext_inner_right ℝ
  intro v
  have hh := congrArg (fun D => D (pack E v 0 0)) hd
  simp only [CompensatedMean.Data.perturbationGradient, signalY,
    InnerProductSpace.toDual_apply, inner_pack, uProj_pack, sProj_pack, zProj_pack,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
    smul_eq_mul, zero_mul, mul_zero, add_zero, zero_add, sub_zero, Function.comp_apply] at hh
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left, sum_inner]
  linear_combination hh

theorem inactiveU_mem (r : ℕ) (y : LowerSpace E) (V : Submodule ℝ E)
    (hu : uProj E y ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U (uProj E y) j| ≤ P.signalResolution) :
    P.data.perturbationU y - P.signalU y ∈ V := by
  rw [P.inactiveU_formula]
  have ht := P.inactiveResidual_gradient_mem r _ V hu hU hz
  apply V.sub_mem (V.smul_mem _ ht)
  apply V.smul_mem
  apply V.add_mem (V.smul_mem _ ht)
  apply V.sum_mem
  intro j hj
  exact V.smul_mem _ (P.flatApproximation_gradient_mem r j (Finset.mem_range.mp hj) _ V hu hU hz)

theorem inactiveLowerY_u_mem (r : ℕ) (x : E) (y : LowerSpace E) (V : Submodule ℝ E)
    (hx : x ∈ V) (hu : uProj E y ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U (uProj E y) j| ≤ P.signalResolution) :
    uProj E (P.inactiveLowerY x y) ∈ V := by
  have he : uProj E (P.inactiveLowerY x y) =
      (P.μ • uProj E y - P.L • x) + (P.data.perturbationU y - P.signalU y) := by
    simp only [inactiveLowerY, CompensatedMean.Data.lowerY, signalY, map_sub, uProj_pack]
    change P.μ • uProj E y - P.L • x + P.data.perturbationU y - P.signalU y = _
    abel
  rw [he]
  exact V.add_mem (V.sub_mem (V.smul_mem _ hu) (V.smul_mem _ hx)) (P.inactiveU_mem r y V hu hU hz)

/-- A failed Bernoulli revelation has no vector component beyond the known
query/prefix subspace. Scalar coefficients are not discarded. -/
theorem inactive_sample_u_mem (r : ℕ) (p : ℝ) (x : E) (y : LowerSpace E)
    (V : Submodule ℝ E) (hx : x ∈ V) (hu : uProj E y ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U (uProj E y) j| ≤ P.signalResolution) :
    uProj E (P.sampleLowerY p x y false) ∈ V := by
  rw [(P.inactive_sample p x y).2]
  exact P.inactiveLowerY_u_mem r x y V hx hu hU hz

/-- On activation the actual sample needs at most one additional frame column. -/
theorem active_sample_u_mem (r : ℕ) (p : ℝ) (x : E) (y : LowerSpace E)
    (V : Submodule ℝ E) (hx : x ∈ V) (hu : uProj E y ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r+1 → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U (uProj E y) j| ≤ P.signalResolution) :
    uProj E (P.sampleLowerY p x y true) ∈ V := by
  simp only [sampleLowerY, BernoulliOracle.sample, if_true, map_add, map_smul,
    signalY, uProj_pack]
  exact V.add_mem (P.inactiveLowerY_u_mem r x y V hx hu (fun j hj => hU j (by omega)) hz)
    (V.smul_mem _ (P.signalU_mem r y V hu hU hz))

theorem upperY_u_mem (r : ℕ) (x : E) (y : LowerSpace E) (V : Submodule ℝ E)
    (hu : uProj E y ∈ V)
    (hU : ∀ j : Fin (n+1), j.val < r → P.U (basis j) ∈ V)
    (hz : ∀ j : Fin (n+1), r ≤ j.val →
      |coordinates n P.R P.U (uProj E y) j| ≤ P.signalResolution) :
    uProj E (P.data.upperY x y) ∈ V :=
  P.revealed_gradient_mem r _ V hu hU hz

theorem sampleLowerX_mem (p : ℝ) (x : E) (y : LowerSpace E) (b : Bool)
    (V : Submodule ℝ E) (hu : uProj E y ∈ V) : P.sampleLowerX p x y b ∈ V :=
  V.smul_mem (-P.L) hu

end Parameters
end Bilevel.MultiscaleMean
