import GradientHessian.MemoryMissJets
import GradientHessian.InnerFunctions

/-! Explicit function masks. A hidden future forcing is removed as a whole
weighted term. Setting its numerical vector to zero would retain a positive
constant, just as zeroing a memory direction retains a nonzero incoming term. -/

noncomputable section
namespace GradientHessian.GeometricMaskJets
open Filter JetLocality
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem forcing_zero_vector (y : E) : InverseGate.forcing 0 y=10*InverseGate.H₀^2 := by
  have ht := IntegralProfiles.theta_identity (t := 0) (by norm_num)
  simp only [InverseGate.forcing,InverseGate.forcingArg,inner_zero_left,zero_div,ht,add_zero]
  ring

theorem forcing_zero_vector_pos (y : E) : 0<InverseGate.forcing 0 y := by
  rw [forcing_zero_vector]
  norm_num [InverseGate.H₀]

theorem incoming_zero_direction_pos {r : ℝ} (hr : 0<r) (y : E) :
    LatchChain.incoming r 0 y=32*r ∧ 0<LatchChain.incoming r 0 y := by
  rw [MemoryMissJets.incoming_zero_direction]
  exact ⟨rfl,mul_pos (by norm_num) hr⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {M : ℕ}

omit [NormedSpace ℝ F] in
theorem later_weight_zero_near (port : Fin M → F → ℝ) {x : F} {i j : Fin M}
    (hij : i<j) (hi : port i =ᶠ[𝓝 x] fun _ => 0) :
    (fun z => InnerSelector.weight (fun k => port k z) j) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [hi] with z hz
  have hp : (∏ k : Fin M, if k<j then port k z else 1)=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [if_pos hij,hz])
  simp only [InnerSelector.weight,hp,mul_zero]

omit [NormedSpace ℝ F] in
theorem later_forcing_zero_near (port : Fin M → F → ℝ) (payload : F → ℝ)
    {x : F} {i j : Fin M} (hij : i<j) (hi : port i =ᶠ[𝓝 x] fun _ => 0) :
    (fun z => InnerSelector.weight (fun k => port k z) j*payload z) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [later_weight_zero_near port hij hi] with z hz
  rw [hz,zero_mul]

theorem later_forcing_richJet_zero (port : Fin M → F → ℝ) (payload : F → ℝ)
    {x : F} {i j : Fin M} (hij : i<j) (hi : port i =ᶠ[𝓝 x] fun _ => 0) :
    richJet (fun z => InnerSelector.weight (fun k => port k z) j*payload z) x=0 :=
  (richJet_congr_of_eventuallyEq (later_forcing_zero_near port payload hij hi)).trans (richJet_zero x)

end GradientHessian.GeometricMaskJets
