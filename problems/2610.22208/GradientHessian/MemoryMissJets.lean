import GradientHessian.LatchDerivativeSums
import GradientHessian.JetLocality

/-! Literal old/inner memory misses. The gates have an open zero plateau,
the hidden self block becomes its public quadratic, and the incoming function
is explicitly not erased merely by replacing a direction with zero. -/

noncomputable section
namespace GradientHessian.MemoryMissJets
open Filter JetLocality EuclideanRegisters
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem readout_miss_near (L : F →L[ℝ] E) (r : ℝ) (v : E) (x : F)
    (hmiss : |LatchChain.u r v (L x)| ≤ 1/8) :
    ∀ᶠ z in 𝓝 x, LatchChain.u r v (L z) < 1/4 := by
  have hlt : LatchChain.u r v (L x)<1/4 := by
    have h := (le_abs_self _).trans hmiss
    linarith
  exact (((LatchChain.u_contDiff r v).continuous.comp L.continuous).continuousAt).preimage_mem_nhds
    (gt_mem_nhds hlt)

theorem chi_zero_near (L : F →L[ℝ] E) (r : ℝ) (v : E) (x : F)
    (hmiss : |LatchChain.u r v (L x)| ≤ 1/8) :
    (fun z => Profiles.chi (LatchChain.u r v (L z))) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [readout_miss_near L r v x hmiss] with z hz
  exact Profiles.chi_zero hz.le

theorem varpi_zero_near (L : F →L[ℝ] E) (r : ℝ) (v : E) (x : F)
    (hmiss : |LatchChain.u r v (L x)| ≤ 1/8) :
    (fun z => Profiles.varpi (LatchChain.u r v (L z))) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [readout_miss_near L r v x hmiss] with z hz
  exact Profiles.varpi_zero (by linarith)

theorem chi_richJet_zero (L : F →L[ℝ] E) (r : ℝ) (v : E) (x : F)
    (hmiss : |LatchChain.u r v (L x)| ≤ 1/8) :
    richJet (fun z => Profiles.chi (LatchChain.u r v (L z))) x = 0 :=
  (richJet_congr_of_eventuallyEq (chi_zero_near L r v x hmiss)).trans (richJet_zero x)

theorem varpi_richJet_zero (L : F →L[ℝ] E) (r : ℝ) (v : E) (x : F)
    (hmiss : |LatchChain.u r v (L x)| ≤ 1/8) :
    richJet (fun z => Profiles.varpi (LatchChain.u r v (L z))) x = 0 :=
  (richJet_congr_of_eventuallyEq (varpi_zero_near L r v x hmiss)).trans (richJet_zero x)

theorem self_eq_public_of_zero_gates (n : ℕ) (v : Fin (n+1) → E) (r : Fin (n+1) → ℝ)
    (hr : ∀ i, r i≠0) (U : Registers E (n+1))
    (hg : ∀ i, Profiles.chi (LatchChain.u (r i) (v i) (U i))=0) :
    LatchChain.self n v r 0 U = LatchChain.publicQuadratic n r U := by
  rw [LatchDerivativeSums.self_eq_sums n v r hr]
  simp only [LatchDerivativeSums.selfSum, LatchDerivativeSums.selfTerm,
    LatchLocalDerivatives.selfResidual, LatchDerivativeSums.edgeSum,
    LatchDerivativeSums.edgeTerm, hg, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, sub_zero]

theorem self_near_public (n : ℕ) (L : F →L[ℝ] Registers E (n+1))
    (v : Fin (n+1) → E) (r : Fin (n+1) → ℝ) (hr : ∀ i, r i≠0) (x : F)
    (hmiss : ∀ i, |LatchChain.u (r i) (v i) (L x i)| ≤ 1/8) :
    (fun z => LatchChain.self n v r 0 (L z)) =ᶠ[𝓝 x] fun z => LatchChain.publicQuadratic n r (L z) := by
  have hg (i : Fin (n+1)) : ∀ᶠ z in 𝓝 x, Profiles.chi (LatchChain.u (r i) (v i) (L z i))=0 :=
    chi_zero_near ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n+1) => E) i).comp L) (r i) (v i) x (hmiss i)
  filter_upwards [Filter.eventually_all.mpr hg] with z hz
  exact self_eq_public_of_zero_gates n v r hr (L z) hz

theorem self_richJet_public (n : ℕ) (L : F →L[ℝ] Registers E (n+1))
    (v : Fin (n+1) → E) (r : Fin (n+1) → ℝ) (hr : ∀ i, r i≠0) (x : F)
    (hmiss : ∀ i, |LatchChain.u (r i) (v i) (L x i)| ≤ 1/8) :
    richJet (fun z => LatchChain.self n v r 0 (L z)) x =
      richJet (fun z => LatchChain.publicQuadratic n r (L z)) x :=
  richJet_congr_of_eventuallyEq (self_near_public n L v r hr x hmiss)

theorem port_zero_near (n : ℕ) (L : F →L[ℝ] Registers E (n+1))
    (v : Fin (n+1) → E) (r : Fin (n+1) → ℝ) (x : F)
    (hmiss : |LatchChain.u (r (Fin.last n)) (v (Fin.last n)) (L x (Fin.last n))| ≤ 1/8) :
    (fun z => LatchChain.port n v r (L z)) =ᶠ[𝓝 x] fun _ => 0 :=
  varpi_zero_near ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n+1) => E) (Fin.last n)).comp L)
    (r (Fin.last n)) (v (Fin.last n)) x hmiss

theorem port_richJet_zero (n : ℕ) (L : F →L[ℝ] Registers E (n+1))
    (v : Fin (n+1) → E) (r : Fin (n+1) → ℝ) (x : F)
    (hmiss : |LatchChain.u (r (Fin.last n)) (v (Fin.last n)) (L x (Fin.last n))| ≤ 1/8) :
    richJet (fun z => LatchChain.port n v r (L z)) x = 0 :=
  (richJet_congr_of_eventuallyEq (port_zero_near n L v r x hmiss)).trans (richJet_zero x)

theorem incoming_zero_direction (r : ℝ) (x : E) : LatchChain.incoming r 0 x = 32*r := by
  have hu : LatchChain.u r (0:E) x = 0 := by simp [LatchChain.u, LatchActivation.readout]
  have he : IntegralProfiles.ell₀ 0=4 := by
    simpa using IntegralProfiles.ell₀_identity (t := 0) (by norm_num)
  simp [LatchChain.incoming, hu, Profiles.chi_zero (by norm_num : (0:ℝ)≤1/4), he]
  ring

end GradientHessian.MemoryMissJets
