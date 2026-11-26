import Nonsmooth.GrunbaumApplication
import Mathlib.Topology.Instances.Matrix

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem basis_determinant_continuous {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ E) : Continuous (fun v : ι → E => b.det v) := by
  have hm : Continuous (fun v : ι → E => b.toMatrix v) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (b.coord i).continuous_of_finiteDimensional.comp (continuous_apply j)
  simpa only [Module.Basis.det_apply] using hm.matrix_det

theorem exists_nonzero_determinant_tuple {S : Set E} {r : ℝ} (hr : 0 < r)
    (hinner : Metric.closedBall (0 : E) r ⊆ S) :
    ∃ v : Fin (Module.finrank ℝ E) → E, (∀ i, v i ∈ S) ∧
      (stdOrthonormalBasis ℝ E).toBasis.det v ≠ 0 := by
  let b := stdOrthonormalBasis ℝ E
  refine ⟨fun i => r • b i, ?_, ?_⟩
  · intro i
    apply hinner
    simp [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, b.norm_eq_one]
  · have heq : b.toBasis.det (fun i => r • b i) = r ^ Module.finrank ℝ E := by
      have h := b.toBasis.det.toMultilinearMap.map_smul_univ (fun _ => r) b
      have hb : b.toBasis.det (⇑b) = 1 := b.toBasis.det_self
      simpa [hb] using h
    rw [heq]
    exact pow_ne_zero _ hr.ne'

/-- Maximizing determinant magnitude controls every coordinate by one. -/
theorem exists_maximal_determinant_basis {S : Set E} (hcompact : IsCompact S)
    {r : ℝ} (hr : 0 < r) (hinner : Metric.closedBall (0 : E) r ⊆ S) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, (∀ i, b i ∈ S) ∧
      ∀ x ∈ S, ∀ i, |b.repr x i| ≤ 1 := by
  classical
  let e := (stdOrthonormalBasis ℝ E).toBasis
  let P : Set (Fin (Module.finrank ℝ E) → E) := Set.pi Set.univ (fun _ => S)
  have hP : IsCompact P := isCompact_univ_pi (fun _ => hcompact)
  obtain ⟨v0, hv0, hdet0⟩ := exists_nonzero_determinant_tuple hr hinner
  have hv0P : v0 ∈ P := fun i _ => hv0 i
  obtain ⟨v, hv, hmax⟩ := hP.exists_isMaxOn ⟨v0, hv0P⟩
    (basis_determinant_continuous e).abs.continuousOn
  have hdet : e.det v ≠ 0 := by
    have hpos : 0 < |e.det v0| := abs_pos.mpr hdet0
    exact abs_pos.mp (hpos.trans_le (hmax hv0P))
  have hb := e.is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.Basis.mk hb.1 hb.2.ge
  refine ⟨b, ?_, ?_⟩
  · intro i
    simpa only [b, Module.Basis.coe_mk] using hv i (mem_univ i)
  · intro x hx i
    have hup : Function.update v i x ∈ P := by
      intro j hj
      by_cases hji : j = i
      · subst j
        simpa using hx
      · simpa [Function.update_of_ne hji] using hv j hj
    have hm := hmax hup
    change |e.det (Function.update v i x)| ≤ |e.det v| at hm
    have heq : e.det v * (b.repr x i) = e.det (Function.update v i x) := by
      have h := congrArg (fun L : E →ₗ[ℝ] ℝ => L x)
        (e.det_smul_mk_coord_eq_det_update hb.1 hb.2.ge i)
      exact h
    rw [← heq, abs_mul] at hm
    exact (mul_le_mul_iff_of_pos_left (abs_pos.mpr hdet)).mp (by simpa using hm)

end
end Nonsmooth
