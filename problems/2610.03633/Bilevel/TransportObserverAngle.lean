import Bilevel.TransportObserverBlock
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Deterministic angle argument behind the fresh transport block lemma.
The actual hard projection and previously determined complementary component
are bounded from source frame energy. Only the fresh complementary projection
event is left as a probabilistic prerequisite; its Haar law is not assumed or
derived from a different conditioning here. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportObserver
open ProjectionGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem project_norm_le (W : Submodule ℝ E) (z : E) : ‖project W z‖ ≤ ‖z‖ := by
  have hh := W.orthogonalProjection.le_opNorm z
  exact hh.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right W.orthogonalProjection_norm_le (norm_nonneg z))

/-- Source frame energy bounds the hard component of every source vector,
with its original norm retained. -/
theorem hard_projection_bound {ι : Type*} [Fintype ι] (H S : Submodule ℝ E)
    (b : OrthonormalBasis ι ℝ H) {e : ℝ}
    (hsource : frameEnergy S (fun i => (b i : E)) Finset.univ ≤ e)
    (v : E) (hv : v ∈ S) : ‖project H v‖ ≤ Real.sqrt e*‖v‖ := by
  have he : 0 ≤ e := (frameEnergy_nonneg S (fun i => (b i : E)) Finset.univ).trans hsource
  have hparse : ‖project H v‖^2 = ∑ i, ⟪(b i : E),v⟫^2 := by
    have hh := b.sum_sq_norm_inner (H.orthogonalProjection v)
    simpa only [Submodule.inner_orthogonalProjection_eq_of_mem_left,Real.norm_eq_abs,sq_abs] using hh.symm
  have hb (i : ι) : ⟪(b i : E),v⟫^2 ≤ energy S (b i : E)*‖v‖^2 := by
    rw [inner_project_mem S _ v hv]
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ ‖project S (b i : E)‖*‖v‖)).mpr
      (abs_real_inner_le_norm (project S (b i : E)) v)
    simpa only [sq_abs,mul_pow,energy] using hh
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  rw [← Finset.sum_mul] at hsum
  have hsq : ‖project H v‖^2 ≤ e*‖v‖^2 := by
    rw [hparse]
    exact hsum.trans (mul_le_mul_of_nonneg_right hsource (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rwa [mul_pow,Real.sq_sqrt he]

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

omit [NormedAddCommGroup G] [InnerProductSpace ℝ G] in
theorem projection_range_pairing_bound (L : F →L[ℝ] E) {a : ℝ} (ha : 0 ≤ a)
    (hlower : ∀ x, ‖x‖/2 ≤ ‖L x‖) (z : E)
    (hpair : ∀ x, |⟪L x,z⟫| ≤ a*‖x‖) :
    ‖project (LinearMap.range L.toLinearMap) z‖ ≤ 2*a := by
  let p := project (LinearMap.range L.toLinearMap) z
  obtain ⟨x,hx⟩ := project_mem (LinearMap.range L.toLinearMap) z
  change L x = p at hx
  have hnorm : ‖x‖ ≤ 2*‖p‖ := by have := hlower x; rw [hx] at this; linarith
  have hi : ⟪p,z⟫ = ‖p‖^2 := by
    dsimp [p]
    rw [project_inner,real_inner_self_eq_norm_sq]
  have hs := (le_abs_self ⟪L x,z⟫).trans (hpair x)
  rw [hx] at hs
  change ⟪p,z⟫ ≤ a*‖x‖ at hs
  rw [hi] at hs
  have hm := mul_le_mul_of_nonneg_left hnorm ha
  by_cases hp : ‖p‖ = 0
  · change ‖p‖ ≤ 2*a
    rw [hp]
    positivity
  · have hpp : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hp)
    change ‖p‖ ≤ 2*a
    nlinarith

/-- The previously disclosed complementary component costs at most 2e.
Orthogonality of the original input blocks and the actual hard projections
are sufficient; no Gram-matrix bound is postulated as a conclusion. -/
theorem old_complementary_bound (H : Submodule ℝ E) (A : F →ₗᵢ[ℝ] E) (U : G →ₗᵢ[ℝ] E)
    {e : ℝ} (he : 0 ≤ e) (hsqrt : Real.sqrt e ≤ 1/2)
    (hA : ∀ x, ‖project H (A x)‖ ≤ Real.sqrt e*‖x‖)
    (hU : ∀ u, ‖project H (U u)‖ ≤ Real.sqrt e*‖u‖)
    (horth : ∀ x u, ⟪A x,U u⟫ = 0) (u : G) :
    ‖project (LinearMap.range (innovationMap H A).toLinearMap) (innovationMap H U u)‖ ≤ 2*e*‖u‖ := by
  have hlower (x : F) : ‖x‖/2 ≤ ‖innovationMap H A x‖ :=
    innovation_singular_lower_bound H A (fun x => (hA x).trans (by
      have hh := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg x)
      linarith)) x
  have hpair (x : F) : |⟪innovationMap H A x,innovationMap H U u⟫| ≤ (e*‖u‖)*‖x‖ := by
    rw [innovationMap_apply,innovationMap_apply,residual_inner,horth,zero_sub,abs_neg]
    have hh := abs_real_inner_le_norm (project H (A x)) (project H (U u))
    have hm := mul_le_mul (hA x) (hU u) (norm_nonneg _) (by positivity : 0 ≤ Real.sqrt e*‖x‖)
    have heq : (Real.sqrt e*‖x‖)*(Real.sqrt e*‖u‖) = (e*‖u‖)*‖x‖ := by
      calc
        _ = (Real.sqrt e)^2*(‖u‖*‖x‖) := by ring
        _ = _ := by rw [Real.sq_sqrt he]; ring
    exact hh.trans (hm.trans_eq heq)
  have hh := projection_range_pairing_bound (innovationMap H A) (mul_nonneg he (norm_nonneg u))
    hlower (innovationMap H U u) hpair
  simpa only [mul_assoc] using hh

/-- Actual source geometry plus the single fresh-complement angle event imply
the deterministic projected-angle hypothesis. The event is exactly where the
future conditional Haar moment/Markov argument must attach. -/
theorem angle_of_fresh_complement (H W : Submodule ℝ E)
    (O : E ≃ₗᵢ[ℝ] E) (A : F →ₗᵢ[ℝ] E) (U : G →ₗᵢ[ℝ] E)
    {e : ℝ} (he : 0 ≤ e) (hsmall : e ≤ (1:ℝ)/4096)
    (hA : ∀ x, ‖project H (A x)‖ ≤ Real.sqrt e*‖x‖)
    (hU : ∀ u, ‖project H (U u)‖ ≤ Real.sqrt e*‖u‖)
    (horth : ∀ x u, ⟪A x,U u⟫ = 0)
    (hfresh : ∀ u, ‖project W (O (ProjectionGeometry.residual (LinearMap.range (innovationMap H A).toLinearMap)
      (innovationMap H U u)))‖ ≤ ‖u‖/8) (u : G) :
    ‖project W (O (U u))‖ ≤ ‖u‖/2 := by
  have hsqrt : Real.sqrt e ≤ 1/2 := by
    have hh := small_energy_angle_constant hsmall
    linarith
  let z := innovationMap H U u
  let R := LinearMap.range (innovationMap H A).toLinearMap
  have hold := old_complementary_bound H A U he hsqrt hA hU horth u
  have hdecomp : U u = project H (U u)+project R z+ProjectionGeometry.residual R z := by
    dsimp [ProjectionGeometry.residual,z]
    rw [innovationMap_apply]
    dsimp [ProjectionGeometry.residual]
    abel
  have hproj : project W (O (U u)) = project W (O (project H (U u)))+
      project W (O (project R z))+project W (O (ProjectionGeometry.residual R z)) := by
    nth_rw 1 [hdecomp]
    rw [O.map_add,O.map_add,project_add,project_add]
  have hnorm := (norm_add_le (project W (O (project H (U u)))+project W (O (project R z)))
    (project W (O (ProjectionGeometry.residual R z)))).trans
      (add_le_add_right (norm_add_le _ _) _)
  have hhard := (project_norm_le W (O (project H (U u)))).trans (by simpa only [O.norm_map] using hU u)
  have hold' : ‖project W (O (project R z))‖ ≤ 2*e*‖u‖ :=
    (project_norm_le W _).trans (by simpa only [O.norm_map] using hold)
  have hcoef := mul_le_mul_of_nonneg_right (small_energy_angle_constant hsmall).le (norm_nonneg u)
  rw [hproj]
  have hfr := hfresh u
  change ‖project W (O (ProjectionGeometry.residual R z))‖ ≤ ‖u‖/8 at hfr
  nlinarith

end Bilevel.TransportObserver
