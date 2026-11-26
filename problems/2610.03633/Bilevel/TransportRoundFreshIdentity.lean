import Bilevel.TransportRoundUnprotected
import Bilevel.TransportControllerPairedStore

/-! The implemented paired-domain monitor is exactly the fresh complement
used in the protected-angle proof. Thus a good measured monitor controls
the actual transport innovation and energy increment, with no extra fresh
projection event silently assumed. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open ProjectionGeometry TransportObserver TransportEdgePosterior EuclideanGaussian OrthogonalAction
set_option maxHeartbeats 600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem residual_fresh_identity (H A : Submodule ℝ E) (x : E) :
    residual (residualSpace H A) (residual H x)=residual (H⊔A) x := by
  let v := residual (residualSpace H A) (residual H x)
  have hv : v∈(H⊔A)ᗮ := freshSpace_perp H A ⊤
    ⟨residual H x,⟨x,Submodule.mem_top,rfl⟩,rfl⟩
  have hB : residualSpace H A≤H⊔A := residualSpace_local le_sup_left le_sup_right
  have hs : x-v∈H⊔A := by
    have he : x-v=project H x+project (residualSpace H A) (residual H x) := by
      dsimp [v,ProjectionGeometry.residual]; abel
    rw [he]
    exact (H⊔A).add_mem ((show H≤H⊔A from le_sup_left) (project_mem H x))
      (hB (project_mem (residualSpace H A) (residual H x)))
  have hp : project (H⊔A) x=x-v := Submodule.eq_orthogonalProjection_of_mem_orthogonal hs (by simpa using hv)
  change v=x-project (H⊔A) x
  rw [hp]
  abel

theorem freshSpace_identity (H A U : Submodule ℝ E) : freshSpace H A U=residualSpace (H⊔A) U := by
  ext x
  constructor
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    refine ⟨z,hz,?_⟩
    exact (residual_fresh_identity H A z).symm
  · rintro ⟨z,hz,rfl⟩
    refine ⟨residual H z,⟨z,hz,rfl⟩,?_⟩
    exact residual_fresh_identity H A z

theorem protected_angle_of_paired_monitor {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Pairs D) (H A S F W Kspace : Submodule ℝ (Space D))
    (b : OrthonormalBasis ι ℝ H) (K : Finset ι)
    (hKA : Kspace≤A) (hKH : Kspace≤H) (hK : ∀ i∈K, (b i : Space D)∈Kspace)
    (hAS : A≤S) (hFS : F≤S) (hdom : domain L=H⊔A)
    {e : ℝ} (hsource : frameEnergy S (fun i => (b i : Space D)) (Finset.univ\K)≤e)
    (hsmall : e≤(1:ℝ)/4096) (O : OrthogonalHaar.Group D)
    (hgood : ¬ TransportControllerEdge.angleBad W (residualSpace (domain L) (residualSpace A F)) O) :
    (∀ u : residualSpace A F, ‖project W (O • (u : Space D))‖≤‖u‖/2) ∧
      (∀ u : residualSpace A F,
        ‖u‖/2≤‖innovationMap W ((isometry D O).toLinearIsometry.comp (residualSpace A F).subtypeₗᵢ) u‖) := by
  let A0 := (unprotected A Kspace).subtypeₗᵢ
  let U := (residualSpace A F).subtypeₗᵢ
  have hfr : ∀ u, ‖project W ((isometry D O) (residual (LinearMap.range (innovationMap H A0).toLinearMap)
      (innovationMap H U u)))‖≤‖u‖/8 := by
    intro u
    let f := freshVector H A0 U u
    have hf : (f : Space D)∈residualSpace (domain L) (residualSpace A F) := by
      have he : freshSpace H (LinearMap.range A0.toLinearMap) (LinearMap.range U.toLinearMap) =
          residualSpace (domain L) (residualSpace A F) := by
        dsimp only [A0,U]
        rw [subtype_range,subtype_range,freshSpace_identity,hard_unprotected H A Kspace hKA hKH,← hdom]
      exact he.le f.property
    have hbound : ‖project W (O • (f : Space D))‖≤‖f‖/8 := le_of_not_gt (fun h => hgood ⟨⟨f,hf⟩,h⟩)
    have hn := freshVector_norm H A0 U u
    have hh := hbound.trans (div_le_div_of_nonneg_right hn (by norm_num : (0:ℝ)≤8))
    simpa only [f,freshVector,innovation_range] using hh
  apply protected_source_angle H S W b K (isometry D O) A0 U hsource hsmall
  · intro x; exact hAS x.property.1
  · intro u; exact residualSpace_local hAS hFS u.property
  · intro i hi x; exact Submodule.inner_right_of_mem_orthogonal (hK i hi) x.property.2
  · intro i hi u; exact Submodule.inner_right_of_mem_orthogonal (hKA (hK i hi)) (residualSpace_perp A F u.property)
  · exact residual_unprotected_orthogonal A Kspace F
  · exact hfr

theorem protected_energy_of_paired_monitor {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Pairs D) (H A S F W Kspace : Submodule ℝ (Space D))
    (b : OrthonormalBasis ι ℝ H) (K I : Finset ι) (hIK : I⊆Finset.univ\K)
    (hKA : Kspace≤A) (hKH : Kspace≤H) (hK : ∀ i∈K, (b i : Space D)∈Kspace)
    (hAS : A≤S) (hFS : F≤S) (hdom : domain L=H⊔A)
    {e : ℝ} (hsource : frameEnergy S (fun i => (b i : Space D)) (Finset.univ\K)≤e)
    (hsmall : e≤(1:ℝ)/4096) (O : OrthogonalHaar.Group D)
    (hgood : ¬ TransportControllerEdge.angleBad W (residualSpace (domain L) (residualSpace A F)) O) :
    frameEnergy (W⊔(residualSpace A F).map (isometry D O).toLinearEquiv.toLinearMap)
        (fun i => O • (b i : Space D)) I-frameEnergy W (fun i => O • (b i : Space D)) I ≤
      8*(e+frameEnergy W (fun i => O • (b i : Space D)) I) := by
  have ha := (protected_angle_of_paired_monitor L H A S F W Kspace b K hKA hKH hK hAS hFS
    hdom hsource hsmall O hgood).1
  apply transported_frame_energy_update (isometry D O) W (residualSpace A F) S
    (residualSpace_local hAS hFS) (fun i => (b i : Space D)) I (Finset.univ\K) hIK hsource
  rintro x ⟨u,hu,rfl⟩
  have hh := ha ⟨u,hu⟩
  change ‖project W ((isometry D O) u)‖≤‖(isometry D O) u‖/2
  rw [(isometry D O).norm_map]
  exact hh

end Bilevel.TransportRound
