import Bilevel.TransportRoundAngle

/-! Removing protected columns from the actual paired domain. Canonical
subtype isometries provide the old unprotected and new residual blocks;
all orthogonality/domain prerequisites of the protected-angle lemma follow
from subspace inclusions and the actual protected span. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.TransportRound
open EuclideanGaussian ProjectionGeometry TransportObserver TransportEdgePosterior OrthogonalAction
set_option maxHeartbeats 600000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def unprotected (A K : Submodule ℝ E) : Submodule ℝ E := A ⊓ Kᗮ

theorem protected_decomposition (A K : Submodule ℝ E) (hK : K≤A) : K ⊔ unprotected A K=A := by
  rw [unprotected,inf_comm]
  exact Submodule.sup_orthogonal_inf_of_completeSpace hK

theorem hard_unprotected (H A K : Submodule ℝ E) (hKA : K≤A) (hKH : K≤H) :
    H ⊔ unprotected A K = H ⊔ A := by
  conv_rhs => rw [← protected_decomposition A K hKA]
  rw [← sup_assoc,sup_eq_left.mpr hKH]

omit [FiniteDimensional ℝ E] in
theorem unprotected_le (A K : Submodule ℝ E) : unprotected A K≤A := inf_le_left

theorem unprotected_orthogonal (A K : Submodule ℝ E) (x : unprotected A K) (y : residualSpace A A) :
    ⟪(x : E),(y : E)⟫=0 := Submodule.inner_right_of_mem_orthogonal x.property.1 (residualSpace_perp _ _ y.property)

theorem residual_unprotected_orthogonal (A K S : Submodule ℝ E)
    (x : unprotected A K) (u : residualSpace A S) : ⟪(x : E),(u : E)⟫=0 :=
  Submodule.inner_right_of_mem_orthogonal x.property.1 (residualSpace_perp _ _ u.property)

theorem domain_append {D : ℕ} (P Q : Pairs D) : domain (P++Q)=domain P ⊔ domain Q := by
  induction P with
  | nil => simp [domain]
  | cons p P ih =>
    simp only [List.cons_append,domain,ih]
    ac_rfl

theorem range_append {D : ℕ} (P Q : Pairs D) : range (P++Q)=range P ⊔ range Q := by
  induction P with
  | nil => simp [range]
  | cons p P ih =>
    simp only [List.cons_append,range,ih]
    ac_rfl

omit [FiniteDimensional ℝ E] in
theorem subtype_range (R : Submodule ℝ E) : LinearMap.range R.subtypeₗᵢ.toLinearMap=R := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩; exact u.property
  · intro hx; exact ⟨⟨x,hx⟩,rfl⟩

theorem paired_residual_failure {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Pairs D) (H A S F W Kspace : Submodule ℝ (Space D))
    (b : OrthonormalBasis ι ℝ H) (K I : Finset ι) (hIK : I⊆Finset.univ\K)
    (hKA : Kspace≤A) (hKH : Kspace≤H) (hK : ∀ i∈K, (b i : Space D)∈Kspace)
    (hAS : A≤S) (hFS : F≤S) (hdom : domain L≤H⊔A)
    {e : ℝ} (hsource : frameEnergy S (fun i => (b i : Space D)) (Finset.univ\K)≤e)
    (hsmall : e≤(1:ℝ)/4096) (hd : 0<Module.finrank ℝ (range L)ᗮ)
    (μ : Measure (OrthogonalHaar.Group D)) [IsProbabilityMeasure μ]
    (hμ : Invariant (range L) μ) (hL : ∀ᵐ O ∂μ, Supports L O) :
    μ.real {O |
      (∃ u : residualSpace A F, ‖u‖/2 < ‖project W (O • (u : Space D))‖) ∨
      (∃ u : residualSpace A F,
        ‖innovationMap W ((isometry D O).toLinearIsometry.comp (residualSpace A F).subtypeₗᵢ) u‖ < ‖u‖/2) ∨
      8*(e+frameEnergy W (fun i => O • (b i : Space D)) I) <
        frameEnergy (W ⊔ (residualSpace A F).map (isometry D O).toLinearEquiv.toLinearMap)
          (fun i => O • (b i : Space D)) I-frameEnergy W (fun i => O • (b i : Space D)) I} ≤
      64*((Module.finrank ℝ (residualSpace A F):ℝ)*Module.finrank ℝ W /
        (Module.finrank ℝ (range L)ᗮ:ℝ)) := by
  have hA0 : ∀ x : unprotected A Kspace, (x : Space D)∈S := fun x => hAS x.property.1
  have hU : ∀ u : residualSpace A F, (u : Space D)∈S := fun u => residualSpace_local hAS hFS u.property
  have hAK : ∀ i∈K, ∀ x : unprotected A Kspace, ⟪(b i : Space D),(x : Space D)⟫=0 := by
    intro i hi x
    exact Submodule.inner_right_of_mem_orthogonal (hK i hi) x.property.2
  have hUK : ∀ i∈K, ∀ u : residualSpace A F, ⟪(b i : Space D),(u : Space D)⟫=0 := by
    intro i hi u
    exact Submodule.inner_right_of_mem_orthogonal (hKA (hK i hi)) (residualSpace_perp A F u.property)
  have hdom' : domain L≤H⊔LinearMap.range (unprotected A Kspace).subtypeₗᵢ.toLinearMap := by
    rw [subtype_range,hard_unprotected H A Kspace hKA hKH]
    exact hdom
  have hh := paired_protected_failure L H S W b K I hIK (unprotected A Kspace).subtypeₗᵢ
    (residualSpace A F).subtypeₗᵢ hsource hsmall hA0 hU hAK hUK
    (residual_unprotected_orthogonal A Kspace F) hdom' hd μ hμ hL
  have hrank : Module.finrank ℝ (LinearMap.range (residualSpace A F).subtypeₗᵢ.toLinearMap) =
      Module.finrank ℝ (residualSpace A F) :=
    congrArg (fun R : Submodule ℝ (Space D) => Module.finrank ℝ R) (subtype_range (residualSpace A F))
  rw [hrank] at hh
  simpa only [subtype_range] using hh

end Bilevel.TransportRound
