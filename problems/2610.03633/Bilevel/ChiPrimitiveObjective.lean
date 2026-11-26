import Bilevel.ChiPrimitiveAssembly
import Bilevel.ChiOuterCoercive

/-! Gap and variation certificates for the actual mean objective. This
connects the scalar recursive objective to the source Primitive interface. -/
noncomputable section
namespace Bilevel.ChiPrimitive
open PrimitiveGeometry Filter
open scoped Topology
variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {μ Lf Lg Cf ρ : ℝ}

def enlargeVariation (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (ρ' : ℝ) (hρ : ρ ≤ ρ') : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ' :=
  { P with
    ρ_nonneg := P.ρ_nonneg.trans hρ
    variation_yy := fun x x' y y' => (P.variation_yy x x' y y').trans
      (mul_le_mul_of_nonneg_right hρ (Real.sqrt_nonneg _))
    variation_xy := fun x x' y y' => (P.variation_xy x x' y y').trans
      (mul_le_mul_of_nonneg_right hρ (Real.sqrt_nonneg _)) }

def enlargeVariationResponse (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (ρ' : ℝ) (hρ : ρ ≤ ρ') (r : P.Response) : (enlargeVariation P ρ' hρ).Response :=
  ⟨r.y,r.minimizes⟩

theorem enlargeVariation_mean (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (ρ' : ℝ) (hρ : ρ ≤ ρ') (r : P.Response) (x : X) :
    (enlargeVariation P ρ' hρ).hyperobjective (enlargeVariationResponse P ρ' hρ r) x=P.hyperobjective r x := rfl

theorem gapCertificate_of_coercive_mean [FiniteDimensional ℝ X]
    (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ) (r : P.Response)
    (F : X → ℝ) (hF : Continuous F) (hcoer : Tendsto F (cocompact X) atTop)
    (hmean : ∀ x,P.hyperobjective r x=F x) (x₀ : X) (Δ : ℝ)
    (hgap : F x₀-sInf (Set.range F) ≤ Δ) : Nonempty (P.GapCertificate r x₀ Δ) := by
  obtain ⟨z,hz⟩ := hF.exists_forall_le hcoer
  have hbounded : BddBelow (Set.range F) := ⟨F z,by rintro _ ⟨w,rfl⟩;exact hz w⟩
  refine ⟨⟨sInf (Set.range F),?_,?_⟩⟩
  · intro x
    rw [hmean]
    exact csInf_le hbounded ⟨x,rfl⟩
  · rwa [hmean]

theorem mean_gradient_eq (P : Model.Primitive (X:=X) (Y:=Y) μ Lf Lg Cf ρ)
    (r : P.Response) (F : X → ℝ) (hmean : ∀ x,P.hyperobjective r x=F x) (x : X) :
    gradient (P.hyperobjective r) x=gradient F x := by rw [show P.hyperobjective r=F from funext hmean]

end Bilevel.ChiPrimitive
