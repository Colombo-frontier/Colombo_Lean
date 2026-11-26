import GradientHessian.CompactBorelSelection
import GradientHessian.NalenSubproblem
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic

/-! A jointly Borel trust-region minimizer for the literal NALEN quadratic.
The matrix is unrestricted; neither convexity nor an operator norm bound is
needed. The public radius is fixed, including the degenerate radius zero. -/

noncomputable section
namespace GradientHessian.Nalen
open Set Metric MeasureTheory
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (E →L[ℝ] E)] [BorelSpace (E →L[ℝ] E)]

abbrev QuadraticParameters (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E × (E →L[ℝ] E) × E × E × ℝ

def quadraticPolynomial (p : QuadraticParameters E) (x : E) : ℝ :=
  ⟪p.1,x⟫_ℝ+(1/4:ℝ)*⟪p.2.1 (x-p.2.2.1),x-p.2.2.1⟫_ℝ+p.2.2.2.2*‖x-p.2.2.2.1‖^2

theorem quadraticPolynomial_joint_continuous :
    Continuous (fun q : QuadraticParameters E × E => quadraticPolynomial q.1 q.2) := by
  unfold quadraticPolynomial
  fun_prop

def reciprocalParameters (p : QuadraticParameters E) : QuadraticParameters E :=
  (p.1,p.2.1,p.2.2.1,p.2.2.2.1,1/(2*p.2.2.2.2))

theorem reciprocalParameters_measurable : Measurable (reciprocalParameters (E := E)) := by
  unfold reciprocalParameters
  fun_prop

theorem quadraticPolynomial_reciprocal (p : QuadraticParameters E) (x : E) :
    quadraticPolynomial (reciprocalParameters p) x=
      quadraticModel p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 x := rfl

abbrev TrustBall (E : Type*) [NormedAddCommGroup E] (D : ℝ) :=
  ↥(closedBall (0 : E) D)

theorem quadraticPolynomial_ball_continuous (D : ℝ) :
    Continuous (fun q : QuadraticParameters E × TrustBall E D => quadraticPolynomial q.1 q.2.val) :=
  quadraticPolynomial_joint_continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

def quadraticBorelStep {D : ℝ} (hD : 0≤D) (p : QuadraticParameters E) : E := by
  letI : CompactSpace (TrustBall E D) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) D)
  letI : Nonempty (TrustBall E D) := ⟨⟨0,by simpa using hD⟩⟩
  exact (CompactBorelSelection.minimizer
    (f := fun (p : QuadraticParameters E) (x : TrustBall E D) => quadraticPolynomial p x.val)
    (quadraticPolynomial_ball_continuous (E := E) D)
    (reciprocalParameters p)).val

theorem quadraticBorelStep_measurable {D : ℝ} (hD : 0≤D) :
    Measurable (quadraticBorelStep (E := E) hD) := by
  letI : CompactSpace (TrustBall E D) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) D)
  letI : Nonempty (TrustBall E D) := ⟨⟨0,by simpa using hD⟩⟩
  exact measurable_subtype_coe.comp ((CompactBorelSelection.minimizer_measurable
    (f := fun (p : QuadraticParameters E) (x : TrustBall E D) => quadraticPolynomial p x.val)
    (quadraticPolynomial_ball_continuous (E := E) D)).comp (reciprocalParameters_measurable (E := E)))

theorem quadraticBorelStep_spec {D : ℝ} (hD : 0≤D) (p : QuadraticParameters E) :
    quadraticBorelStep hD p ∈ closedBall (0 : E) D ∧
      IsMinOn (quadraticModel p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
        (closedBall (0 : E) D) (quadraticBorelStep hD p) := by
  letI : CompactSpace (TrustBall E D) := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) D)
  letI : Nonempty (TrustBall E D) := ⟨⟨0,by simpa using hD⟩⟩
  refine ⟨(CompactBorelSelection.minimizer
    (f := fun (p : QuadraticParameters E) (x : TrustBall E D) => quadraticPolynomial p x.val)
    (quadraticPolynomial_ball_continuous (E := E) D)
    (reciprocalParameters p)).property,?_⟩
  intro x hx
  exact CompactBorelSelection.minimizer_spec
    (f := fun (p : QuadraticParameters E) (x : TrustBall E D) => quadraticPolynomial p x.val)
    (quadraticPolynomial_ball_continuous (E := E) D)
    (reciprocalParameters p) (⟨x,hx⟩ : TrustBall E D)

theorem quadraticBorelStep_variational {D η : ℝ} (hD : 0≤D) (hη : 0<η)
    (g : E) (B : E →L[ℝ] E) (δ v : E)
    (hB : ∀ x y,⟪B x,y⟫_ℝ=⟪x,B y⟫_ℝ) {u : E} (hu : u ∈ closedBall (0 : E) D) :
    let x := quadraticBorelStep hD (g,B,δ,v,η)
    0 ≤ ⟪η • (g+(1/2:ℝ) • B (x-δ))+x-v,u-x⟫_ℝ := by
  have hs := quadraticBorelStep_spec hD (g,B,δ,v,η)
  exact quadraticModel_variational hη g B δ v _ hB hs.1 hs.2 hu

theorem quadraticBorelStep_comp_measurable {Ω : Type*} [MeasurableSpace Ω] {D : ℝ} (hD : 0≤D)
    {g δ v : Ω → E} {B : Ω → E →L[ℝ] E} {η : Ω → ℝ}
    (hg : Measurable g) (hB : Measurable B) (hδ : Measurable δ) (hv : Measurable v) (hη : Measurable η) :
    Measurable (fun w => quadraticBorelStep hD (g w,B w,δ w,v w,η w)) :=
  (quadraticBorelStep_measurable hD).comp (hg.prodMk (hB.prodMk (hδ.prodMk (hv.prodMk hη))))

end GradientHessian.Nalen
