import SampleReuse.RandomFrameReduction
import SampleReuse.CurvatureRadialExclusion

/-! A genuine fixed-cap lower bound for the actual radial scalar loss and its
full value/gradient/Hessian oracle. Every probabilistic and derivative premise
has been discharged; the remaining hypotheses are explicit numeric budgets
and measurability of the unrestricted algorithm. -/

noncomputable section
namespace SampleReuse.RandomFrame

open MeasureTheory SecondOrder RandomizedFO2003 Rotations

variable {Ω : Type*} [MeasurableSpace Ω]

theorem curvature_radial_fixed_cap_tail {d T N : ℕ} (hN : N < T+1)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      query n p.1 p.2))
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {A β b ε γ R t : ℝ}
    (hA : 0 ≤ A) (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 < R) (hγ : 0 < γ)
    (ht : 0 < t) (hβt : β*t ≤ 1/2)
    (hnegative : 8*γ ≤ A*β^2*Real.exp (-(9:ℝ)/4))
    (hwall : 2*b/R ≤ γ)
    (htransverse : 4*(A*β^2*curvatureCoreConstant)/(β*R) ≤ γ)
    (hexterior : ε < b-A*β*(curvatureCoreConstant*Real.sqrt (T+1:ℕ)))
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (ho : Measurable (fun p : Ω × (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      output p.1 p.2)) :
    (μ.prod (haarLaw (Point d))).real {p |
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U p.2) A β) b R) ε γ
        (radialFullOutput query (rotatedEmbedding U p.2) A β b R N output p.1)} ≤
      (((T+1 : ℕ) : ℝ) * (N+1)) *
        (2 * Real.exp (-((d-N : ℕ) : ℝ) * t ^ 2 / (2 * (2*R) ^ 2))) := by
  apply radial_fixed_cap_success_bound hN μ query hq U A β b ε γ hR ht hβ.le hβt output ho
  intro V x hs
  exact curvature_radial_sosp_completed (rotatedEmbedding U V) hA hβ hb hR hγ
    hnegative hwall htransverse hexterior hs

theorem curvature_radial_fixed_cap_confidence {d T N : ℕ} (hN : N < T+1)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (query : ∀ n, Ω → (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (hq : ∀ n, Measurable (fun p : Ω × (Fin n → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      query n p.1 p.2))
    (U : Point (T+1) →ₗᵢ[ℝ] Point d) {A β b ε γ R t δ : ℝ}
    (hA : 0 ≤ A) (hβ : 0 < β) (hb : 0 ≤ b) (hR : 0 < R) (hγ : 0 < γ)
    (ht : 0 < t) (hβt : β*t ≤ 1/2) (hδ : 0 < δ)
    (hnegative : 8*γ ≤ A*β^2*Real.exp (-(9:ℝ)/4))
    (hwall : 2*b/R ≤ γ)
    (htransverse : 4*(A*β^2*curvatureCoreConstant)/(β*R) ≤ γ)
    (hexterior : ε < b-A*β*(curvatureCoreConstant*Real.sqrt (T+1:ℕ)))
    (hdim : 2*(2*R)^2*Real.log (2*((T+1)*(N+1):ℕ)/δ) ≤ ((d-N:ℕ):ℝ)*t^2)
    (output : Ω → (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) → Point d)
    (ho : Measurable (fun p : Ω × (Fin N → ℝ × Point d × (Point d →L[ℝ] Point d)) =>
      output p.1 p.2)) :
    (μ.prod (haarLaw (Point d))).real {p |
      IsSOSP (radialGlobalization (curvatureFrameCore (rotatedEmbedding U p.2) A β) b R) ε γ
        (radialFullOutput query (rotatedEmbedding U p.2) A β b R N output p.1)} ≤ δ := by
  apply (curvature_radial_fixed_cap_tail hN μ query hq U hA hβ hb hR hγ ht hβt
    hnegative hwall htransverse hexterior output ho).trans
  have hc := spherical_union_confidence ((T+1)*(N+1)) (d-N)
    (show 0 < 2*R by positivity) hδ hdim
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hc

end SampleReuse.RandomFrame
