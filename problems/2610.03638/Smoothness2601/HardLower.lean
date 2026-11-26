import Smoothness2601.HardReply
import Smoothness2601.KernelRisk
import Smoothness2601.DimensionRate

/-! The hard family defeats every unrestricted randomized finite-budget
algorithm. All response locality, Haar tails, and execution-law identities
are proved for the actual constructed source functions. -/
noncomputable section
namespace Smoothness2601.HardProfiles
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open ExtensiveChain PrefixSimulator DeferredPrefix
open scoped RealInnerProductSpace ENNReal

variable {b : Budgets} {M Λ β : ℝ} (W : WidthConstants b M Λ β)
variable {p : WithTop ℕ} (hp : 1 ≤ p) (hβ : 0 ≤ β) {s : ℝ} (hs : 0 < s) (hsδ : s ≤ W.threshold)

theorem fixed_frame_expected_norm (n d residual N : ℕ)
    (hd : (n+1)+(residual+1) ≤ d)
    (hlog : Real.log (16*((N+1 : ℕ) : ℝ)*(n+1)) ≤
      (residual : ℝ)*(1/16 : ℝ)^2/(8*(chainRadius radiusConstant n)^2))
    (hbudget : (N : ℝ)*revealRate W p s ≤ (n+1 : ℝ)/8)
    (A : Adaptive.Algorithm (Bilevel.EuclideanGaussian.Space d) ℝ) :
    ∃ U : Frame d (n+1), ∃ hU : Orthonormal ℝ U,
      ENNReal.ofReal (s/8) ≤ Adaptive.expectedNorm A
        (oracle W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU)) N () 0 0 := by
  let reply := rawReply W p s (E := Bilevel.EuclideanGaussian.Space d) (n := n)
  let point := fun q : Adaptive.Query (Bilevel.EuclideanGaussian.Space d) ℝ =>
    compressedPoint W s n q.2.1
  let outPoint := compressedPoint W s n (E := Bilevel.EuclideanGaussian.Space d)
  have hr : Measurable (fun z : Frame d (n+1) ×
      (Adaptive.Query (Bilevel.EuclideanGaussian.Space d) ℝ × Bool) => reply z.1 z.2.1 z.2.2) :=
    rawReply_measurable W p s n
  have ho : Measurable outPoint := (compressedPoint_continuous W s n).measurable
  have hpoint : Measurable point := ho.comp (measurable_fst.comp measurable_snd)
  have hq0 := (revealRate_pos W hp hβ hs hsδ).le
  have hq1 := revealRate_le_one W hp hβ hs hsδ
  obtain ⟨U,hU,hlarge⟩ := exists_orthonormal_hidden_output A reply hr point hpoint outPoint ho
    (by norm_num : (0:ℝ) < 1/16) (radius_pos n) (radius_ge_delta n)
    (fun q => compressedPoint_norm W s n q.2.1) (compressedPoint_norm W s n)
    (fun U k q c htail => rawReply_local W p s U k q c htail)
    residual hd N (by omega) (by simpa using hlog)
    (revealRate W p s) hq0 hq1 (by simpa using hbudget) (A.initialLaw (0,0))
  refine ⟨U,hU,?_⟩
  have hrU : Measurable (fun z : Adaptive.Query (Bilevel.EuclideanGaussian.Space d) ℝ × Bool =>
      reply U z.1 z.2) := hr.comp (measurable_const.prodMk measurable_id)
  have hb : ∀ x : Bilevel.EuclideanGaussian.Space d,
      (∃ i : Fin (n+1), |⟪outPoint x,U i⟫| < 1/16) →
      s/4 ≤ ‖gradient (population W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU)).objective x‖ := by
    intro x hx
    apply gradient_barrier W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU) x
    obtain ⟨i,hi⟩ := hx
    refine ⟨i,?_⟩
    rw [FrameTruncation.frameProjection_isometry,FrameTruncation.coordinates_apply,real_inner_comm]
    exact hi.trans (by norm_num)
  have he := expectedNorm_of_hidden_output A reply U hrU
    (oracle W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU))
    (BernoulliOracle.law (revealRate W p s) hq1)
    (rawReply_oracle_law W hp hβ hs hsδ U hU hq1)
    outPoint (1/16) N (0,0) (by positivity : 0 ≤ s/4) hb hlarge.le
  convert he using 1
  congr 1
  ring

def hardDimension (N n : ℕ) : ℕ :=
  ambientDimension (N+1) (n+1) (1/16) (chainRadius radiusConstant n)

theorem fixed_frame_expected_norm_chosen_dimension (n N : ℕ)
    (hbudget : (N : ℝ)*revealRate W p s ≤ (n+1 : ℝ)/8)
    (A : Adaptive.Algorithm (Bilevel.EuclideanGaussian.Space (hardDimension N n)) ℝ) :
    ∃ U : Frame (hardDimension N n) (n+1), ∃ hU : Orthonormal ℝ U,
      ENNReal.ofReal (s/8) ≤ Adaptive.expectedNorm A
        (oracle W hp hβ hs hsδ (FrameTruncation.frameIsometry U hU)) N () 0 0 := by
  apply fixed_frame_expected_norm W hp hβ hs hsδ n (hardDimension N n)
    (residualDimension (N+1) (n+1) (1/16) (chainRadius radiusConstant n)) N
  · unfold hardDimension ambientDimension
    omega
  · simpa using residualDimension_sufficient (N+1) (n+1)
      (by norm_num : (0:ℝ) < 1/16) (radius_pos n)
  · exact hbudget

end Smoothness2601.HardProfiles
