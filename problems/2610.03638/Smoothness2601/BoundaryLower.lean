import Smoothness2601.BoundaryReply
import Smoothness2601.HardLower

/-! The boundary upper-noise hard instance defeats every unrestricted
randomized algorithm, using the same verified deferred-prefix experiment. -/
noncomputable section
namespace Smoothness2601.BoundaryInstance
open MeasureTheory ProbabilityTheory
open Bilevel EuclideanGaussian ProjectionPosterior PrimitiveGeometry IndependentDraws
open ExtensiveChain PrefixSimulator DeferredPrefix
open scoped RealInnerProductSpace ENNReal

variable {b : Budgets} {s : ℝ} (hs : 0 < s) (hμL : b.μ ≤ b.L₁)
  (hsmall : s ≤ b.σ/(Cutoffs.frontierGradientBound+1))

theorem fixed_frame_expected_norm (n N : ℕ)
    (hbudget : (N : ℝ)*revealRate b s ≤ (n+1 : ℝ)/8)
    (A : Adaptive.Algorithm (Bilevel.EuclideanGaussian.Space (HardProfiles.hardDimension N n)) ℝ) :
    ∃ U : Frame (HardProfiles.hardDimension N n) (n+1), ∃ hU : Orthonormal ℝ U,
      ENNReal.ofReal (s/4) ≤ Adaptive.expectedNorm A
        (oracle (FrameTruncation.frameIsometry U hU) hs hμL hsmall) N () 0 0 := by
  let d := HardProfiles.hardDimension N n
  let reply := rawReply b s (E := Bilevel.EuclideanGaussian.Space d) (n := n)
  let point := fun q : Adaptive.Query (Bilevel.EuclideanGaussian.Space d) ℝ =>
    compressedPoint b s n q.2.1
  let outPoint := compressedPoint b s n (E := Bilevel.EuclideanGaussian.Space d)
  have hr : Measurable (fun z : Frame d (n+1) ×
      (Adaptive.Query (Bilevel.EuclideanGaussian.Space d) ℝ × Bool) => reply z.1 z.2.1 z.2.2) :=
    rawReply_measurable b s n
  have ho : Measurable outPoint := (compressedPoint_continuous b s n).measurable
  have hpoint : Measurable point := ho.comp (measurable_fst.comp measurable_snd)
  have hq0 := (revealRate_pos b hs).le
  have hq1 := revealRate_le_one b hs hsmall
  let residual := residualDimension (N+1) (n+1) (1/16) (chainRadius HardProfiles.radiusConstant n)
  have hd : (n+1)+(residual+1) ≤ d := by
    unfold d HardProfiles.hardDimension ambientDimension residual
    omega
  have hlog := residualDimension_sufficient (N+1) (n+1)
    (by norm_num : (0:ℝ) < 1/16) (HardProfiles.radius_pos n)
  obtain ⟨U,hU,hlarge⟩ := exists_orthonormal_hidden_output A reply hr point hpoint outPoint ho
    (by norm_num : (0:ℝ) < 1/16) (HardProfiles.radius_pos n) (HardProfiles.radius_ge_delta n)
    (fun q => compressedPoint_norm b s n q.2.1) (compressedPoint_norm b s n)
    (fun U k q c htail => rawReply_local b s U k q c htail)
    residual hd N (by omega) hlog (revealRate b s) hq0 hq1
    (by simpa using hbudget) (A.initialLaw (0,0))
  refine ⟨U,hU,?_⟩
  have hrU : Measurable (fun z : Adaptive.Query (Bilevel.EuclideanGaussian.Space d) ℝ × Bool =>
      reply U z.1 z.2) := hr.comp (measurable_const.prodMk measurable_id)
  have hb : ∀ x : Bilevel.EuclideanGaussian.Space d,
      (∃ i : Fin (n+1), |⟪outPoint x,U i⟫| < 1/16) →
      s/2 ≤ ‖gradient (population (FrameTruncation.frameIsometry U hU) hs hμL).objective x‖ := by
    intro x hx
    apply gradient_barrier (FrameTruncation.frameIsometry U hU) hs hμL x
    obtain ⟨i,hi⟩ := hx
    refine ⟨i,?_⟩
    rw [FrameTruncation.frameProjection_isometry,FrameTruncation.coordinates_apply,real_inner_comm]
    exact hi.trans (by norm_num)
  have he := expectedNorm_of_hidden_output A reply U hrU
    (oracle (FrameTruncation.frameIsometry U hU) hs hμL hsmall)
    (BernoulliOracle.law (revealRate b s) hq1)
    (rawReply_oracle_law hs hμL U hU hsmall hq1)
    outPoint (1/16) N (0,0) (by positivity : 0 ≤ s/2) hb hlarge.le
  convert he using 1
  congr 1
  ring

end Smoothness2601.BoundaryInstance
