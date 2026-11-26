import HeavyTail.GaussianOnlineFactorMoments
import HeavyTail.GaussianOnlineMaster
import HeavyTail.AdaptiveKernelConcentration

/-! The observable Gaussian learner on arbitrary adaptive histories.
The means may change with the complete preceding history. Its one-step
exponential bounds follow from actual centered kernel moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Classical InnerProductSpace

namespace HeavyTail.GaussianEntropy
open GaussianEstimates AdaptiveKernel
universe u v w
variable {Seed E ι : Type u} {Query : Type v} {Output : Type w}
  [MeasurableSpace Seed] [MeasurableSpace Query] [MeasurableSpace Output]
  [Fintype ι] [Nonempty ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def onlineHistoryWeights (c : E) (a η β : ℝ) (centers : ι → E)
    {ε : ℝ} (hε : 0 < ε) (initial : SimplexPoint ι) :
    (t : ℕ) → History Seed E t → SimplexPoint ι
  | 0 => fun _ => initial
  | t + 1 => fun h => gaussianOnlineUpdate E c a η β centers hε
      (onlineHistoryWeights c a η β centers hε initial t h.1, h.2)

theorem onlineHistoryWeights_measurable (c : E) (a η β : ℝ) (centers : ι → E)
    {ε : ℝ} (hε : 0 < ε) (initial : SimplexPoint ι) (t : ℕ) :
    Measurable (onlineHistoryWeights (Seed := Seed) c a η β centers hε initial t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (gaussianOnlineUpdate_measurable E c a η β centers hε).comp
        ((ih.comp measurable_fst).prodMk measurable_snd)

def predictableGaussianW (c : E) (a η : ℝ) (centers : ι → E)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E) (t : ℕ) (h : History Seed E t × E) : ℝ :=
  onlineMixtureW E c a η centers (weights t h.1).val h.2 (b t h.1)
    (finiteMixtureMean centers (weights t h.1).val)

def predictableGaussianComparator (c : E) (a η : ℝ) (centers : ι → E)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E) (q : SimplexPoint ι)
    (t : ℕ) (h : History Seed E t × E) : ℝ :=
  Real.exp (∫ u, onlineMixtureError E η h.2 (b t h.1)
    (finiteMixtureMean centers (weights t h.1).val) u
      ∂physicalGaussianMixtureLaw E c a centers q.val)

theorem predictableGaussianW_measurable (c : E) (a η : ℝ) (centers : ι → E)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E)
    (hw : ∀ t, Measurable (weights t)) (hb : ∀ t, Measurable (b t)) (t : ℕ) :
    Measurable (predictableGaussianW c a η centers weights b t) := by
  let input : History Seed E t × E → SimplexPoint ι × (E × (E × E)) := fun h =>
    (weights t h.1, h.2, b t h.1, finiteMixtureMean centers (weights t h.1).val)
  have hw' : Measurable (fun h : History Seed E t × E => weights t h.1) :=
    (hw t).comp measurable_fst
  have hz := (finiteMixtureMean centers).continuous.measurable.comp
    (measurable_subtype_coe.comp hw')
  have hin : Measurable input := hw'.prodMk
    (measurable_snd.prodMk (((hb t).comp measurable_fst).prodMk hz))
  have hm := (onlineMixtureW_measurable E c a η centers).comp hin
  simpa only [Function.comp_def, input, predictableGaussianW] using hm

theorem predictableGaussianComparator_measurable (c : E) {a : ℝ} (ha : a ≠ 0)
    (η : ℝ) (centers : ι → E)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (b : (t : ℕ) → History Seed E t → E) (q : SimplexPoint ι)
    (hw : ∀ t, Measurable (weights t)) (hb : ∀ t, Measurable (b t)) (t : ℕ) :
    Measurable (predictableGaussianComparator c a η centers weights b q t) := by
  let input : History Seed E t × E → E × (E × SimplexPoint ι) := fun h =>
    (h.2, b t h.1, weights t h.1)
  have hin : Measurable input := measurable_snd.prodMk
    (((hb t).comp measurable_fst).prodMk ((hw t).comp measurable_fst))
  have hm := ((onlineMixtureError_integral_measurable E c ha η centers q.property).comp hin).exp
  simpa only [Function.comp_def, input, predictableGaussianComparator] using hm

/-- Genuine one-step noise contract against the actual adaptive reply law.
It imposes only centering and the source strong/weak moment bounds. -/
structure PredictableNoiseContract {T : ℕ} (A : Policy Seed Query E Output T)
    (K : Kernel Query E) (b : (t : ℕ) → History Seed E t → E) (p s V M : ℝ) : Prop where
  mean_measurable : ∀ t, Measurable (b t)
  mean_bound : ∀ t h, ‖b t h‖ ≤ M
  square_integrable : ∀ t h, Integrable (fun r => ‖r - b t h‖ ^ 2) (K (A.query t h))
  centered : ∀ t h, (∫ r, r - b t h ∂K (A.query t h)) = 0
  square_bound : ∀ t h, (∫ r, ‖r - b t h‖ ^ 2 ∂K (A.query t h)) ≤ V
  weak_bound : ∀ t h v, ‖v‖ = 1 →
    (∫ r, |⟪v, r - b t h⟫_ℝ| ^ p ∂K (A.query t h)) ≤ s ^ p

theorem predictableGaussianW_moment {T : ℕ} (A : Policy Seed Query E Output T)
    (K : Kernel Query E) [IsMarkovKernel K]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R η a : ℝ}
    (H : PredictableNoiseContract A K b p s V M) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (c : E) (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι)
    (t : ℕ) (h : History Seed E t) :
    (∫ r, predictableGaussianW c a η centers weights b t (h, r) ∂K (A.query t h)) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  have hm := onlineMixtureW_moment E (P := K (A.query t h))
    (measurable_id.sub_const (b t h)) (H.square_integrable t h) (H.centered t h)
    hp hp2 hs (H.square_bound t h) (H.weak_bound t h) c (b t h)
    (finiteMixtureMean centers (weights t h).val) (H.mean_bound t h) hη ha haR htune centers
    (center_finiteMixtureMean_distance E c R centers hc (weights t h).property) (weights t h).property
  simpa only [predictableGaussianW, add_sub_cancel] using hm.2

theorem predictableGaussianComparator_moment {T : ℕ} (A : Policy Seed Query E Output T)
    (K : Kernel Query E) [IsMarkovKernel K]
    (b : (t : ℕ) → History Seed E t → E) {p s V M R η a : ℝ}
    (H : PredictableNoiseContract A K b p s V M) (hp : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s)
    (c : E) (hη : 0 ≤ η) (ha : 0 < a) (haR : a ≤ R) (htune : η * M * R ≤ 1 / 16)
    (centers : ι → E) (hc : ∀ i, ‖centers i - c‖ ≤ R)
    (weights : (t : ℕ) → History Seed E t → SimplexPoint ι) (q : SimplexPoint ι)
    (t : ℕ) (h : History Seed E t) :
    (∫ r, predictableGaussianComparator c a η centers weights b q t (h, r) ∂K (A.query t h)) ≤
      Real.exp (mixedConstant p * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) := by
  have hm := comparator_exp_error_moment E (P := K (A.query t h))
    (measurable_id.sub_const (b t h)) (H.square_integrable t h) (H.centered t h)
    hp hp2 hs (H.square_bound t h) (H.weak_bound t h) c (b t h)
    (finiteMixtureMean centers (weights t h).val) (H.mean_bound t h) hη ha haR htune centers
    (center_finiteMixtureMean_distance E c R centers hc (weights t h).property) q.property
  simpa only [predictableGaussianComparator, add_sub_cancel] using hm.2

end HeavyTail.GaussianEntropy
