import Mathlib
import PaperAudit.Frontier09

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: BorelCubicOptimizerCertificate.lean

namespace OriginalBorelOuterCubic
open MeasureTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

/-- This is the optimizer actually called by the new cubic trajectory. It is Borel
in both returned model coefficients, including all nonunique-minimum cases. -/
theorem executed_optimizer_measurable (M : ℝ) (hM : 0 < M) :
    Measurable (fun p : E × (E →L[ℝ] E) => minimizer p.1 p.2 M) := by
  simpa only [minimizer,dif_pos hM] using OriginalCubicBorelSelection.select_measurable (E := E) M hM

end
end OriginalBorelOuterCubic
end

section
-- Source component: BorelTaylorProxStep.lean

open MeasureTheory

namespace OriginalBorelTaylorProx
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

def NonnegativeQuadratic (H : E →L[ℝ] E) : Prop := ∀ d : E, 0 ≤ inner ℝ (H d) d

theorem nonnegative_quadratic_closed :
    IsClosed {H : E →L[ℝ] E | NonnegativeQuadratic H} := by
  simp only [NonnegativeQuadratic,Set.setOf_forall]
  apply isClosed_iInter
  intro d
  have heval : Continuous (fun H : E →L[ℝ] E => H d) := by fun_prop
  exact isClosed_le continuous_const (heval.inner continuous_const)

def safeHessian (H : E →L[ℝ] E) : {K : E →L[ℝ] E | NonnegativeQuadratic K} :=
  ⟨if NonnegativeQuadratic H then H else 0,by
    by_cases h : NonnegativeQuadratic H
    · simpa only [Set.mem_setOf_eq,if_pos h] using h
    · simp only [Set.mem_setOf_eq,if_neg h]
      intro d
      simp⟩

def safeLambda (lam : ℝ) : {t : ℝ | 0 < t} :=
  ⟨if 0 < lam then lam else 1,by split_ifs with h; exact h; norm_num⟩

theorem safe_hessian_measurable : Measurable (safeHessian (E := E)) := by
  exact (Measurable.ite nonnegative_quadratic_closed.measurableSet measurable_id measurable_const).subtype_mk

theorem safe_lambda_measurable : Measurable safeLambda := by
  exact (Measurable.ite measurableSet_Ioi measurable_id measurable_const).subtype_mk

abbrev Parameter (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  (E × {H : E →L[ℝ] E | NonnegativeQuadratic H}) × {lam : ℝ | 0 < lam}

def modelFamily (M : ℝ) (q : Parameter E × E) : ℝ :=
  CertifiedATS.model q.1.1.1 q.1.1.2.1 M q.1.2.1 q.2

theorem model_family_continuous (M : ℝ) : Continuous (modelFamily (E := E) M) := by
  unfold modelFamily CertifiedATS.model
  have hden : ∀ q : Parameter E × E, (2:ℝ)*(q.1.2:ℝ) ≠ 0 :=
    fun q => mul_ne_zero (by norm_num) (ne_of_gt q.1.2.2)
  fun_prop

theorem model_family_has_minimum (M : ℝ) (hM : 0 ≤ M) (p : Parameter E) :
    ∃ d : E, OriginalMeasurableArgmin.IsMin (modelFamily M) p d := by
  refine ⟨OriginalTaylorProxStability.exactStep p.1.1 p.1.2 M p.2,?_⟩
  exact OriginalTaylorProxStability.exactStep_minimizes p.1.1 p.1.2 M p.2 0 hM p.2.2 le_rfl
    (fun d => by simpa only [zero_mul] using p.1.2.2 d)

/-- A total Borel extension on the full coefficient/answer space. Illegal
quadratic or lambda inputs are mapped to the fixed zero-Hessian/positive-lambda
parameter before applying the explicit Borel argmin selector. On every legal
ATS input the retraction is the identity. M=0 is included. -/
def step (M : ℝ) (hM : 0 ≤ M) (v : E) (H : E →L[ℝ] E) (lam : ℝ) : E :=
  OriginalMeasurableArgmin.selector (modelFamily M) (model_family_continuous M)
    (model_family_has_minimum M hM) ((v,safeHessian H),safeLambda lam)

theorem step_measurable (M : ℝ) (hM : 0 ≤ M) :
    Measurable (fun p : (E × (E →L[ℝ] E)) × ℝ => step M hM p.1.1 p.1.2 p.2) := by
  have hp : Measurable (fun p : (E × (E →L[ℝ] E)) × ℝ =>
      ((p.1.1,safeHessian p.1.2),safeLambda p.2)) :=
    (measurable_fst.fst.prodMk (safe_hessian_measurable.comp measurable_fst.snd)).prodMk
      (safe_lambda_measurable.comp measurable_snd)
  exact (OriginalMeasurableArgmin.selector_measurable (modelFamily M) (model_family_continuous M)
    (model_family_has_minimum M hM)).comp hp

theorem step_eq_original_on_legal_coefficients
    (M : ℝ) (hM : 0 ≤ M) (v : E) (H : E →L[ℝ] E) (lam : ℝ)
    (hH : NonnegativeQuadratic H) (hlam : 0 < lam) :
    step M hM v H lam = OriginalTaylorProxStability.exactStep v H M lam := by
  have hm := OriginalMeasurableArgmin.selector_is_min (modelFamily M) (model_family_continuous M)
    (model_family_has_minimum M hM) ((v,safeHessian H),safeLambda lam)
  have hmin : ∀ w : E,
      CertifiedATS.model v H M lam (step M hM v H lam) ≤ CertifiedATS.model v H M lam w := by
    simpa only [step,OriginalMeasurableArgmin.IsMin,modelFamily,safeHessian,safeLambda,
      if_pos hH,if_pos hlam] using hm
  exact OriginalBetaATSTrial.exactStep_unique v H M lam 0 hM hlam le_rfl
    (fun d => by simpa only [zero_mul] using hH d) _ hmin

/-- Same argument order as the executed legacy exactStep; fixed public negative
M is extended by zero. Every legal M>=0 uses the proved Borel selector. -/
def totalStep (v : E) (H : E →L[ℝ] E) (M lam : ℝ) : E :=
  if hM : 0 ≤ M then step M hM v H lam else 0

theorem total_step_measurable (M : ℝ) :
    Measurable (fun p : (E × (E →L[ℝ] E)) × ℝ => totalStep p.1.1 p.1.2 M p.2) := by
  by_cases hM : 0 ≤ M
  · simpa only [totalStep,dif_pos hM] using step_measurable M hM
  · simpa only [totalStep,dif_neg hM] using (measurable_const : Measurable
      (fun _ : (E × (E →L[ℝ] E)) × ℝ => (0:E)))

theorem total_step_eq_original
    (v : E) (H : E →L[ℝ] E) (M lam : ℝ) (hM : 0 ≤ M)
    (hH : NonnegativeQuadratic H) (hlam : 0 < lam) :
    totalStep v H M lam = OriginalTaylorProxStability.exactStep v H M lam := by
  simpa only [totalStep,dif_pos hM] using step_eq_original_on_legal_coefficients M hM v H lam hH hlam

theorem total_step_minimizes
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hmu : 0 ≤ mu) (hcoer : ∀ d : E, mu*‖d‖^2 ≤ inner ℝ (H d) d) :
    ∀ w : E, CertifiedATS.model v H M lam (totalStep v H M lam) ≤ CertifiedATS.model v H M lam w := by
  have hH : NonnegativeQuadratic H := fun d =>
    (mul_nonneg hmu (sq_nonneg ‖d‖)).trans (hcoer d)
  rw [total_step_eq_original v H M lam hM hH hlam]
  exact OriginalTaylorProxStability.exactStep_minimizes v H M lam mu hM hlam hmu hcoer

end
end OriginalBorelTaylorProx
end

section
-- Source component: BorelWarmReplay.lean

namespace OriginalBorelWarmReplay
namespace OriginalTaylorProxStability
open _root_.OriginalTaylorProxStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def proxGradient (v : E) (H : E →L[ℝ] E) (M lam : ℝ) (d : E) : E :=
  v + CertifiedATS.sympart H d + (M / 2 * ‖d‖) • d + lam⁻¹ • d

noncomputable def exactStep (v : E) (H : E →L[ℝ] E) (M lam : ℝ) : E :=
  _root_.OriginalBorelTaylorProx.totalStep v H M lam

theorem model_strongConvex_with_prox
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    StrongConvexOn (Set.univ : Set E) (mu + lam⁻¹) (CertifiedATS.model v H M lam) := by
  let K := H + lam⁻¹ • ContinuousLinearMap.id ℝ E
  have hK : ∀ d : E, (mu + lam⁻¹) * ‖d‖ ^ 2 ≤ inner ℝ (K d) d := by
    intro d
    change (mu + lam⁻¹) * ‖d‖ ^ 2 ≤ inner ℝ (H d + lam⁻¹ • d) d
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith only [hcoer d]
  have hlin : ConvexOn ℝ (Set.univ : Set E) (fun d => inner ℝ v d) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [inner_add_right, inner_smul_right, smul_eq_mul, le_refl]
  have hcub : ConvexOn ℝ (Set.univ : Set E) (fun d => M / 6 * ‖d‖ ^ 3) := by
    simpa only [Pi.pow_apply, smul_eq_mul] using
      ConvexOn.smul (by positivity : 0 ≤ M / 6)
        (convexOn_univ_norm.pow (fun d _ => norm_nonneg d) 3)
  have hq := strongConvexOn_iff_convex.mp (CertifiedATS.quadratic_strongConvex K (mu + lam⁻¹) hK)
  have hh := (hq.add hlin).add hcub
  apply strongConvexOn_iff_convex.mpr
  convert! hh using 1
  funext d
  simp only [Pi.add_apply, CertifiedATS.model, K, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, inner_add_left, real_inner_smul_left]
  rw [real_inner_self_eq_norm_sq]
  field_simp <;> ring

theorem exactStep_minimizes
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    ∀ w : E, CertifiedATS.model v H M lam (exactStep v H M lam) ≤ CertifiedATS.model v H M lam w := by
  exact _root_.OriginalBorelTaylorProx.total_step_minimizes v H M lam mu hM hlam hmu hcoer

theorem exactStep_first_order
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    proxGradient v H M lam (exactStep v H M lam) = 0 := by
  exact CertifiedATS.model_minimum_first_order v H M lam _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer)

theorem distance_from_scaled_residual
    (v : E) (H : E →L[ℝ] E) (M lam mu sigma : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hres : ‖lam • proxGradient v H M lam d‖ ≤ sigma * ‖d‖) :
    ‖d - exactStep v H M lam‖ ≤ sigma * ‖d‖ := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d
  rw [(CertifiedATS.model_hasGradientAt v H M lam d).gradient] at hs
  have hscaled := mul_le_mul_of_nonneg_left hs hlam.le
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hres
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hlam)
  have hnonneg : 0 ≤ lam * mu * ‖d - exactStep v H M lam‖ := by positivity
  change lam * ((mu + lam⁻¹) * ‖d - exactStep v H M lam‖) ≤
    lam * ‖proxGradient v H M lam d‖ at hscaled
  change lam * ‖proxGradient v H M lam d‖ ≤ sigma * ‖d‖ at hres
  have hcoeff : lam * (mu + lam⁻¹) = lam * mu + 1 := by rw [mul_add, hinv]
  rw [← mul_assoc, hcoeff] at hscaled
  nlinarith only [hscaled, hres, hnonneg]

theorem approximate_norm_bracket
    (v : E) (H : E →L[ℝ] E) (M lam mu sigma : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hres : ‖lam • proxGradient v H M lam d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * ‖d‖ ≤ ‖exactStep v H M lam‖ ∧
      ‖exactStep v H M lam‖ ≤ (1 + sigma) * ‖d‖ := by
  have hd := distance_from_scaled_residual v H M lam mu sigma hM hlam hmu hcoer d hres
  have h1 := norm_le_norm_sub_add d (exactStep v H M lam)
  have h2 := norm_le_norm_sub_add (exactStep v H M lam) d
  rw [norm_sub_rev (exactStep v H M lam) d] at h2
  constructor <;> nlinarith only [hd, h1, h2]

theorem exactStep_size_bound
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d) :
    (mu + lam⁻¹) * ‖exactStep v H M lam‖ ≤ ‖v‖ := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) (0 : E)
  rw [(CertifiedATS.model_hasGradientAt v H M lam 0).gradient] at hs
  simpa only [zero_sub, norm_neg, map_zero, norm_zero, zero_smul, smul_zero, mul_zero, add_zero] using hs


theorem parameter_stability
    (v v' : E) (H H' : E →L[ℝ] E) (M lam lam' mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hlam' : 0 < lam') (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (hcoer' : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H' d) d) :
    (mu + lam⁻¹) * ‖exactStep v H M lam - exactStep v' H' M lam'‖ ≤
      ‖v - v'‖ + (‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ + |lam⁻¹ - lam'⁻¹|) *
        ‖exactStep v' H' M lam'‖ := by
  let d' := exactStep v' H' M lam'
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d'
  rw [(CertifiedATS.model_hasGradientAt v H M lam d').gradient, norm_sub_rev d'] at hs
  have hz := exactStep_first_order v' H' M lam' mu hM hlam' hmu hcoer'
  have heq : proxGradient v H M lam d' = (v - v') +
      (CertifiedATS.sympart H - CertifiedATS.sympart H') d' + (lam⁻¹ - lam'⁻¹) • d' := by
    have heq0 : proxGradient v H M lam d' - proxGradient v' H' M lam' d' =
        (v - v') + (CertifiedATS.sympart H - CertifiedATS.sympart H') d' +
          (lam⁻¹ - lam'⁻¹) • d' := by
      dsimp [proxGradient]
      simp only [sub_apply, sub_smul]
      abel
    rw [hz, sub_zero] at heq0
    exact heq0
  change (mu + lam⁻¹) * ‖exactStep v H M lam - d'‖ ≤ ‖proxGradient v H M lam d'‖ at hs
  rw [heq] at hs
  have hnorm : ‖(v - v') + (CertifiedATS.sympart H - CertifiedATS.sympart H') d' +
      (lam⁻¹ - lam'⁻¹) • d'‖ ≤
      ‖v - v'‖ + (‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ + |lam⁻¹ - lam'⁻¹|) * ‖d'‖ := by
    calc
      _ ≤ ‖v - v'‖ + ‖(CertifiedATS.sympart H - CertifiedATS.sympart H') d'‖ +
          ‖(lam⁻¹ - lam'⁻¹) • d'‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖v - v'‖ + ‖CertifiedATS.sympart H - CertifiedATS.sympart H'‖ * ‖d'‖ +
          |lam⁻¹ - lam'⁻¹| * ‖d'‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact ContinuousLinearMap.le_opNorm (CertifiedATS.sympart H - CertifiedATS.sympart H') d' 
      _ = _ := by ring
  exact hs.trans hnorm

end OriginalTaylorProxStability


namespace OriginalBetaCurveBounds
open _root_.OriginalBetaCurveBounds

open OriginalCoupledBetaAlgebra
open OriginalTaylorProxStability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem lambda_compact_bounds
    (A s t b : ℝ) (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hsb : s ≤ b) (hbt : b ≤ 1 - t) :
    A * s ^ 2 ≤ lambda A b ∧ lambda A b ≤ A / t := by
  have hb : 0 ≤ b := hs.le.trans hsb
  have hb1 : b < 1 := by linarith
  have hden : 0 < 1 - b := by linarith
  have hsquare : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.le hb).mpr hsb
  have hbSquare : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  constructor
  · apply (le_div_iff₀ hden).mpr
    have h1 := mul_le_mul_of_nonneg_left (show 1 - b ≤ 1 by linarith) (by positivity : 0 ≤ A * s ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hsquare hA.le
    nlinarith only [h1, h2]
  · have hnum : A * b ^ 2 ≤ A := by nlinarith only [mul_le_mul_of_nonneg_left hbSquare hA.le]
    have hinv : 1 / (1 - b) ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith)
    change A * b ^ 2 / (1 - b) ≤ A / t
    calc
      _ = (A * b ^ 2) * (1 / (1 - b)) := by ring
      _ ≤ A * (1 / t) := mul_le_mul hnum hinv (by positivity) hA.le
      _ = A / t := by ring

theorem reciprocal_lipschitz (a b m : ℝ) (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |a⁻¹ - b⁻¹| ≤ |a - b| / m ^ 2 := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm b a]
  have hprod : m ^ 2 ≤ a * b := by nlinarith only [mul_le_mul ha hb hm.le ha0.le]
  have hinv : 1 / (a * b) ≤ 1 / m ^ 2 := one_div_le_one_div_of_le (sq_pos_of_pos hm) hprod
  calc
    _ = |a - b| * (1 / (a * b)) := by ring
    _ ≤ |a - b| * (1 / m ^ 2) := mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
    _ = |a - b| / m ^ 2 := by ring

theorem inverse_lambda_lipschitz_on_compact
    (A s t b c : ℝ) (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hsb : s ≤ b) (hsc : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |(lambda A b)⁻¹ - (lambda A c)⁻¹| ≤
      ((2 * A / t ^ 2) / (A * s ^ 2) ^ 2) * |b - c| := by
  have hb := lambda_compact_bounds A s t b hA hs ht hsb hbt
  have hc := lambda_compact_bounds A s t c hA hs ht hsc hct
  have hdiff := lambda_lipschitz_on_compact A t b c hA ht (hs.le.trans hsb) (hs.le.trans hsc) hbt hct
  calc
    _ ≤ |lambda A b - lambda A c| / (A * s ^ 2) ^ 2 :=
      reciprocal_lipschitz _ _ _ (by positivity) hb.1 hc.1
    _ ≤ ((2 * A / t ^ 2) * |b - c|) / (A * s ^ 2) ^ 2 :=
      div_le_div_of_nonneg_right hdiff (by positivity)
    _ = _ := by ring

noncomputable def gradientBound (g : E → ℝ) (Lg : ℝ) (x y : E) : ℝ :=
  ‖gradient g y‖ + Lg * ‖x - y‖

noncomputable def actualStep (g : E → ℝ) (M : ℝ) (z : E) (lam : ℝ) : E :=
  exactStep (gradient g z) (fderiv ℝ (gradient g) z) M lam

noncomputable def betaStep (g : E → ℝ) (M A : ℝ) (x y : E) (b : ℝ) : E :=
  actualStep g M (center x y b) (lambda A b)

noncomputable def betaSize (g : E → ℝ) (M A : ℝ) (x y : E) (b : ℝ) : ℝ :=
  lambda A b * ‖betaStep g M A x y b‖

theorem center_gradient_bound
    (g : E → ℝ) (Lg : ℝ) (hLg : 0 ≤ Lg)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y : E) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖gradient g (center x y b)‖ ≤ gradientBound g Lg x y := by
  have hz : ‖center x y b - y‖ ≤ ‖x - y‖ := by
    have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    nlinarith only [mul_le_mul_of_nonneg_right hb1 (norm_nonneg (x - y))]
  have ht := norm_le_norm_sub_add (gradient g (center x y b)) (gradient g y)
  have hh := (hlip (center x y b) y).trans (mul_le_mul_of_nonneg_left hz hLg)
  dsimp [gradientBound]
  linarith only [ht, hh]

theorem actualStep_uniform_bound
    (g : E → ℝ) (mu Lg M lam : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hC2 : ContDiff ℝ 2 g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y : E) (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    ‖actualStep g M (center x y b) lam‖ ≤ gradientBound g Lg x y / mu := by
  have hs := exactStep_size_bound (gradient g (center x y b)) (fderiv ℝ (gradient g) (center x y b))
    M lam mu hM hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc (center x y b))
  have hg := center_gradient_bound g Lg hLg hlip x y b hb hb1
  have hnonneg : 0 ≤ lam⁻¹ * ‖actualStep g M (center x y b) lam‖ := by positivity
  apply (le_div_iff₀ hmu).mpr
  change (mu + lam⁻¹) * ‖actualStep g M (center x y b) lam‖ ≤ _ at hs
  nlinarith only [hs, hg, hnonneg]


noncomputable def inverseLambdaModulus (A s t : ℝ) : ℝ := (2 * A / t ^ 2) / (A * s ^ 2) ^ 2

noncomputable def stepModulus (mu Lg M A s t G D : ℝ) : ℝ :=
  (Lg * D + (M * D + inverseLambdaModulus A s t) * (G / mu)) / mu

noncomputable def sizeModulus (mu Lg M A s t G D : ℝ) : ℝ :=
  (2 * A / t ^ 2) * (G / mu) + (A / t) * stepModulus mu Lg M A s t G D

theorem betaStep_lipschitz
    (g : E → ℝ) (mu Lg M A s t G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (x y : E) (hG : gradientBound g Lg x y ≤ G)
    (b c : ℝ) (hsb : s ≤ b) (hsc' : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
      stepModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by
  have hb0 : 0 ≤ b := hs.le.trans hsb
  have hc0 : 0 ≤ c := hs.le.trans hsc'
  have hb1 : b < 1 := by linarith
  have hc1 : c < 1 := by linarith
  have hblam := (coupled_weights A b hA (hs.trans_le hsb) hb1).1
  have hclam := (coupled_weights A c hA (hs.trans_le hsc') hc1).1
  have hcRadius : ‖betaStep g M A x y c‖ ≤ G / mu :=
    (actualStep_uniform_bound g mu Lg M _ hmu hLg hM hclam hC2 hsc hlip x y c hc0 hc1.le).trans
      (div_le_div_of_nonneg_right hG hmu.le)
  have hraw := parameter_stability (gradient g (center x y b)) (gradient g (center x y c))
    (fderiv ℝ (gradient g) (center x y b)) (fderiv ℝ (gradient g) (center x y c)) M
    (lambda A b) (lambda A c) mu hM hblam hclam hmu.le
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc _)
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc _)
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 _),
    CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 _)] at hraw
  have hz := center_lipschitz x y b c
  have hv : ‖gradient g (center x y b) - gradient g (center x y c)‖ ≤ Lg * ‖x - y‖ * |b - c| := by
    calc
      _ ≤ Lg * ‖center x y b - center x y c‖ := hlip _ _
      _ = _ := by rw [hz]; ring
  have hH : ‖fderiv ℝ (gradient g) (center x y b) - fderiv ℝ (gradient g) (center x y c)‖ ≤
      M * ‖x - y‖ * |b - c| := by
    calc
      _ ≤ M * ‖center x y b - center x y c‖ := hHlip _ _
      _ = _ := by rw [hz]; ring
  have hi := inverse_lambda_lipschitz_on_compact A s t b c hA hs ht hsb hsc' hbt hct
  have hG0 : 0 ≤ G := (by dsimp [gradientBound]; positivity : 0 ≤ gradientBound g Lg x y).trans hG
  have hbound : mu * ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
      (Lg * ‖x - y‖ + (M * ‖x - y‖ + inverseLambdaModulus A s t) * (G / mu)) * |b - c| := by
    have hnonneg : 0 ≤ (lambda A b)⁻¹ * ‖betaStep g M A x y b - betaStep g M A x y c‖ := by positivity
    have h1 : mu * ‖betaStep g M A x y b - betaStep g M A x y c‖ ≤
        (mu + (lambda A b)⁻¹) * ‖betaStep g M A x y b - betaStep g M A x y c‖ := by
      nlinarith only [hnonneg]
    refine h1.trans (hraw.trans ?_)
    have hcoef0 : 0 ≤ (M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c| := by
      dsimp [inverseLambdaModulus]
      positivity
    have hsum : ‖fderiv ℝ (gradient g) (center x y b) - fderiv ℝ (gradient g) (center x y c)‖ +
        |(lambda A b)⁻¹ - (lambda A c)⁻¹| ≤
        (M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c| := by
      calc
        _ ≤ M * ‖x - y‖ * |b - c| + ((2 * A / t ^ 2) / (A * s ^ 2) ^ 2) * |b - c| := add_le_add hH hi
        _ = _ := by dsimp [inverseLambdaModulus]; ring
    calc
      _ ≤ (Lg * ‖x - y‖ * |b - c|) +
          ((M * ‖x - y‖ + inverseLambdaModulus A s t) * |b - c|) * (G / mu) := by
        exact add_le_add hv (mul_le_mul hsum hcRadius (norm_nonneg _) hcoef0)
      _ = _ := by ring
  calc
    _ ≤ ((Lg * ‖x - y‖ + (M * ‖x - y‖ + inverseLambdaModulus A s t) * (G / mu)) * |b - c|) / mu :=
      (le_div_iff₀ hmu).mpr (by nlinarith only [hbound])
    _ = stepModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by dsimp [stepModulus]; ring

theorem betaSize_lipschitz
    (g : E → ℝ) (mu Lg M A s t G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hA : 0 < A) (hs : 0 < s) (ht : 0 < t)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (x y : E) (hG : gradientBound g Lg x y ≤ G)
    (b c : ℝ) (hsb : s ≤ b) (hsc' : s ≤ c) (hbt : b ≤ 1 - t) (hct : c ≤ 1 - t) :
    |betaSize g M A x y b - betaSize g M A x y c| ≤
      sizeModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by
  have hb0 : 0 ≤ b := hs.le.trans hsb
  have hb1 : b < 1 := by linarith
  have hblam := (coupled_weights A b hA (hs.trans_le hsb) hb1).1
  have hclam := (coupled_weights A c hA (hs.trans_le hsc') (by linarith)).1
  have hG0 : 0 ≤ G := (by dsimp [gradientBound]; positivity : 0 ≤ gradientBound g Lg x y).trans hG
  have hRadius : ‖betaStep g M A x y b‖ ≤ G / mu :=
    (actualStep_uniform_bound g mu Lg M _ hmu hLg hM hblam hC2 hsc hlip x y b hb0 hb1.le).trans
      (div_le_div_of_nonneg_right hG hmu.le)
  have hlamDiff := lambda_lipschitz_on_compact A t b c hA ht hb0 (hs.le.trans hsc') hbt hct
  have hlamUpper := (lambda_compact_bounds A s t c hA hs ht hsc' hct).2
  have hStepDiff := betaStep_lipschitz g mu Lg M A s t G hmu hLg hM hA hs ht
    hC2 hsc hlip hHlip x y hG b c hsb hsc' hbt hct
  have hNormDiff := (abs_norm_sub_norm_le (betaStep g M A x y b) (betaStep g M A x y c)).trans hStepDiff
  unfold betaSize
  calc
    _ = |(lambda A b - lambda A c) * ‖betaStep g M A x y b‖ +
        lambda A c * (‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖)| := by congr 1; ring
    _ ≤ |(lambda A b - lambda A c) * ‖betaStep g M A x y b‖| +
        |lambda A c * (‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖)| := abs_add_le _ _
    _ = |lambda A b - lambda A c| * ‖betaStep g M A x y b‖ +
        lambda A c * |‖betaStep g M A x y b‖ - ‖betaStep g M A x y c‖| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_pos hclam]
    _ ≤ ((2 * A / t ^ 2) * |b - c|) * (G / mu) +
        (A / t) * (stepModulus mu Lg M A s t G ‖x - y‖ * |b - c|) := by gcongr
    _ = sizeModulus mu Lg M A s t G ‖x - y‖ * |b - c| := by dsimp [sizeModulus]; ring

end OriginalBetaCurveBounds


namespace OriginalBetaATSUniform
open _root_.OriginalBetaATSUniform

noncomputable def uniformStepFloor (mu Lg M lo rho : ℝ) : ℝ :=
  CertifiedATS.stepFloor rho (Lg + mu / 4 + lo⁻¹) M

noncomputable def uniformTolerance (mu Lg M lo up sigma rho : ℝ) : ℝ :=
  min (rho / 8) (min (mu / 4)
    (min (sigma * uniformStepFloor mu Lg M lo rho / (2 * up)) (sigma / (2 * up))))

theorem uniformStepFloor_positive
    (mu Lg M lo rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hrho : 0 < rho) :
    0 < uniformStepFloor mu Lg M lo rho := by
  exact CertifiedATS.stepFloor_positive rho _ M hrho (by positivity) hM

theorem uniformTolerance_positive
    (mu Lg M lo up sigma rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hup : 0 < up) (hsigma : 0 < sigma) (hrho : 0 < rho) :
    0 < uniformTolerance mu Lg M lo up sigma rho := by
  have hell := uniformStepFloor_positive mu Lg M lo rho hmu hLg hM hlo hrho
  unfold uniformTolerance
  positivity

theorem uniformStepFloor_le
    (mu Lg M lo lam rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hrho : 0 < rho) :
    uniformStepFloor mu Lg M lo rho ≤ CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hinv : lam⁻¹ ≤ lo⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hlo hlolam
  have hden : 0 < 8 * (Lg + mu / 4 + lam⁻¹ + M / 2) := by positivity
  have hdenle : 8 * (Lg + mu / 4 + lam⁻¹ + M / 2) ≤ 8 * (Lg + mu / 4 + lo⁻¹ + M / 2) := by linarith
  change min 1 (rho / (8 * (Lg + mu / 4 + lo⁻¹ + M / 2))) ≤
    min 1 (rho / (8 * (Lg + mu / 4 + lam⁻¹ + M / 2)))
  exact min_le_min le_rfl (div_le_div_of_nonneg_left hrho.le hden hdenle)

theorem uniformTolerance_le_refinementTolerance
    (mu Lg M lo up lam sigma rho : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hlamup : lam ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    uniformTolerance mu Lg M lo up sigma rho ≤
      CertifiedATS.refinementTolerance mu Lg M lam sigma rho := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hup : 0 < up := hlam.trans_le hlamup
  have hfloor := uniformStepFloor_le mu Lg M lo lam rho hmu hLg hM hlo hlolam hrho
  have hell : 0 < CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M :=
    CertifiedATS.stepFloor_positive rho _ M hrho (by positivity) hM
  have hterm3 : sigma * uniformStepFloor mu Lg M lo rho / (2 * up) ≤
      sigma * CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M / (2 * lam) := by
    calc
      _ ≤ sigma * CertifiedATS.stepFloor rho (Lg + mu / 4 + lam⁻¹) M / (2 * up) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor hsigma.le) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hterm4 : sigma / (2 * up) ≤ sigma / (2 * lam) :=
    div_le_div_of_nonneg_left hsigma.le (by positivity) (by linarith)
  have h1 : uniformTolerance mu Lg M lo up sigma rho ≤ rho / 8 := min_le_left _ _
  have h2 : uniformTolerance mu Lg M lo up sigma rho ≤ mu / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h3 : uniformTolerance mu Lg M lo up sigma rho ≤ sigma * uniformStepFloor mu Lg M lo rho / (2 * up) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : uniformTolerance mu Lg M lo up sigma rho ≤ sigma / (2 * up) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact le_min h1 (le_min h2 (le_min (h3.trans hterm3) (h4.trans hterm4)))

theorem uniform_geometric_refinement
    (mu Lg M lo up lam sigma rho error0 : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hM : 0 ≤ M) (hlo : 0 < lo) (hlolam : lo ≤ lam) (hlamup : lam ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    error0 / (2 : ℝ) ^ CertifiedATS.halvingCount error0
      (uniformTolerance mu Lg M lo up sigma rho) ≤
        CertifiedATS.refinementTolerance mu Lg M lam sigma rho := by
  have hup : 0 < up := (hlo.trans_le hlolam).trans_le hlamup
  have ht := uniformTolerance_positive mu Lg M lo up sigma rho hmu hLg hM hlo hup hsigma hrho
  exact (CertifiedATS.halving_precision error0 _ ht).trans
    (uniformTolerance_le_refinementTolerance mu Lg M lo up lam sigma rho
      hmu hLg hM hlo hlolam hlamup hsigma hrho)

end OriginalBetaATSUniform


namespace OriginalBetaATSTrial
open _root_.OriginalBetaATSTrial

open OriginalTaylorProxStability
open OriginalBetaATSUniform

abbrev GetterProgram := _root_.OriginalBetaATSTrial.GetterProgram

noncomputable def execute {Q A R : Type*} (getter : Q → A) : GetterProgram Q A R → R × ℕ
  | .pure r => (r, 0)
  | .ask q next => let r := execute getter (next (getter q)); (r.1, r.2 + 1)

 theorem execute_eq_original {Q A R : Type*} (getter : Q → A) (p : GetterProgram Q A R) :
    execute getter p = _root_.OriginalBetaATSTrial.execute getter p := by
  induction p with
  | pure r => rfl
  | ask q next ih => simp only [execute,_root_.OriginalBetaATSTrial.execute,ih]

structure Answer (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  grad : E
  hess : E →L[ℝ] E

inductive TrialResult (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | stop (point : E)
  | step (displacement : E) (outputAnswer : Answer E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def trialProgram (M lam delta rho deltaY : ℝ) (z : E) :
    GetterProgram (E × ℝ) (Answer E) (TrialResult E) := by
  classical
  exact .ask (z, delta) (fun a =>
    if ‖a.grad‖ + delta ≤ rho then .pure (.stop z) else
      let d := exactStep a.grad a.hess M lam
      .ask (z + d, deltaY) (fun aY =>
        if ‖aY.grad‖ + deltaY ≤ rho then .pure (.stop (z + d)) else .pure (.step d aY)))

noncomputable def trial (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) : TrialResult E :=
  (execute getter (trialProgram M lam delta rho deltaY z)).1

def TrialSpec (g : E → ℝ) (M lam sigma rho deltaY : ℝ) (z : E) : TrialResult E → Prop
  | .stop w => ‖gradient g w‖ ≤ rho
  | .step d aY =>
      ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (z + d)‖ ≤ deltaY ∧ rho / 2 < ‖gradient g (z + d)‖

theorem exactStep_unique
    (v : E) (H : E →L[ℝ] E) (M lam mu : ℝ)
    (hM : 0 ≤ M) (hlam : 0 < lam) (hmu : 0 ≤ mu)
    (hcoer : ∀ d : E, mu * ‖d‖ ^ 2 ≤ inner ℝ (H d) d)
    (d : E) (hmin : ∀ w : E, CertifiedATS.model v H M lam d ≤ CertifiedATS.model v H M lam w) :
    d = exactStep v H M lam := by
  have hm : 0 < mu + lam⁻¹ := by positivity
  have hd : Differentiable ℝ (CertifiedATS.model v H M lam) :=
    fun t => (CertifiedATS.model_hasGradientAt v H M lam t).differentiableAt
  have hs := PacketCore.strongConvex_gradient_distance _ (mu + lam⁻¹) hm
    (model_strongConvex_with_prox v H M lam mu hM hlam hcoer) hd _
    (exactStep_minimizes v H M lam mu hM hlam hmu hcoer) d
  rw [PacketCore.gradient_eq_zero_at_global_min _ _ hmin, norm_zero] at hs
  have hn : ‖d - exactStep v H M lam‖ ≤ 0 := by
    apply (mul_le_mul_iff_right₀ hm).mp
    simpa only [mul_zero] using hs
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

theorem selected_approximate_step_accepts
    (g : E → ℝ) (mu Lg M lam sigma rho delta : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (z v : E) (H : E →L[ℝ] E)
    (hgerr : ‖v - gradient g z‖ ≤ delta) (hHerr : ‖H - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hsmall : delta ≤ CertifiedATS.refinementTolerance mu Lg M lam sigma rho)
    (haway : rho / 2 ≤ ‖gradient g z‖) :
    ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M (exactStep v H M lam) +
      exactStep v H M lam‖ ≤ sigma * ‖exactStep v H M lam‖ := by
  obtain ⟨d, hmin, hfloor, hcert, hATS⟩ := CertifiedATS.model_acceptance_at_accuracy g hC2
    mu Lg M lam sigma rho hmu hLg hM hlam hsigma hrho hsc hlip z v H delta hgerr hHerr hsmall haway
  have hdmu : delta ≤ mu / 4 := hsmall.trans (CertifiedATS.refinementTolerance_bounds mu Lg M lam sigma rho).2.1
  have hcoer : ∀ w : E, (3 * mu / 4) * ‖w‖ ^ 2 ≤ inner ℝ (H w) w := by
    intro w
    simpa only [CertifiedATS.sympart_same_quadratic] using
      CertifiedATS.approximate_hessian_coercive g hC2 mu hsc z H delta hHerr hdmu w
  have heq := exactStep_unique v H M lam (3 * mu / 4) hM hlam (by positivity) hcoer d hmin
  rwa [heq] at hATS

theorem trial_getter_calls
    (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) :
    (execute getter (trialProgram M lam delta rho deltaY z)).2 ≤ 2 := by
  classical
  by_cases hc : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simp [trialProgram, execute, hc]
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    by_cases ho : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · dsimp only [d] at ho
      simp [trialProgram, execute, hc, d, ho]
    · dsimp only [d] at ho
      simp [trialProgram, execute, hc, d, ho]

theorem trial_spec_at_accuracy
    (g : E → ℝ) (mu Lg M lam sigma rho delta deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hdelta : 0 < delta)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) (hsmall : delta ≤ CertifiedATS.refinementTolerance mu Lg M lam sigma rho) :
    TrialSpec g M lam sigma rho deltaY z (trial getter M lam delta rho deltaY z) := by
  classical
  have herr := hgetter z delta hdelta
  have hdeltaSmall := hsmall.trans (CertifiedATS.refinementTolerance_bounds mu Lg M lam sigma rho).1
  by_cases hcenter : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simpa only [trial, trialProgram, execute, if_pos hcenter, TrialSpec] using
      CertifiedATS.center_stop_certifies _ _ delta rho herr.1 hcenter
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    have herrY := (hgetter (z + d) deltaY hdeltaY).1
    by_cases hout : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · dsimp only [d] at hout
      simpa only [trial, trialProgram, execute, d, if_neg hcenter, if_pos hout, TrialSpec] using
        CertifiedATS.center_stop_certifies _ _ deltaY rho herrY hout
    · dsimp only [d] at hout
      have hcenterAway : rho / 2 ≤ ‖gradient g z‖ := by
        have hn := norm_le_norm_sub_add (getter (z, delta)).grad (gradient g z)
        have hnot : rho < ‖(getter (z, delta)).grad‖ + delta := lt_of_not_ge hcenter
        linarith only [hn, herr.1, hdeltaSmall, hnot, hrho]
      have hATS := selected_approximate_step_accepts g mu Lg M lam sigma rho delta
        hmu hLg hM hlam hsigma hrho hC2 hsc hlip z _ _ herr.1 herr.2 hsmall hcenterAway
      have hawayY : rho / 2 < ‖gradient g (z + d)‖ := by
        have hn := norm_le_norm_sub_add (getter (z + d, deltaY)).grad (gradient g (z + d))
        have hnot : rho < ‖(getter (z + d, deltaY)).grad‖ + deltaY := lt_of_not_ge hout
        linarith only [hn, herrY, hdeltaYsmall, hnot, hrho]
      have hs : TrialSpec g M lam sigma rho deltaY z (.step d (getter (z + d, deltaY))) :=
        ⟨hATS, herrY, hawayY⟩
      simpa only [trial, trialProgram, execute, d, if_neg hcenter, if_neg hout] using hs

theorem trial_uniform_spec
    (g : E → ℝ) (mu Lg M lo up lam sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M) (hlo : 0 < lo)
    (hlolam : lo ≤ lam) (hlamup : lam ≤ up) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ Lg * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) :
    TrialSpec g M lam sigma rho deltaY z
      (trial getter M lam (uniformTolerance mu Lg M lo up sigma rho) rho deltaY z) := by
  have hlam : 0 < lam := hlo.trans_le hlolam
  have hup : 0 < up := hlam.trans_le hlamup
  exact trial_spec_at_accuracy g mu Lg M lam sigma rho _ deltaY
    hmu hLg hM hlam hsigma hrho
    (uniformTolerance_positive mu Lg M lo up sigma rho hmu hLg hM hlo hup hsigma hrho)
    hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter z
    (uniformTolerance_le_refinementTolerance mu Lg M lo up lam sigma rho hmu hLg hM hlo hlolam hlamup hsigma hrho)

end OriginalBetaATSTrial


namespace RobustAHPE
open _root_.RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_differentiable (F : E → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (gradient F) := by
  have hder : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have heq : gradient F = fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F y) := rfl
  rw [heq]
  exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder).differentiable (by norm_num)


theorem scalarization_hasGradientAt (T : E → E) (hdiff : Differentiable ℝ T) (w x : E) :
    HasGradientAt (fun u : E => inner ℝ w (T u)) ((fderiv ℝ T x).adjoint w) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (InnerProductSpace.toDual ℝ E w).hasFDerivAt.comp x (hdiff x).hasFDerivAt
  convert! hh using 1
  ext d
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem scalarization_gradient_lipschitz (T : E → E) (hdiff : Differentiable ℝ T)
    (M : ℝ) (hT : ∀ x y : E, ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * ‖x - y‖)
    (w x y : E) :
    ‖gradient (fun u : E => inner ℝ w (T u)) x - gradient (fun u : E => inner ℝ w (T u)) y‖ ≤
      (M * ‖w‖) * ‖x - y‖ := by
  rw [(scalarization_hasGradientAt T hdiff w x).gradient,
    (scalarization_hasGradientAt T hdiff w y).gradient]
  have he : (fderiv ℝ T x).adjoint w - (fderiv ℝ T y).adjoint w =
      (fderiv ℝ T x - fderiv ℝ T y).adjoint w := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [he]
  have hn := ContinuousLinearMap.le_opNorm (fderiv ℝ T x - fderiv ℝ T y).adjoint w
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  have hm := mul_le_mul_of_nonneg_right (hT x y) (norm_nonneg w)
  nlinarith only [hn, hm]

theorem vector_taylor_remainder (T : E → E) (hdiff : Differentiable ℝ T)
    (M : ℝ) (hM : 0 < M)
    (hT : ∀ x y : E, ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖T (z + d) - T z - fderiv ℝ T z d‖ ≤ M / 2 * ‖d‖ ^ 2 := by
  let R := T (z + d) - T z - fderiv ℝ T z d
  by_cases hz : R = 0
  · change ‖R‖ ≤ M / 2 * ‖d‖ ^ 2
    rw [hz, norm_zero]
    positivity
  · have hR : 0 < ‖R‖ := norm_pos_iff.mpr hz
    let p : E → ℝ := fun u => inner ℝ R (T u)
    have hp : Differentiable ℝ p := fun u => (scalarization_hasGradientAt T hdiff R u).differentiableAt
    have hupper := OriginalAudit.smooth_descent_upper p (M * ‖R‖) (by positivity) hp
      (scalarization_gradient_lipschitz T hdiff M hT R) z d
    have hgrad : gradient p z = (fderiv ℝ T z).adjoint R :=
      (scalarization_hasGradientAt T hdiff R z).gradient
    rw [hgrad, ContinuousLinearMap.adjoint_inner_left] at hupper
    have hi : inner ℝ R (T (z + d)) - inner ℝ R (T z) - inner ℝ R (fderiv ℝ T z d) = ‖R‖ ^ 2 := by
      rw [← inner_sub_right, ← inner_sub_right]
      exact real_inner_self_eq_norm_sq R
    dsimp only [p] at hupper
    have hsq : ‖R‖ * ‖R‖ ≤ ‖R‖ * (M / 2 * ‖d‖ ^ 2) := by
      nlinarith only [hupper, hi]
    change ‖R‖ ≤ M / 2 * ‖d‖ ^ 2
    exact (mul_le_mul_iff_right₀ hR).mp (by nlinarith only [hsq])

theorem gradient_taylor_remainder (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d‖ ≤
      M / 2 * ‖d‖ ^ 2 :=
  vector_taylor_remainder (gradient g) (gradient_differentiable g hC2) M hM hH z d

end RobustAHPE

namespace RobustAHPE
open _root_.RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def trueModelVector (g : E → ℝ) (z : E) (Mbar : ℝ) (d : E) : E :=
  gradient g z + fderiv ℝ (gradient g) z d + (Mbar / 2 * ‖d‖) • d

theorem gradient_minus_modelVector_bound (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M Mbar : ℝ) (hM : 0 < M) (hMbar : 0 ≤ Mbar)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) : ‖gradient g (z + d) - trueModelVector g z Mbar d‖ ≤
      (M + Mbar) / 2 * ‖d‖ ^ 2 := by
  have ht := gradient_taylor_remainder g hC2 M hM hH z d
  have he : gradient g (z + d) - trueModelVector g z Mbar d =
      (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) - (Mbar / 2 * ‖d‖) • d := by
    dsimp only [trueModelVector]
    abel
  rw [he]
  have hn : ‖(Mbar / 2 * ‖d‖) • d‖ = (Mbar / 2) * ‖d‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have htri := norm_sub_le
    (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) ((Mbar / 2 * ‖d‖) • d)
  rw [hn] at htri
  nlinarith only [ht, htri]

theorem true_gradient_residual_from_ATS (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖lam • gradient g (z + d) + d‖ ≤ (sigmaHat + sigmaU) * ‖d‖ := by
  have hm := gradient_minus_modelVector_bound g hC2 M M hM hM.le hH z d
  have he : lam • gradient g (z + d) + d =
      (lam • trueModelVector g z M d + d) + lam • (gradient g (z + d) - trueModelVector g z M d) := by
    module
  rw [he]
  have htri := norm_add_le (lam • trueModelVector g z M d + d)
    (lam • (gradient g (z + d) - trueModelVector g z M d))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at htri
  have hmul := mul_le_mul_of_nonneg_left hm hlam.le
  have hw := (le_div_iff₀ hM).mp hwindow
  have hwmul := mul_le_mul_of_nonneg_right hw (norm_nonneg d)
  nlinarith only [htri, hATS, hmul, hwmul]

theorem new_gradient_bound_from_ATS (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * ‖d‖ / lam := by
  have hr := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindow
  have ht := norm_sub_le (lam • gradient g (z + d) + d) d
  have he : (lam • gradient g (z + d) + d) - d = lam • gradient g (z + d) := by abel
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
  apply (le_div_iff₀ hlam).mpr
  nlinarith only [ht, hr]

theorem large_lambda_gradient_endpoint (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (M lam sigmaHat sigmaU : ℝ) (hM : 0 < M) (hlam : 0 < lam)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaU : 0 ≤ sigmaU)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaU / M) :
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * sigmaU / (M * lam ^ 2) := by
  have hg := new_gradient_bound_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindow
  have hw : ‖d‖ ≤ sigmaU / (M * lam) := by
    apply (le_div_iff₀ (mul_pos hM hlam)).mpr
    have hh := (le_div_iff₀ hM).mp hwindow
    nlinarith only [hh]
  calc
    ‖gradient g (z + d)‖ ≤ (1 + sigmaHat + sigmaU) * ‖d‖ / lam := hg
    _ ≤ (1 + sigmaHat + sigmaU) * (sigmaU / (M * lam)) / lam := by gcongr
    _ = (1 + sigmaHat + sigmaU) * sigmaU / (M * lam ^ 2) := by field_simp <;> ring

end RobustAHPE


namespace OriginalBetaSearchEndpoints
open _root_.OriginalBetaSearchEndpoints

open OriginalCoupledBetaAlgebra
open OriginalTaylorProxStability
open OriginalBetaCurveBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem gradient_upper_from_certificate
    (g : E → ℝ) (Lg : ℝ) (x y v : E) (delta : ℝ)
    (herr : ‖v - gradient g y‖ ≤ delta) :
    gradientBound g Lg x y ≤ ‖v‖ + delta + Lg * ‖x - y‖ := by
  have hn := norm_le_norm_sub_add (gradient g y) v
  rw [norm_sub_rev (gradient g y) v] at hn
  dsimp [gradientBound]
  linarith only [hn, herr]

theorem actual_scaled_residual
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (M lam : ℝ) (hlam : 0 < lam) (z d : E) :
    lam • proxGradient (gradient g z) (fderiv ℝ (gradient g) z) M lam d =
      lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d := by
  dsimp [proxGradient, CertifiedATS.trueVector]
  rw [CertifiedATS.sympart_eq_of_selfadjoint _ (CertifiedATS.gradient_derivative_selfadjoint g hC2 z)]
  simp only [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt hlam), one_smul]

theorem actual_approximate_norm_bracket
    (g : E → ℝ) (mu M lam sigma : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * (lam * ‖d‖) ≤ lam * ‖actualStep g M z lam‖ ∧
      lam * ‖actualStep g M z lam‖ ≤ (1 + sigma) * (lam * ‖d‖) := by
  have hr : ‖lam • proxGradient (gradient g z) (fderiv ℝ (gradient g) z) M lam d‖ ≤ sigma * ‖d‖ := by
    rw [actual_scaled_residual g hC2 M lam hlam z d]
    exact hATS
  have hn := approximate_norm_bracket (gradient g z) (fderiv ℝ (gradient g) z) M lam mu sigma
    hM hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z) d hr
  change (1 - sigma) * ‖d‖ ≤ ‖actualStep g M z lam‖ ∧
    ‖actualStep g M z lam‖ ≤ (1 + sigma) * ‖d‖ at hn
  constructor
  · have hh := mul_le_mul_of_nonneg_left hn.1 hlam.le
    nlinarith only [hh]
  · have hh := mul_le_mul_of_nonneg_left hn.2 hlam.le
    nlinarith only [hh]

theorem exact_step_lambda_bound
    (g : E → ℝ) (mu M lam G : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (hG : ‖gradient g z‖ ≤ G) : ‖actualStep g M z lam‖ ≤ lam * G := by
  have hh := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) M lam mu hM hlam hmu.le
    (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hm := mul_le_mul_of_nonneg_left (hh.trans hG) hlam.le
  have hinv : lam * (mu + lam⁻¹) = lam * mu + 1 := by
    rw [mul_add, mul_inv_cancel₀ (ne_of_gt hlam)]
  change lam * ((mu + lam⁻¹) * ‖actualStep g M z lam‖) ≤ lam * G at hm
  rw [← mul_assoc, hinv] at hm
  have hn : 0 ≤ lam * mu * ‖actualStep g M z lam‖ := by positivity
  nlinarith only [hm, hn]

theorem approximate_small_lambda_bound
    (g : E → ℝ) (mu M lam sigma G : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖) :
    (1 - sigma) * (lam * ‖d‖) ≤ lam ^ 2 * G := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM hlam hC2 hsc z d hATS).1
  have hs := exact_step_lambda_bound g mu M lam G hmu hM hlam hC2 hsc z hG
  have hm := mul_le_mul_of_nonneg_left hs hlam.le
  nlinarith only [hb, hm]

noncomputable def lambdaLow (M sigmaLow sigma G : ℝ) : ℝ :=
  min 1 (sigmaLow * (1 - sigma) / (2 * M * (1 + G)))

noncomputable def lambdaHigh (M rho sigma sigmaUp : ℝ) : ℝ :=
  1 + 2 * ((1 + sigma + sigmaUp) * sigmaUp) / (M * rho)

noncomputable def betaLow (A ell : ℝ) : ℝ := min (1 / 4) (ell / (4 * (1 + A)))
noncomputable def highMargin (A H : ℝ) : ℝ := min (1 / 4) (A / (8 * (1 + H)))
noncomputable def betaHigh (A H : ℝ) : ℝ := 1 - highMargin A H

theorem lambdaLow_positive
    (M sigmaLow sigma G : ℝ) (hM : 0 < M) (hLow : 0 < sigmaLow) (hsigma : sigma < 1) (hG : 0 ≤ G) :
    0 < lambdaLow M sigmaLow sigma G ∧ lambdaLow M sigmaLow sigma G ≤ 1 := by
  exact ⟨lt_min zero_lt_one (by positivity), min_le_left _ _⟩

theorem betaLow_properties
    (A ell : ℝ) (hA : 0 < A) (hell : 0 < ell) :
    0 < betaLow A ell ∧ betaLow A ell ≤ 1 / 4 ∧ lambda A (betaLow A ell) ≤ ell := by
  let b := betaLow A ell
  have hb : 0 < b := lt_min (by norm_num) (by positivity)
  have hb4 : b ≤ 1 / 4 := min_le_left _ _
  have hbell : b ≤ ell / (4 * (1 + A)) := min_le_right _ _
  have hden : 0 < 1 - b := by linarith
  have hinv : 1 / (1 - b) ≤ 2 := by apply (div_le_iff₀ hden).mpr; linarith
  have hb2 : b ^ 2 ≤ b := by nlinarith only [hb, hb4]
  refine ⟨hb, hb4, ?_⟩
  change A * b ^ 2 / (1 - b) ≤ ell
  calc
    _ = (A * b ^ 2) * (1 / (1 - b)) := by ring
    _ ≤ (A * b) * 2 := mul_le_mul (mul_le_mul_of_nonneg_left hb2 hA.le) hinv (by positivity) (by positivity)
    _ ≤ (A * (ell / (4 * (1 + A)))) * 2 := by gcongr
    _ ≤ ell := by
      have heq : (A * (ell / (4 * (1 + A)))) * 2 = (2 * A * ell) / (4 * (1 + A)) := by ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (1 + A))).mpr
      nlinarith only [hA, hell]

theorem betaHigh_properties
    (A H : ℝ) (hA : 0 < A) (hH : 0 ≤ H) :
    0 < highMargin A H ∧ highMargin A H ≤ 1 / 4 ∧
    3 / 4 ≤ betaHigh A H ∧ betaHigh A H < 1 ∧ H ≤ lambda A (betaHigh A H) := by
  let t := highMargin A H
  let b := betaHigh A H
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht4 : t ≤ 1 / 4 := min_le_left _ _
  have htA : t ≤ A / (8 * (1 + H)) := min_le_right _ _
  have hb : 3 / 4 ≤ b := by dsimp [b, betaHigh]; linarith only [ht4]
  have hb1 : b < 1 := by dsimp [b, betaHigh]; linarith only [ht]
  refine ⟨ht, ht4, hb, hb1, ?_⟩
  have hb2 : (1 / 4 : ℝ) ≤ b ^ 2 := by nlinarith only [hb]
  have hAprod := (le_div_iff₀ (by positivity : 0 < 8 * (1 + H))).mp htA
  have hlow : H ≤ (A / 4) / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith only [hAprod, ht, hH]
  have hquad := mul_le_mul_of_nonneg_left hb2 hA.le
  have heq : 1 - b = t := by dsimp [b, betaHigh, t]; ring
  change H ≤ A * b ^ 2 / (1 - b)
  rw [heq]
  exact hlow.trans (div_le_div_of_nonneg_right (by nlinarith only [hquad]) ht.le)


theorem low_endpoint_is_low
    (g : E → ℝ) (mu Lg M A sigmaLow sigma G : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 < M) (hA : 0 < A)
    (hLow : 0 < sigmaLow) (hsigma : sigma < 1) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (x y d : E) (hG : gradientBound g Lg x y ≤ G)
    (hATS : let b := betaLow A (lambdaLow M sigmaLow sigma G)
      ‖lambda A b • CertifiedATS.trueVector (gradient g (center x y b))
        (fderiv ℝ (gradient g) (center x y b)) M d + d‖ ≤ sigma * ‖d‖) :
    lambda A (betaLow A (lambdaLow M sigmaLow sigma G)) * ‖d‖ < sigmaLow / M := by
  let ell := lambdaLow M sigmaLow sigma G
  let b := betaLow A ell
  let lam := lambda A b
  have hell := lambdaLow_positive M sigmaLow sigma G hM hLow hsigma hG0
  have hb := betaLow_properties A ell hA hell.1
  have hb1 : b < 1 := by linarith only [hb.2.1]
  have hlam : 0 < lam := (coupled_weights A b hA hb.1 hb1).1
  have hlamEll : lam ≤ ell := hb.2.2
  have hlamOne : lam ≤ 1 := hlamEll.trans hell.2
  have hprod := mul_nonneg hlam.le (sub_nonneg.mpr hlamOne)
  have hsq : lam ^ 2 ≤ ell := by nlinarith only [hprod, hlamEll]
  have hgrad : ‖gradient g (center x y b)‖ ≤ G :=
    (center_gradient_bound g Lg hLg hlip x y b hb.1.le hb1.le).trans hG
  have hsmall := approximate_small_lambda_bound g mu M lam sigma G hmu hM.le hlam hC2 hsc
    (center x y b) d hgrad hATS
  have hratio : ell ≤ sigmaLow * (1 - sigma) / (2 * M * (1 + G)) := min_le_right _ _
  have hr := (le_div_iff₀ (by positivity : 0 < 2 * M * (1 + G))).mp hratio
  have hellG : ell * G ≤ sigmaLow * (1 - sigma) / (2 * M) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * M)).mpr
    have hn : 0 ≤ 2 * M * ell := mul_nonneg (by positivity) hell.1.le
    nlinarith only [hr, hn]
  have hscale : (1 - sigma) * (lam * ‖d‖) ≤ (1 - sigma) * (sigmaLow / (2 * M)) := by
    calc
      _ ≤ lam ^ 2 * G := hsmall
      _ ≤ ell * G := mul_le_mul_of_nonneg_right hsq hG0
      _ ≤ sigmaLow * (1 - sigma) / (2 * M) := hellG
      _ = _ := by ring
  have hs : lam * ‖d‖ ≤ sigmaLow / (2 * M) :=
    (mul_le_mul_iff_right₀ (show 0 < 1 - sigma by linarith)).mp hscale
  have hhalf : sigmaLow / (2 * M) < sigmaLow / M := by
    have hp : 0 < sigmaLow / M := div_pos hLow hM
    have heq : sigmaLow / (2 * M) = (sigmaLow / M) / 2 := by ring
    rw [heq]
    linarith only [hp]
  exact hs.trans_lt hhalf

theorem large_lambda_upper_is_small
    (g : E → ℝ) (M rho sigma sigmaUp lam : ℝ)
    (hM : 0 < M) (hrho : 0 < rho) (hsigma : 0 ≤ sigma) (hUp : 0 ≤ sigmaUp)
    (hlam : 0 < lam) (hlarge : lambdaHigh M rho sigma sigmaUp ≤ lam)
    (hC2 : ContDiff ℝ 2 g)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ M * ‖z - w‖)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : lam * ‖d‖ ≤ sigmaUp / M) : ‖gradient g (z + d)‖ ≤ rho / 2 := by
  let C := (1 + sigma + sigmaUp) * sigmaUp
  let q := 2 * C / (M * rho)
  have hq : 0 ≤ q := by dsimp [q, C]; positivity
  have hlarge' : 1 + q ≤ lam := hlarge
  have hsquare : q ≤ lam ^ 2 := by nlinarith only [hlarge', hq, sq_nonneg q]
  have hmul := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ M * rho)
  have heq : (M * rho) * q = 2 * C := by dsimp [q]; field_simp
  rw [heq] at hmul
  have hfinal : C / (M * lam ^ 2) ≤ rho / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < M * lam ^ 2)).mpr
    nlinarith only [hmul]
  have hb := RobustAHPE.large_lambda_gradient_endpoint g hC2 M lam sigma sigmaUp
    hM hlam hsigma hUp hHlip z d hATS hwindow
  exact hb.trans hfinal

theorem low_failure_exact_threshold
    (g : E → ℝ) (mu M lam sigma sigmaLow : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : 0 ≤ sigma)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hlow : lam * ‖d‖ < sigmaLow / M) :
    lam * ‖actualStep g M z lam‖ ≤ sigmaLow * (1 + sigma) / M := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).2
  have hm := mul_le_mul_of_nonneg_left hlow.le (by positivity : 0 ≤ 1 + sigma)
  have heq : (1 + sigma) * (sigmaLow / M) = sigmaLow * (1 + sigma) / M := by ring
  exact hb.trans (by simpa only [heq] using hm)

theorem high_failure_exact_threshold
    (g : E → ℝ) (mu M lam sigma sigmaUp : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : sigma < 1)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hhigh : sigmaUp / M < lam * ‖d‖) :
    sigmaUp * (1 - sigma) / M ≤ lam * ‖actualStep g M z lam‖ := by
  have hb := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).1
  have hm := mul_le_mul_of_nonneg_left hhigh.le (show 0 ≤ 1 - sigma by linarith)
  have heq : (1 - sigma) * (sigmaUp / M) = sigmaUp * (1 - sigma) / M := by ring
  have hm' : sigmaUp * (1 - sigma) / M ≤ (1 - sigma) * (lam * ‖d‖) := by
    simpa only [heq] using hm
  exact hm'.trans hb

end OriginalBetaSearchEndpoints


namespace FangqingHysteresis
open _root_.FangqingHysteresis

inductive Decision (R : Type*) where
  | accept (value : R)
  | low
  | high

inductive Outcome (R : Type*) where
  | found (value : R)
  | bracket (left right : ℝ)

inductive Program (Reply Result : Type*) where
  | pure (value : Result)
  | ask (point : ℝ) (next : Reply → Program Reply Result)

noncomputable def execute {Reply Result : Type*} (oracle : ℝ → Reply) :
    Program Reply Result → Result × ℕ
  | .pure value => (value, 0)
  | .ask x next => let r := execute oracle (next (oracle x)); (r.1, r.2 + 1)

noncomputable def bisect {R : Type*} : ℕ → ℝ → ℝ → Program (Decision R) (Outcome R)
  | 0, l, r => .pure (.bracket l r)
  | n + 1, l, r =>
      let m := (l + r) / 2
      .ask m (fun answer => match answer with
        | .accept value => .pure (.found value)
        | .low => bisect n m r
        | .high => bisect n l m)

def Bracket (F : ℝ → ℝ) (a b L U l r : ℝ) : Prop :=
  L ≤ l ∧ l ≤ r ∧ r ≤ U ∧ F l ≤ a ∧ b ≤ F r

def Spec {R : Type*} (F : ℝ → ℝ) (P : R → Prop) (a b L U : ℝ)
    (fuel : ℕ) (l r : ℝ) : Outcome R → Prop
  | .found value => P value
  | .bracket l' r' => Bracket F a b L U l' r' ∧ r' - l' = (r - l) / (2 : ℝ) ^ fuel

theorem execution_calls_le_fuel {R : Type*} (trial : ℝ → Decision R)
    (fuel : ℕ) (l r : ℝ) : (execute trial (bisect fuel l r)).2 ≤ fuel := by
  induction fuel generalizing l r with
  | zero => simp [bisect, execute]
  | succ n ih =>
    cases htrial : trial ((l + r) / 2) with
    | accept value => simp [bisect, execute, htrial]
    | low =>
      simpa only [bisect, execute, htrial] using Nat.add_le_add_right (ih ((l + r) / 2) r) 1
    | high =>
      simpa only [bisect, execute, htrial] using Nat.add_le_add_right (ih l ((l + r) / 2)) 1

theorem run_spec {R : Type*} (trial : ℝ → Decision R) (F : ℝ → ℝ) (P : R → Prop)
    (a b L U : ℝ)
    (haccept : ∀ x ∈ Set.Icc L U, ∀ value, trial x = .accept value → P value)
    (hlow : ∀ x ∈ Set.Icc L U, trial x = .low → F x ≤ a)
    (hhigh : ∀ x ∈ Set.Icc L U, trial x = .high → b ≤ F x)
    (fuel : ℕ) (l r : ℝ) (hbracket : Bracket F a b L U l r) :
    Spec F P a b L U fuel l r (execute trial (bisect fuel l r)).1 := by
  induction fuel generalizing l r with
  | zero =>
    simp only [bisect, execute, Spec, pow_zero, div_one]
    exact ⟨hbracket, True.intro⟩
  | succ n ih =>
    rcases hbracket with ⟨hl, hlr, hr, hFl, hFr⟩
    let m := (l + r) / 2
    have hm : m ∈ Set.Icc L U := ⟨by dsimp only [m]; linarith, by dsimp only [m]; linarith⟩
    cases htrial : trial ((l + r) / 2) with
    | accept value =>
      simp only [bisect, execute, htrial, Spec]
      exact haccept m hm value htrial
    | low =>
      have hnew : Bracket F a b L U m r :=
        ⟨hm.1, by dsimp only [m]; linarith, hr, hlow m hm htrial, hFr⟩
      have hi := ih m r hnew
      simp only [bisect, execute, htrial]
      cases hres : (execute trial (bisect n m r)).1 with
      | found value => simpa only [hres, Spec] using hi
      | bracket l' r' =>
        simp only [hres, Spec] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [hi.2]
        dsimp only [m]
        rw [pow_succ]
        field_simp
        <;> ring
    | high =>
      have hnew : Bracket F a b L U l m :=
        ⟨hl, by dsimp only [m]; linarith, hm.2, hFl, hhigh m hm htrial⟩
      have hi := ih l m hnew
      simp only [bisect, execute, htrial]
      cases hres : (execute trial (bisect n l m)).1 with
      | found value => simpa only [hres, Spec] using hi
      | bracket l' r' =>
        simp only [hres, Spec] at hi ⊢
        refine ⟨hi.1, ?_⟩
        rw [hi.2]
        dsimp only [m]
        rw [pow_succ]
        field_simp
        <;> ring

noncomputable def halvingCount (a tau : ℝ) : ℕ :=
  Nat.ceil (Real.logb 2 (max 1 (a / tau)))

theorem halving_precision (a tau : ℝ) (htau : 0 < tau) :
    a / (2 : ℝ) ^ halvingCount a tau ≤ tau := by
  have hm : 0 < max 1 (a / tau) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hn : Real.logb 2 (max 1 (a / tau)) ≤ (halvingCount a tau : ℝ) := Nat.le_ceil _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hm,
    Real.rpow_natCast] at hp
  have hh := le_trans (le_max_right 1 (a / tau)) hp
  have hmul := (div_le_iff₀ htau).mp hh
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  nlinarith only [hmul]

noncomputable def searchFuel (K L U a b : ℝ) : ℕ :=
  halvingCount (K * (U - L)) ((b - a) / 2)

theorem bisection_success_and_calls {R : Type*}
    (trial : ℝ → Decision R) (F : ℝ → ℝ) (P : R → Prop)
    (a b L U K : ℝ) (hgap : a < b) (hK : 0 ≤ K)
    (hLU : L ≤ U) (hL : F L ≤ a) (hU : b ≤ F U)
    (hLip : ∀ x ∈ Set.Icc L U, ∀ y ∈ Set.Icc L U, |F x - F y| ≤ K * |x - y|)
    (haccept : ∀ x ∈ Set.Icc L U, ∀ value, trial x = .accept value → P value)
    (hlow : ∀ x ∈ Set.Icc L U, trial x = .low → F x ≤ a)
    (hhigh : ∀ x ∈ Set.Icc L U, trial x = .high → b ≤ F x) :
    ∃ value : R,
      (execute trial (bisect (searchFuel K L U a b) L U)).1 = .found value ∧ P value ∧
      (execute trial (bisect (searchFuel K L U a b) L U)).2 ≤ searchFuel K L U a b := by
  let n := searchFuel K L U a b
  have hspec := run_spec trial F P a b L U haccept hlow hhigh n L U
    ⟨le_rfl, hLU, le_rfl, hL, hU⟩
  cases hout : (execute trial (bisect n L U)).1 with
  | found value =>
    refine ⟨value, rfl, ?_, execution_calls_le_fuel trial n L U⟩
    simpa only [hout, Spec] using hspec
  | bracket l r =>
    simp only [hout, Spec, Bracket] at hspec
    rcases hspec with ⟨⟨hl, hlr, hr, hFl, hFr⟩, hwidth⟩
    have hlI : l ∈ Set.Icc L U := ⟨hl, le_trans hlr hr⟩
    have hrI : r ∈ Set.Icc L U := ⟨le_trans hl hlr, hr⟩
    have hdiff := hLip r hrI l hlI
    rw [abs_of_nonneg (sub_nonneg.mpr hlr)] at hdiff
    have hfg : b - a ≤ F r - F l := by linarith only [hFl, hFr]
    have hg : b - a ≤ K * (r - l) := hfg.trans ((le_abs_self _).trans hdiff)
    have hsmall := halving_precision (K * (U - L)) ((b - a) / 2) (by linarith only [hgap])
    change K * (U - L) / (2 : ℝ) ^ n ≤ (b - a) / 2 at hsmall
    have heq : K * (r - l) = K * (U - L) / (2 : ℝ) ^ n := by rw [hwidth]; ring
    rw [heq] at hg
    exfalso
    linarith only [hg, hsmall, hgap]

theorem searchFuel_log_bound (K L U a b : ℝ) :
    (searchFuel K L U a b : ℝ) ≤
      1 + Real.logb 2 (max 1 ((K * (U - L)) / ((b - a) / 2))) := by
  unfold searchFuel halvingCount
  have h0 : 0 ≤ Real.logb 2 (max 1 ((K * (U - L)) / ((b - a) / 2))) :=
    Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have h := Nat.ceil_lt_add_one h0
  linarith only [h]

end FangqingHysteresis


namespace OriginalCoupledBetaSearch
open _root_.OriginalCoupledBetaSearch

open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalBetaATSUniform
open OriginalBetaATSTrial (Answer TrialResult)
open FangqingHysteresis (Decision Outcome)

structure Settings where
  mu : ℝ
  Lg : ℝ
  M : ℝ
  A : ℝ
  sigma : ℝ
  sigmaLow : ℝ
  sigmaUp : ℝ
  rho : ℝ

structure Legal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_pos : 0 < c.M
  A_pos : 0 < c.A
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

noncomputable def lower (c : Settings) (G : ℝ) : ℝ :=
  betaLow c.A (lambdaLow c.M c.sigmaLow c.sigma G)
noncomputable def margin (c : Settings) : ℝ :=
  highMargin c.A (lambdaHigh c.M c.rho c.sigma c.sigmaUp)
noncomputable def upper (c : Settings) : ℝ := 1 - margin c
noncomputable def lambdaMin (c : Settings) (G : ℝ) : ℝ := c.A * lower c G ^ 2
noncomputable def lambdaMax (c : Settings) : ℝ := c.A / margin c
noncomputable def tolerance (c : Settings) (G : ℝ) : ℝ :=
  uniformTolerance c.mu c.Lg c.M (lambdaMin c G) (lambdaMax c) c.sigma c.rho
noncomputable def thresholdLow (c : Settings) : ℝ := c.sigmaLow * (1 + c.sigma) / c.M
noncomputable def thresholdHigh (c : Settings) : ℝ := c.sigmaUp * (1 - c.sigma) / c.M

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def modulus (c : Settings) (G : ℝ) (x y : E) : ℝ :=
  sizeModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G ‖x - y‖

noncomputable def observedGradientBound (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  ‖(getter (y, 1)).grad‖ + 1 + c.Lg * ‖x - y‖

inductive Result (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | stop (point : E)
  | window (beta : ℝ) (displacement : E) (outputAnswer : Answer E)

noncomputable def classifiedTrial (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) (b : ℝ) : Decision (Result E) := by
  classical
  exact match OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
    | .stop w => .accept (.stop w)
    | .step d aY =>
        if c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M then
          .accept (.window b d aY)
        else if lambda c.A b * ‖d‖ < c.sigmaLow / c.M then .low else .high

def ValidResult (g : E → ℝ) (c : Settings) (G deltaY : ℝ) (x y : E) : Result E → Prop
  | .stop w => ‖gradient g w‖ ≤ c.rho
  | .window b d aY =>
      b ∈ Set.Icc (lower c G) (upper c) ∧ 0 < b ∧ b < 1 ∧
      0 < lambda c.A b ∧
      c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖lambda c.A b • CertifiedATS.trueVector (gradient g (center x y b))
        (fderiv ℝ (gradient g) (center x y b)) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (center x y b + d)‖ ≤ deltaY ∧
      weight c.A b = (lambda c.A b + Real.sqrt (lambda c.A b ^ 2 + 4 * lambda c.A b * c.A)) / 2 ∧
      center x y b = (c.A / (c.A + weight c.A b)) • y +
        (weight c.A b / (c.A + weight c.A b)) • x

theorem compact_properties (c : Settings) (hc : Legal c) (G : ℝ) (hG : 0 ≤ G) :
    0 < lower c G ∧ lower c G ≤ 1 / 4 ∧ 0 < margin c ∧ margin c ≤ 1 / 4 ∧
    3 / 4 ≤ upper c ∧ upper c < 1 ∧ lower c G ≤ upper c ∧
    0 < lambdaMin c G ∧ 0 < lambdaMax c := by
  have hLow := lambdaLow_positive c.M c.sigmaLow c.sigma G hc.M_pos hc.low_pos hc.sigma_lt_one hG
  have hlo := betaLow_properties c.A _ hc.A_pos hLow.1
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hHigh : 0 ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
    dsimp [lambdaHigh]
    have hm := hc.M_pos
    have hr := hc.rho_pos
    have hs := hc.sigma_pos
    positivity
  have hhi := betaHigh_properties c.A _ hc.A_pos hHigh
  have hrange : lower c G ≤ upper c := by
    change betaLow c.A _ ≤ betaHigh c.A _
    linarith only [hlo.2.1, hhi.2.2.1]
  refine ⟨hlo.1, hlo.2.1, hhi.1, hhi.2.1, hhi.2.2.1, hhi.2.2.2.1, hrange, ?_, ?_⟩
  · exact mul_pos hc.A_pos (sq_pos_of_pos hlo.1)
  · exact div_pos hc.A_pos hhi.1

theorem interval_lambda_bounds (c : Settings) (hc : Legal c) (G : ℝ) (hG : 0 ≤ G)
    (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c)) :
    0 < b ∧ b < 1 ∧ 0 < lambda c.A b ∧
      lambdaMin c G ≤ lambda c.A b ∧ lambda c.A b ≤ lambdaMax c := by
  have hp := compact_properties c hc G hG
  have hb0 : 0 < b := hp.1.trans_le hb.1
  have hb1 : b < 1 := hb.2.trans_lt hp.2.2.2.2.2.1
  have hlam := (coupled_weights c.A b hc.A_pos hb0 hb1).1
  have hh := lambda_compact_bounds c.A (lower c G) (margin c) b hc.A_pos hp.1 hp.2.2.1 hb.1 hb.2
  exact ⟨hb0, hb1, hlam, hh.1, hh.2⟩

theorem observed_bound_is_valid
    (g : E → ℝ) (c : Settings) (hc : Legal c) (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    0 ≤ observedGradientBound getter c x y ∧
      gradientBound g c.Lg x y ≤ observedGradientBound getter c x y := by
  refine ⟨?_, ?_⟩
  · dsimp [observedGradientBound]
    have hLg := hc.Lg_nonneg
    positivity
  · exact gradient_upper_from_certificate g c.Lg x y _ 1 (hgetter y 1 (by norm_num)).1

theorem interval_trial_spec
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c)) :
    OriginalBetaATSTrial.TrialSpec g c.M (lambda c.A b) c.sigma c.rho deltaY (center x y b)
      (OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b)) := by
  have hp := compact_properties c hc G hG
  have hl := interval_lambda_bounds c hc G hG b hb
  exact OriginalBetaATSTrial.trial_uniform_spec g c.mu c.Lg c.M (lambdaMin c G) (lambdaMax c)
    (lambda c.A b) c.sigma c.rho deltaY hc.mu_pos hc.Lg_nonneg hc.M_pos.le
    hp.2.2.2.2.2.2.2.1 hl.2.2.2.1 hl.2.2.2.2 hc.sigma_pos hc.rho_pos
    hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter (center x y b)


theorem actual_modulus_spec
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G : ℝ) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    0 ≤ modulus c G x y ∧
    (∀ b ∈ Set.Icc (lower c G) (upper c), ∀ d ∈ Set.Icc (lower c G) (upper c),
      |betaSize g c.M c.A x y b - betaSize g c.M c.A x y d| ≤ modulus c G x y * |b - d|) := by
  have hp := compact_properties c hc G hG0
  have hmu := hc.mu_pos
  have hLg := hc.Lg_nonneg
  have hM := hc.M_pos
  have hA := hc.A_pos
  have hlo := hp.1
  have ht := hp.2.2.1
  refine ⟨?_, ?_⟩
  · dsimp [modulus, sizeModulus, stepModulus, inverseLambdaModulus]
    positivity
  · intro b hb d hd
    exact betaSize_lipschitz g c.mu c.Lg c.M c.A (lower c G) (margin c) G
      hc.mu_pos hc.Lg_nonneg hc.M_pos.le hc.A_pos hp.1 hp.2.2.1 hC2 hsc hlip hHlip
      x y hG b d hb.1 hd.1 hb.2 hd.2

theorem threshold_gap (c : Settings) (hc : Legal c) : thresholdLow c < thresholdHigh c :=
  div_lt_div_of_pos_right hc.gap hc.M_pos

theorem classified_accept_valid
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    ValidResult g c G deltaY x y value := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w =>
    simp only [classifiedTrial, hr] at haccept
    have hv := Decision.accept.inj haccept
    rw [← hv]
    rw [hr] at ht
    exact ht
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at haccept
      have hv := Decision.accept.inj haccept
      rw [← hv]
      exact ⟨hb, hl.1, hl.2.1, hl.2.2.1, hw.1, hw.2, ht.1, ht.2.1,
        coupled_square_root_formula c.A b hc.A_pos hl.1 hl.2.1,
        (coupled_center c.A b hc.A_pos hl.1 hl.2.1 x y).symm⟩
    · simp only [classifiedTrial, hr, if_neg hw] at haccept
      split_ifs at haccept <;> cases haccept

theorem classified_low_threshold
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (hlow : classifiedTrial getter c G deltaY x y b = .low) :
    betaSize g c.M c.A x y b ≤ thresholdLow c := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w => simp only [classifiedTrial, hr] at hlow; cases hlow
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at hlow; cases hlow
    · by_cases hm : lambda c.A b * ‖d‖ < c.sigmaLow / c.M
      · exact low_failure_exact_threshold g c.mu c.M (lambda c.A b) c.sigma c.sigmaLow
          hc.mu_pos hc.M_pos hl.2.2.1 hc.sigma_pos.le hC2 hsc (center x y b) d ht.1 hm
      · simp only [classifiedTrial, hr, if_neg hw, if_neg hm] at hlow; cases hlow

theorem classified_high_threshold
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (hhigh : classifiedTrial getter c G deltaY x y b = .high) :
    thresholdHigh c ≤ betaSize g c.M c.A x y b := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w => simp only [classifiedTrial, hr] at hhigh; cases hhigh
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at hhigh; cases hhigh
    · by_cases hm : lambda c.A b * ‖d‖ < c.sigmaLow / c.M
      · simp only [classifiedTrial, hr, if_neg hw, if_pos hm] at hhigh; cases hhigh
      · have hbound : c.sigmaUp / c.M < lambda c.A b * ‖d‖ := by
          apply lt_of_not_ge
          intro hle
          exact hw ⟨le_of_not_gt hm, hle⟩
        exact high_failure_exact_threshold g c.mu c.M (lambda c.A b) c.sigma c.sigmaUp
          hc.mu_pos hc.M_pos hl.2.2.1 hc.sigma_lt_one hC2 hsc (center x y b) d ht.1 hbound


theorem lower_endpoint_not_high
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    classifiedTrial getter c G deltaY x y (lower c G) ≠ .high := by
  classical
  intro hhigh
  have hp := compact_properties c hc G hG0
  have hb : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A (lower c G)) (tolerance c G)
      c.rho deltaY (center x y (lower c G)) with
  | stop w => simp only [classifiedTrial, hr] at hhigh; cases hhigh
  | step d aY =>
    rw [hr] at ht
    have hs := low_endpoint_is_low g c.mu c.Lg c.M c.A c.sigmaLow c.sigma G
      hc.mu_pos hc.Lg_nonneg hc.M_pos hc.A_pos hc.low_pos hc.sigma_lt_one hG0 hC2 hsc hlip x y d hG ht.1
    change lambda c.A (lower c G) * ‖d‖ < c.sigmaLow / c.M at hs
    have hn : ¬(c.sigmaLow / c.M ≤ lambda c.A (lower c G) * ‖d‖ ∧
        lambda c.A (lower c G) * ‖d‖ ≤ c.sigmaUp / c.M) := by
      intro hw
      exact not_le_of_gt hs hw.1
    simp only [classifiedTrial, hr, if_neg hn, if_pos hs] at hhigh
    cases hhigh

theorem upper_endpoint_not_low
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) : classifiedTrial getter c G deltaY x y (upper c) ≠ .low := by
  classical
  intro hlow
  have hp := compact_properties c hc G hG0
  have hb : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hb
  have hl := interval_lambda_bounds c hc G hG0 (upper c) hb
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hHigh0 : 0 ≤ lambdaHigh c.M c.rho c.sigma c.sigmaUp := by
    dsimp [lambdaHigh]
    have hM := hc.M_pos
    have hRho := hc.rho_pos
    have hSigma := hc.sigma_pos
    positivity
  have hlarge := (betaHigh_properties c.A (lambdaHigh c.M c.rho c.sigma c.sigmaUp) hc.A_pos hHigh0).2.2.2.2
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A (upper c)) (tolerance c G)
      c.rho deltaY (center x y (upper c)) with
  | stop w => simp only [classifiedTrial, hr] at hlow; cases hlow
  | step d aY =>
    rw [hr] at ht
    have hs : c.sigmaUp / c.M < lambda c.A (upper c) * ‖d‖ := by
      apply lt_of_not_ge
      intro hwindow
      have hg := large_lambda_upper_is_small g c.M c.rho c.sigma c.sigmaUp (lambda c.A (upper c))
        hc.M_pos hc.rho_pos hc.sigma_pos.le hUp.le hl.2.2.1 hlarge hC2 hHlip (center x y (upper c)) d ht.1 hwindow
      exact not_lt_of_ge hg ht.2.2
    have hn : ¬(c.sigmaLow / c.M ≤ lambda c.A (upper c) * ‖d‖ ∧
        lambda c.A (upper c) * ‖d‖ ≤ c.sigmaUp / c.M) := by
      intro hw
      exact not_le_of_gt hs hw.2
    have hLowUp : c.sigmaLow / c.M < c.sigmaUp / c.M := div_lt_div_of_pos_right hc.low_lt_up hc.M_pos
    have hnotlow : ¬lambda c.A (upper c) * ‖d‖ < c.sigmaLow / c.M :=
      not_lt_of_ge (hLowUp.le.trans hs.le)
    simp only [classifiedTrial, hr, if_neg hn, if_neg hnotlow] at hlow
    cases hlow

noncomputable def fuel (c : Settings) (G : ℝ) (x y : E) : ℕ :=
  FangqingHysteresis.searchFuel (modulus c G x y) (lower c G) (upper c) (thresholdLow c) (thresholdHigh c)

noncomputable def searchProgram (c : Settings) (G : ℝ) (x y : E) :
    FangqingHysteresis.Program (Decision (Result E)) (Outcome (Result E)) :=
  .ask (lower c G) (fun left => match left with
    | .accept value => .pure (.found value)
    | _ => .ask (upper c) (fun right => match right with
      | .accept value => .pure (.found value)
      | _ => FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c)))

theorem bisection_after_endpoints
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G)
    (hleft : classifiedTrial getter c G deltaY x y (lower c G) = .low)
    (hright : classifiedTrial getter c G deltaY x y (upper c) = .high) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).1 = .found value ∧
      ValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).2 ≤ fuel c G x y := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have hK := actual_modulus_spec g c hc G hG0 hC2 hsc hlip hHlip x y hG
  exact FangqingHysteresis.bisection_success_and_calls
    (classifiedTrial getter c G deltaY x y) (betaSize g c.M c.A x y) (ValidResult g c G deltaY x y)
    (thresholdLow c) (thresholdHigh c) (lower c G) (upper c) (modulus c G x y)
    (threshold_gap c hc) hK.1 hp.2.2.2.2.2.2.1
    (classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL hleft)
    (classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU hright)
    hK.2
    (fun b hb value hv => classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value hv)
    (fun b hb hv => classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)
    (fun b hb hv => classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)


noncomputable def classifyResult (c : Settings) (b : ℝ) : TrialResult E → Decision (Result E) := by
  classical
  exact fun raw => match raw with
    | .stop w => .accept (.stop w)
    | .step d aY =>
        if c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M then
          .accept (.window b d aY)
        else if lambda c.A b * ‖d‖ < c.sigmaLow / c.M then .low else .high

theorem classifiedTrial_factor (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) (b : ℝ) :
    classifiedTrial getter c G deltaY x y b = classifyResult c b
      (OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b)) := rfl

theorem positive_search_success_and_calls
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).1 = .found value ∧
      ValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).2 ≤ fuel c G x y + 2 := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  cases hleft : classifiedTrial getter c G deltaY x y (lower c G) with
  | accept value =>
    refine ⟨value, ?_, ?_, ?_⟩
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
    · exact classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL value hleft
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
      omega
  | high => exact False.elim (lower_endpoint_not_high g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y hG hleft)
  | low =>
    cases hright : classifiedTrial getter c G deltaY x y (upper c) with
    | accept value =>
      refine ⟨value, ?_, ?_, ?_⟩
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
      · exact classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU value hright
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
        omega
    | low => exact False.elim (upper_endpoint_not_low g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter x y hright)
    | high =>
      obtain ⟨value, hrun, hvalid, hcount⟩ := bisection_after_endpoints g c hc G deltaY hG0 hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter x y hG hleft hright
      refine ⟨value, ?_, hvalid, ?_⟩
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright] using hrun
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright, Nat.add_assoc] using Nat.add_le_add_right hcount 2

theorem positive_search_log_bound (c : Settings) (G : ℝ) (x y : E) :
    (fuel c G x y : ℝ) + 2 ≤
      3 + Real.logb 2 (max 1 (((modulus c G x y) * (upper c - lower c G)) /
        ((thresholdHigh c - thresholdLow c) / 2))) := by
  have h := FangqingHysteresis.searchFuel_log_bound (modulus c G x y) (lower c G) (upper c) (thresholdLow c) (thresholdHigh c)
  change (fuel c G x y : ℝ) ≤ _ at h
  linarith only [h]

end OriginalCoupledBetaSearch


namespace FangqingGetterComposition
open _root_.FangqingGetterComposition

open OriginalBetaATSTrial

noncomputable def bind {Q A R S : Type*} :
    GetterProgram Q A R → (R → GetterProgram Q A S) → GetterProgram Q A S
  | .pure r, next => next r
  | .ask q cont, next => .ask q (fun answer => bind (cont answer) next)

noncomputable def map {Q A R S : Type*} (f : R → S) (program : GetterProgram Q A R) :
    GetterProgram Q A S := bind program (fun r => .pure (f r))

theorem execute_bind {Q A R S : Type*} (getter : Q → A)
    (program : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    execute getter (bind program next) =
      ((execute getter (next (execute getter program).1)).1,
        (execute getter program).2 + (execute getter (next (execute getter program).1)).2) := by
  induction program with
  | pure r => simp only [bind, execute, zero_add]
  | ask q cont ih =>
    simp only [bind, execute, ih]
    exact Prod.ext rfl (by omega)

theorem execute_map {Q A R S : Type*} (getter : Q → A) (f : R → S)
    (program : GetterProgram Q A R) :
    execute getter (map f program) = (f (execute getter program).1, (execute getter program).2) := by
  simp only [map, execute_bind, execute, add_zero]

noncomputable def derivedReply {Q A Reply : Type*} (getter : Q → A)
    (trials : ℝ → GetterProgram Q A Reply) (point : ℝ) : Reply := (execute getter (trials point)).1

noncomputable def lower {Q A Reply Result : Type*} (trials : ℝ → GetterProgram Q A Reply) :
    FangqingHysteresis.Program Reply Result → GetterProgram Q A Result
  | .pure r => .pure r
  | .ask point cont => bind (trials point) (fun reply => lower trials (cont reply))

theorem lower_result_and_count {Q A Reply Result : Type*}
    (getter : Q → A) (trials : ℝ → GetterProgram Q A Reply) (K : ℕ)
    (htrial : ∀ point : ℝ, (execute getter (trials point)).2 ≤ K)
    (program : FangqingHysteresis.Program Reply Result) :
    (execute getter (lower trials program)).1 =
      (FangqingHysteresis.execute (derivedReply getter trials) program).1 ∧
    (execute getter (lower trials program)).2 ≤
      K * (FangqingHysteresis.execute (derivedReply getter trials) program).2 := by
  induction program with
  | pure r => simp only [lower, execute, FangqingHysteresis.execute, mul_zero, le_refl, and_self]
  | ask point cont ih =>
    have hi := ih (derivedReply getter trials point)
    have hc := htrial point
    simp only [lower, execute_bind, FangqingHysteresis.execute]
    constructor
    · exact hi.1
    · change (execute getter (trials point)).2 +
        (execute getter (lower trials (cont (derivedReply getter trials point)))).2 ≤
          K * ((FangqingHysteresis.execute (derivedReply getter trials)
            (cont (derivedReply getter trials point))).2 + 1)
      have hm := add_le_add hc hi.2
      nlinarith only [hm]

noncomputable def withInitial {Q A Reply Result : Type*} (request : Q)
    (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) : GetterProgram Q A Result :=
  .ask request (fun answer => lower (trials answer) (program answer))

theorem withInitial_result_and_count {Q A Reply Result : Type*}
    (getter : Q → A) (request : Q) (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) (K : ℕ)
    (htrial : ∀ answer point, (execute getter (trials answer point)).2 ≤ K) :
    (execute getter (withInitial request trials program)).1 =
      (FangqingHysteresis.execute (derivedReply getter (trials (getter request))) (program (getter request))).1 ∧
    (execute getter (withInitial request trials program)).2 ≤
      1 + K * (FangqingHysteresis.execute
        (derivedReply getter (trials (getter request))) (program (getter request))).2 := by
  have hi := lower_result_and_count getter (trials (getter request)) K (htrial (getter request))
    (program (getter request))
  simp only [withInitial, execute]
  exact ⟨hi.1, by omega⟩

section ActualTaylorTrials
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def mappedTaylorTrial {Reply : Type*}
    (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    GetterProgram (E × ℝ) (Answer E) Reply :=
  map (classify point) (trialProgram M (lam point) delta rho deltaY (center point))

theorem mappedTaylorTrial_calls {Reply : Type*}
    (getter : E × ℝ → Answer E) (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    (execute getter (mappedTaylorTrial classify M delta rho deltaY lam center point)).2 ≤ 2 := by
  rw [mappedTaylorTrial, execute_map]
  exact trial_getter_calls getter M (lam point) delta rho deltaY (center point)

theorem lowered_actual_trials_result_and_count {Reply Result : Type*}
    (getter : E × ℝ → Answer E) (classify : ℝ → TrialResult E → Reply)
    (M delta rho deltaY : ℝ) (lam : ℝ → ℝ) (center : ℝ → E)
    (program : FangqingHysteresis.Program Reply Result) :
    (execute getter (lower (mappedTaylorTrial classify M delta rho deltaY lam center) program)).1 =
      (FangqingHysteresis.execute
        (derivedReply getter (mappedTaylorTrial classify M delta rho deltaY lam center)) program).1 ∧
    (execute getter (lower (mappedTaylorTrial classify M delta rho deltaY lam center) program)).2 ≤
      2 * (FangqingHysteresis.execute
        (derivedReply getter (mappedTaylorTrial classify M delta rho deltaY lam center)) program).2 :=
  lower_result_and_count getter _ 2 (mappedTaylorTrial_calls getter classify M delta rho deltaY lam center) program

end ActualTaylorTrials
end FangqingGetterComposition

namespace FangqingGetterComposition
open _root_.FangqingGetterComposition
open OriginalBetaATSTrial

noncomputable def trace {Q A R : Type*} (getter : Q → A) : GetterProgram Q A R → List Q
  | .pure _ => []
  | .ask q next => q :: trace getter (next (getter q))

noncomputable def baseCost {Q A R : Type*} (getter : Q → A) (cost : Q → ℕ) : GetterProgram Q A R → ℕ
  | .pure _ => 0
  | .ask q next => cost q + baseCost getter cost (next (getter q))

def AllRequests {Q A R : Type*} (P : Q → Prop) : GetterProgram Q A R → Prop
  | .pure _ => True
  | .ask q next => P q ∧ ∀ answer : A, AllRequests P (next answer)

theorem trace_length_eq_count {Q A R : Type*} (getter : Q → A) (program : GetterProgram Q A R) :
    (trace getter program).length = (execute getter program).2 := by
  induction program with
  | pure r => rfl
  | ask q next ih => simp only [trace, execute, List.length_cons, ih]

theorem baseCost_eq_trace_sum {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (program : GetterProgram Q A R) :
    baseCost getter cost program = ((trace getter program).map cost).sum := by
  induction program with
  | pure r => rfl
  | ask q next ih => simp only [baseCost, trace, List.map_cons, List.sum_cons, ih]

theorem allRequests_trace {Q A R : Type*} (getter : Q → A) (P : Q → Prop)
    (program : GetterProgram Q A R) (hprogram : AllRequests P program) :
    ∀ q ∈ trace getter program, P q := by
  induction program with
  | pure r => simp only [trace, List.not_mem_nil, false_implies, implies_true]
  | ask q next ih =>
    intro req hmem
    simp only [trace, List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · exact hprogram.1
    · exact ih (getter q) (hprogram.2 (getter q)) req htail

theorem allRequests_bind {Q A R S : Type*} (P : Q → Prop)
    (program : GetterProgram Q A R) (next : R → GetterProgram Q A S)
    (hprogram : AllRequests P program) (hnext : ∀ r : R, AllRequests P (next r)) :
    AllRequests P (bind program next) := by
  induction program with
  | pure r => exact hnext r
  | ask q cont ih =>
    exact ⟨hprogram.1, fun answer => ih answer (hprogram.2 answer)⟩

theorem allRequests_map {Q A R S : Type*} (P : Q → Prop) (f : R → S)
    (program : GetterProgram Q A R) (hprogram : AllRequests P program) : AllRequests P (map f program) :=
  allRequests_bind P program _ hprogram (fun _ => True.intro)

theorem allRequests_lower {Q A Reply Result : Type*}
    (P : Q → Prop) (trials : ℝ → GetterProgram Q A Reply)
    (htrials : ∀ point : ℝ, AllRequests P (trials point))
    (program : FangqingHysteresis.Program Reply Result) : AllRequests P (lower trials program) := by
  induction program with
  | pure r => exact True.intro
  | ask point cont ih => exact allRequests_bind P (trials point) _ (htrials point) ih

theorem trace_withInitial_requests {Q A Reply Result : Type*}
    (getter : Q → A) (request : Q) (trials : A → ℝ → GetterProgram Q A Reply)
    (program : A → FangqingHysteresis.Program Reply Result) (P : Q → Prop)
    (hinitial : P request) (htrials : ∀ point : ℝ, AllRequests P (trials (getter request) point)) :
    ∀ q ∈ trace getter (withInitial request trials program), P q := by
  intro q hq
  simp only [withInitial, trace, List.mem_cons] at hq
  rcases hq with rfl | htail
  · exact hinitial
  · exact allRequests_trace getter P _ (allRequests_lower P _ htrials _) q htail

theorem list_cost_bound {Q : Type*} (requests : List Q) (cost : Q → ℕ) (C : ℕ)
    (hcost : ∀ q ∈ requests, cost q ≤ C) : (requests.map cost).sum ≤ C * requests.length := by
  induction requests with
  | nil => simp
  | cons q tail ih =>
    have hh := hcost q (by simp)
    have ht := ih (fun r hr => hcost r (by simp [hr]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith only [hh, ht]

theorem baseCost_le_mul_count {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (program : GetterProgram Q A R) (C : ℕ)
    (hcost : ∀ q ∈ trace getter program, cost q ≤ C) :
    baseCost getter cost program ≤ C * (execute getter program).2 := by
  rw [baseCost_eq_trace_sum]
  simpa only [trace_length_eq_count] using list_cost_bound (trace getter program) cost C hcost

section TaylorRequestPrecisions
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem trialProgram_precision_set (M lam delta rho deltaY : ℝ) (z : E) :
    AllRequests (fun q : E × ℝ => q.2 = delta ∨ q.2 = deltaY)
      (trialProgram M lam delta rho deltaY z) := by
  classical
  unfold trialProgram
  change (delta = delta ∨ delta = deltaY) ∧ _
  refine ⟨Or.inl rfl, ?_⟩
  intro a
  dsimp only
  split_ifs
  · exact True.intro
  · change (deltaY = delta ∨ deltaY = deltaY) ∧ _
    refine ⟨Or.inr rfl, ?_⟩
    intro aY
    dsimp only
    split_ifs <;> exact True.intro

theorem mappedTaylorTrial_precision_set {Reply : Type*}
    (classify : ℝ → TrialResult E → Reply) (M delta rho deltaY : ℝ)
    (lam : ℝ → ℝ) (center : ℝ → E) (point : ℝ) :
    AllRequests (fun q : E × ℝ => q.2 = delta ∨ q.2 = deltaY)
      (mappedTaylorTrial classify M delta rho deltaY lam center point) :=
  allRequests_map _ _ _ (trialProgram_precision_set M (lam point) delta rho deltaY (center point))

end TaylorRequestPrecisions
end FangqingGetterComposition

namespace FangqingGetterComposition
open _root_.FangqingGetterComposition
open OriginalBetaATSTrial

theorem allRequests_mono {Q A R : Type*} (P S : Q → Prop)
    (hPS : ∀ q, P q → S q) (program : GetterProgram Q A R)
    (hp : AllRequests P program) : AllRequests S program := by
  induction program with
  | pure r => exact True.intro
  | ask q next ih => exact ⟨hPS q hp.1, fun a => ih a (hp.2 a)⟩

noncomputable def logarithmicAtomicBound (K eta : ℝ) : ℕ :=
  ⌈K * (1 + Real.log (1 + eta⁻¹))⌉₊

theorem logarithmicAtomicBound_antitone (K floor eta : ℝ)
    (hK : 0 ≤ K) (hfloor : 0 < floor) (heta : floor ≤ eta) :
    logarithmicAtomicBound K eta ≤ logarithmicAtomicBound K floor := by
  have hpos : 0 < eta := hfloor.trans_le heta
  have hinv : eta⁻¹ ≤ floor⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hfloor heta
  have hlog : Real.log (1 + eta⁻¹) ≤ Real.log (1 + floor⁻¹) :=
    Real.log_le_log (by positivity) (by linarith only [hinv])
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (by linarith only [hlog]) hK)

theorem logarithmic_baseCost_bound {Q A R : Type*}
    (getter : Q → A) (cost : Q → ℕ) (accuracy : Q → ℝ)
    (program : GetterProgram Q A R) (K floor : ℝ)
    (hK : 0 ≤ K) (hfloor : 0 < floor)
    (hprecision : ∀ q ∈ trace getter program, floor ≤ accuracy q)
    (hatomic : ∀ q : Q, 0 < accuracy q → cost q ≤ logarithmicAtomicBound K (accuracy q)) :
    baseCost getter cost program ≤ logarithmicAtomicBound K floor * (execute getter program).2 := by
  apply baseCost_le_mul_count
  intro q hq
  exact (hatomic q (hfloor.trans_le (hprecision q hq))).trans
    (logarithmicAtomicBound_antitone K floor (accuracy q) hK hfloor (hprecision q hq))

end FangqingGetterComposition


namespace FangqingGetterComposition
open _root_.FangqingGetterComposition
open OriginalBetaATSTrial

noncomputable def primitiveLower {Q A BQ BA R : Type*}
    (oracle : Q → GetterProgram BQ BA A) : GetterProgram Q A R → GetterProgram BQ BA R
  | .pure r => .pure r
  | .ask q next => bind (oracle q) (fun a => primitiveLower oracle (next a))

noncomputable def implementedGetter {Q A BQ BA : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A) (q : Q) : A :=
  (execute baseAnswer (oracle q)).1

noncomputable def implementedCost {Q A BQ BA : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A) (q : Q) : ℕ :=
  (execute baseAnswer (oracle q)).2

theorem primitiveLower_execution {Q A BQ BA R : Type*}
    (baseAnswer : BQ → BA) (oracle : Q → GetterProgram BQ BA A)
    (program : GetterProgram Q A R) :
    execute baseAnswer (primitiveLower oracle program) =
      ((execute (implementedGetter baseAnswer oracle) program).1,
        baseCost (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle) program) := by
  induction program with
  | pure r => rfl
  | ask q next ih =>
    simp only [primitiveLower, execute_bind, ih, execute, baseCost, implementedGetter, implementedCost]

end FangqingGetterComposition

namespace FangqingGetterComposition
open _root_.FangqingGetterComposition

theorem logarithmicAtomicBound_real_le (K eta : ℝ) (hK : 0 ≤ K) (heta : 0 < eta) :
    (logarithmicAtomicBound K eta : ℝ) ≤ K * (1 + Real.log (1 + eta⁻¹)) + 1 := by
  have hlog : 0 ≤ Real.log (1 + eta⁻¹) := Real.log_nonneg (by have h := inv_nonneg.mpr heta.le; linarith only [h])
  exact (Nat.ceil_lt_add_one (mul_nonneg hK (by linarith only [hlog]))).le

end FangqingGetterComposition


namespace OriginalCoupledGetterProgram
open _root_.OriginalCoupledGetterProgram

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def initialBound (c : Settings) (x y : E) (a : Answer E) : ℝ :=
  ‖a.grad‖ + 1 + c.Lg * ‖x - y‖

noncomputable def trials (c : Settings) (G deltaY : ℝ) (x y : E) :
    ℝ → GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Decision (Result E)) :=
  mappedTaylorTrial (classifyResult c) c.M (tolerance c G) c.rho deltaY
    (lambda c.A) (center x y)

noncomputable def positiveProgram (c : Settings) (deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  withInitial (y, 1) (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y)

theorem trials_derivedReply (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (x y : E) :
    derivedReply getter (trials c G deltaY x y) = classifiedTrial getter c G deltaY x y := by
  funext b
  simp only [derivedReply, trials, mappedTaylorTrial, execute_map]
  rfl

theorem positiveProgram_result_and_count (getter : E × ℝ → Answer E) (c : Settings)
    (deltaY : ℝ) (x y : E) :
    (execute getter (positiveProgram c deltaY x y)).1 =
      (FangqingHysteresis.execute
        (classifiedTrial getter c (observedGradientBound getter c x y) deltaY x y)
        (searchProgram c (observedGradientBound getter c x y) x y)).1 ∧
    (execute getter (positiveProgram c deltaY x y)).2 ≤
      1 + 2 * (FangqingHysteresis.execute
        (classifiedTrial getter c (observedGradientBound getter c x y) deltaY x y)
        (searchProgram c (observedGradientBound getter c x y) x y)).2 := by
  have h := withInitial_result_and_count getter (y, 1)
    (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y) 2
    (fun a b => mappedTaylorTrial_calls getter (classifyResult c) c.M
      (tolerance c (initialBound c x y a)) c.rho deltaY (lambda c.A) (center x y) b)
  rw [trials_derivedReply] at h
  exact h

theorem positiveProgram_success_and_getter_calls
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (positiveProgram c deltaY x y)).1 = .found value ∧
      ValidResult g c (observedGradientBound getter c x y) deltaY x y value ∧
      (execute getter (positiveProgram c deltaY x y)).2 ≤
        2 * fuel c (observedGradientBound getter c x y) x y + 5 := by
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  obtain ⟨value, hrun, hvalid, hcount⟩ := positive_search_success_and_calls g c hc
    (observedGradientBound getter c x y) deltaY hbound.1 hdeltaY hdeltaYsmall
    hC2 hsc hlip hHlip getter hgetter x y hbound.2
  have hprogram := positiveProgram_result_and_count getter c deltaY x y
  exact ⟨value, hprogram.1.trans hrun, hvalid, by omega⟩

theorem positiveProgram_getter_log_bound
    (getter : E × ℝ → Answer E) (c : Settings) (deltaY : ℝ) (x y : E)
    (hcount : (execute getter (positiveProgram c deltaY x y)).2 ≤
      2 * fuel c (observedGradientBound getter c x y) x y + 5) :
    ((execute getter (positiveProgram c deltaY x y)).2 : ℝ) ≤
      7 + 2 * Real.logb 2 (max 1
        ((modulus c (observedGradientBound getter c x y) x y *
          (upper c - lower c (observedGradientBound getter c x y))) /
            ((thresholdHigh c - thresholdLow c) / 2))) := by
  have h := positive_search_log_bound c (observedGradientBound getter c x y) x y
  have hnat : ((execute getter (positiveProgram c deltaY x y)).2 : ℝ) ≤
      2 * (fuel c (observedGradientBound getter c x y) x y : ℝ) + 5 := by exact_mod_cast hcount
  linarith only [h, hnat]

end OriginalCoupledGetterProgram

namespace OriginalCoupledGetterProgram
open _root_.OriginalCoupledGetterProgram
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def precisionFloor (c : Settings) (G deltaY : ℝ) : ℝ :=
  min 1 (min (tolerance c G) deltaY)

theorem precisionFloor_positive (c : Settings) (hc : Legal c) (G deltaY : ℝ)
    (hG : 0 ≤ G) (hdeltaY : 0 < deltaY) : 0 < precisionFloor c G deltaY := by
  have hp := compact_properties c hc G hG
  have ht := OriginalBetaATSUniform.uniformTolerance_positive c.mu c.Lg c.M
    (lambdaMin c G) (lambdaMax c) c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le hp.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2 hc.sigma_pos hc.rho_pos
  exact lt_min (by norm_num) (lt_min ht hdeltaY)

theorem positiveProgram_request_precision_floor
    (getter : E × ℝ → Answer E) (c : Settings) (deltaY : ℝ) (x y : E) :
    ∀ q ∈ trace getter (positiveProgram c deltaY x y),
      precisionFloor c (observedGradientBound getter c x y) deltaY ≤ q.2 := by
  apply trace_withInitial_requests getter (y, 1)
    (fun a => trials c (initialBound c x y a) deltaY x y)
    (fun a => searchProgram c (initialBound c x y a) x y)
    (fun q : E × ℝ => precisionFloor c (observedGradientBound getter c x y) deltaY ≤ q.2)
  · exact min_le_left _ _
  · intro b
    apply allRequests_mono
      (fun q : E × ℝ => q.2 = tolerance c (observedGradientBound getter c x y) ∨ q.2 = deltaY)
    · intro q hq
      rcases hq with hq | hq
      · rw [hq]
        exact (min_le_right _ _).trans (min_le_left _ _)
      · rw [hq]
        exact (min_le_right _ _).trans (min_le_right _ _)
    · exact mappedTaylorTrial_precision_set (classifyResult c) c.M
        (tolerance c (observedGradientBound getter c x y)) c.rho deltaY (lambda c.A) (center x y) b

theorem positiveProgram_logarithmic_base_cost
    (getter : E × ℝ → Answer E) (cost : E × ℝ → ℕ) (c : Settings) (deltaY : ℝ) (x y : E)
    (K : ℝ) (hK : 0 ≤ K)
    (hfloor : 0 < precisionFloor c (observedGradientBound getter c x y) deltaY)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (hcount : (execute getter (positiveProgram c deltaY x y)).2 ≤
      2 * fuel c (observedGradientBound getter c x y) x y + 5) :
    baseCost getter cost (positiveProgram c deltaY x y) ≤
      logarithmicAtomicBound K (precisionFloor c (observedGradientBound getter c x y) deltaY) *
        (2 * fuel c (observedGradientBound getter c x y) x y + 5) := by
  exact (logarithmic_baseCost_bound getter cost Prod.snd (positiveProgram c deltaY x y) K _ hK hfloor
    (positiveProgram_request_precision_floor getter c deltaY x y) hatomic).trans
      (Nat.mul_le_mul_left _ hcount)

end OriginalCoupledGetterProgram


namespace OriginalFirstCoupledStep
open _root_.OriginalFirstCoupledStep

open OriginalCoupledBetaAlgebra
open OriginalCoupledBetaSearch
open OriginalBetaATSTrial (Answer)
open FangqingHysteresis (Decision Outcome)

structure CommonLegal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_pos : 0 < c.M
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

noncomputable def proxySettings (c : Settings) : Settings := {c with A := 1}

theorem proxy_legal (c : Settings) (hc : CommonLegal c) : Legal (proxySettings c) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, by norm_num [proxySettings], hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

theorem positive_legal (c : Settings) (hc : CommonLegal c) (hA : 0 < c.A) : Legal c :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hA, hc.sigma_pos,
    hc.sigma_lt_one, hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem center_same (z : E) (b : ℝ) : center z z b = z := by dsimp [center]; module

noncomputable def fixedSearchProgram (c : Settings) (G : ℝ) (z : E) :
    FangqingHysteresis.Program (Decision (Result E)) (Outcome (Result E)) :=
  searchProgram (proxySettings c) G z z

noncomputable def fixedTrial (getter : E × ℝ → Answer E) (c : Settings)
    (G deltaY : ℝ) (z : E) : ℝ → Decision (Result E) :=
  classifiedTrial getter (proxySettings c) G deltaY z z

def FixedValidResult (g : E → ℝ) (c : Settings) (deltaY : ℝ) (z : E) : Result E → Prop
  | .stop w => ‖gradient g w‖ ≤ c.rho
  | .window b d aY =>
      0 < b ∧ b < 1 ∧ 0 < lambda 1 b ∧
      c.sigmaLow / c.M ≤ lambda 1 b * ‖d‖ ∧ lambda 1 b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖lambda 1 b • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      ‖aY.grad - gradient g (z + d)‖ ≤ deltaY ∧
      (lambda 1 b + Real.sqrt (lambda 1 b ^ 2 + 4 * lambda 1 b * 0)) / 2 = lambda 1 b ∧
      (0 / (0 + lambda 1 b)) • z + (lambda 1 b / (0 + lambda 1 b)) • z = z ∧
      0 < 0 + lambda 1 b

theorem proxy_result_is_actual_first_step
    (g : E → ℝ) (c : Settings) (deltaY G : ℝ) (z : E) (value : Result E)
    (hvalid : ValidResult g (proxySettings c) G deltaY z z value) :
    FixedValidResult g c deltaY z value := by
  cases value with
  | stop w => exact hvalid
  | window b d aY =>
    rcases hvalid with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
    rw [center_same] at hATS herr
    have hzero := zero_weight_first_step (lambda 1 b) hlam z z
    exact ⟨hb0, hb1, hlam, hlow, hhigh, hATS, herr, hzero.1, hzero.2, by simpa only [zero_add, proxySettings] using hlam⟩

theorem first_step_success_and_calls
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ c.Lg * ‖x - y‖)
    (hHlip : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ c.M * ‖x - y‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ x : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (x, eta)).grad - gradient g x‖ ≤ eta ∧
      ‖(getter (x, eta)).hess - fderiv ℝ (gradient g) x‖ ≤ eta)
    (z : E) (hG : ‖gradient g z‖ ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (fixedTrial getter c G deltaY z) (fixedSearchProgram c G z)).1 = .found value ∧
      FixedValidResult g c deltaY z value ∧
      (FangqingHysteresis.execute (fixedTrial getter c G deltaY z) (fixedSearchProgram c G z)).2 ≤
        fuel (proxySettings c) G z z + 2 := by
  have hG' : OriginalBetaCurveBounds.gradientBound g (proxySettings c).Lg z z ≤ G := by
    simpa only [OriginalBetaCurveBounds.gradientBound, sub_self, norm_zero, mul_zero, add_zero] using hG
  obtain ⟨value, hrun, hvalid, hcount⟩ := positive_search_success_and_calls g (proxySettings c)
    (proxy_legal c hc) G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter z z hG'
  exact ⟨value, hrun, proxy_result_is_actual_first_step g c deltaY G z value hvalid, hcount⟩

theorem first_step_log_bound (c : Settings) (G : ℝ) (z : E) :
    (fuel (proxySettings c) G z z : ℝ) + 2 ≤
      3 + Real.logb 2 (max 1 (((modulus (proxySettings c) G z z) *
        (upper (proxySettings c) - lower (proxySettings c) G)) /
          ((thresholdHigh (proxySettings c) - thresholdLow (proxySettings c)) / 2))) :=
  positive_search_log_bound (proxySettings c) G z z

end OriginalFirstCoupledStep


namespace OriginalZeroCurvatureSearch
open _root_.OriginalZeroCurvatureSearch

open OriginalTaylorProxStability
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalBetaATSUniform
open OriginalBetaATSTrial (Answer TrialResult)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem zero_hessian_lipschitz_exact_taylor
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (z d : E) :
    CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) 0 d = gradient g (z + d) := by
  have hrem : ‖gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro e he
    let m := 2 * e / (‖d‖ ^ 2 + 1)
    have hm : 0 < m := by dsimp [m]; positivity
    have hHm : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ m * ‖x - y‖ := by
      intro x y
      have hh := hH0 x y
      simp only [zero_mul] at hh
      exact hh.trans (by positivity)
    have hb := RobustAHPE.gradient_taylor_remainder g hC2 m hm hHm z d
    calc
      _ ≤ m / 2 * ‖d‖ ^ 2 := hb
      _ ≤ 0 + e := by
        have heq : m / 2 * ‖d‖ ^ 2 = e * ‖d‖ ^ 2 / (‖d‖ ^ 2 + 1) := by dsimp [m]; ring
        rw [heq, zero_add]
        apply (div_le_iff₀ (by positivity : 0 < ‖d‖ ^ 2 + 1)).mpr
        nlinarith only [he]
  have hzero := norm_eq_zero.mp (le_antisymm hrem (norm_nonneg _))
  have heq : gradient g (z + d) = gradient g z + fderiv ℝ (gradient g) z d := by
    calc
      _ = (gradient g (z + d) - gradient g z - fderiv ℝ (gradient g) z d) +
          (gradient g z + fderiv ℝ (gradient g) z d) := by abel
      _ = _ := by rw [hzero, zero_add]
  simpa only [CertifiedATS.trueVector, zero_div, zero_mul, zero_smul, add_zero] using heq.symm

noncomputable def largeLambda (mu sigma rho G : ℝ) : ℝ :=
  1 + 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho)

theorem zero_curvature_large_lambda_small_gradient
    (g : E → ℝ) (mu lam sigma rho G : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1)
    (hrho : 0 < rho) (hG0 : 0 ≤ G) (hlarge : largeLambda mu sigma rho G ≤ lam)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) 0 d + d‖ ≤ sigma * ‖d‖) :
    ‖gradient g (z + d)‖ ≤ rho / 2 := by
  have hsize := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) 0 lam mu
    (by norm_num) hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hRadius : ‖actualStep g 0 z lam‖ ≤ G / mu := by
    have hn : 0 ≤ lam⁻¹ * ‖actualStep g 0 z lam‖ := by positivity
    apply (le_div_iff₀ hmu).mpr
    change (mu + lam⁻¹) * ‖actualStep g 0 z lam‖ ≤ _ at hsize
    nlinarith only [hsize, hG, hn]
  have hbr := (actual_approximate_norm_bracket g mu 0 lam sigma hmu (by norm_num) hlam hC2 hsc z d hATS).1
  have hbr0 : (1 - sigma) * ‖d‖ ≤ ‖actualStep g 0 z lam‖ := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hbr]
  have hmuDiv : mu * (G / mu) = G := by field_simp
  have hd : ‖d‖ ≤ G / (mu * (1 - sigma)) := by
    have hh := mul_le_mul_of_nonneg_left (hbr0.trans hRadius) hmu.le
    rw [hmuDiv] at hh
    apply (le_div_iff₀ (by positivity : 0 < mu * (1 - sigma))).mpr
    nlinarith only [hh]
  have hgradATS : ‖lam • gradient g (z + d) + d‖ ≤ sigma * ‖d‖ := by
    rwa [zero_hessian_lipschitz_exact_taylor g hC2 hH0 z d] at hATS
  have ht := norm_sub_le (lam • gradient g (z + d) + d) d
  have heq : (lam • gradient g (z + d) + d) - d = lam • gradient g (z + d) := by abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
  have hgrad : ‖gradient g (z + d)‖ ≤ (1 + sigma) * (G / (mu * (1 - sigma))) / lam := by
    apply (le_div_iff₀ hlam).mpr
    have hm := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 1 + sigma)
    nlinarith only [ht, hgradATS, hm]
  have hden : 0 < mu * (1 - sigma) * rho := by positivity
  have hl : 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho) ≤ lam := by
    change 1 + _ ≤ lam at hlarge
    linarith only [hlarge]
  have hmul := (div_le_iff₀ hden).mp hl
  have hfinal : (1 + sigma) * (G / (mu * (1 - sigma))) / lam ≤ rho / 2 := by
    have heq' : (1 + sigma) * (G / (mu * (1 - sigma))) / lam =
        ((1 + sigma) * G) / (mu * (1 - sigma) * lam) := by field_simp <;> ring
    rw [heq']
    apply (div_le_iff₀ (by positivity : 0 < mu * (1 - sigma) * lam)).mpr
    nlinarith only [hmul]
  exact hgrad.trans hfinal

theorem zero_curvature_trial_stops
    (g : E → ℝ) (mu Lg lam sigma rho G deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hlam : 0 < lam) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hrho : 0 < rho) (hG0 : 0 ≤ G) (hlarge : largeLambda mu sigma rho G ≤ lam)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (z : E) (hG : ‖gradient g z‖ ≤ G) :
    ∃ w : E, OriginalBetaATSTrial.trial getter 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (OriginalBetaATSTrial.execute getter
        (OriginalBetaATSTrial.trialProgram 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z)).2 ≤ 2 := by
  have ht := OriginalBetaATSTrial.trial_uniform_spec g mu Lg 0 lam lam lam sigma rho deltaY
    hmu hLg (by norm_num) hlam le_rfl le_rfl hsigma0 hrho hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter z
  cases hout : OriginalBetaATSTrial.trial getter 0 lam (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z with
  | stop w =>
    rw [hout] at ht
    exact ⟨w, rfl, ht, OriginalBetaATSTrial.trial_getter_calls getter 0 lam _ rho deltaY z⟩
  | step d aY =>
    rw [hout] at ht
    have hg := zero_curvature_large_lambda_small_gradient g mu lam sigma rho G hmu hlam hsigma0.le hsigma1
      hrho hG0 hlarge hC2 hsc hH0 z d hG ht.1
    exact False.elim (not_lt_of_ge hg ht.2.2)


noncomputable def observedBound (getter : E × ℝ → Answer E) (Lg : ℝ) (x y : E) : ℝ :=
  ‖(getter (y, 1)).grad‖ + 1 + Lg * ‖x - y‖

noncomputable def chosenBeta (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho : ℝ) (x y : E) : ℝ :=
  betaHigh A (largeLambda mu sigma rho (observedBound getter Lg x y))

theorem zero_curvature_observable_coupled_stop
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    let b := chosenBeta getter mu Lg A sigma rho x y
    let lam := OriginalCoupledBetaAlgebra.lambda A b
    let z := OriginalCoupledBetaAlgebra.center x y b
    0 < b ∧ b < 1 ∧ 0 < lam ∧
    (∃ w : E, OriginalBetaATSTrial.trial getter 0 lam
      (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (OriginalBetaATSTrial.execute getter
        (OriginalBetaATSTrial.trialProgram 0 lam
          (uniformTolerance mu Lg 0 lam lam sigma rho) rho deltaY z)).2 ≤ 2) := by
  let G := observedBound getter Lg x y
  have hG0 : 0 ≤ G := by dsimp [G, observedBound]; positivity
  have hG : gradientBound g Lg x y ≤ G :=
    gradient_upper_from_certificate g Lg x y _ 1 (hgetter y 1 (by norm_num)).1
  have hH0' : 0 ≤ largeLambda mu sigma rho G := by dsimp [largeLambda]; positivity
  have hb := betaHigh_properties A (largeLambda mu sigma rho G) hA hH0'
  have hb0 : 0 < betaHigh A (largeLambda mu sigma rho G) := by linarith only [hb.2.2.1]
  have hb1 := hb.2.2.2.1
  have hlam := (OriginalCoupledBetaAlgebra.coupled_weights A _ hA hb0 hb1).1
  refine ⟨hb0, hb1, hlam, ?_⟩
  apply zero_curvature_trial_stops g mu Lg _ sigma rho G deltaY hmu hLg hlam
    hsigma0 hsigma1 hrho hG0 hb.2.2.2.2 hdeltaY hdeltaYsmall hC2 hsc hlip hH0 getter hgetter
  exact (center_gradient_bound g Lg hLg hlip x y _ hb0.le hb1.le).trans hG

end OriginalZeroCurvatureSearch


namespace OriginalCoupledSearchComplete
open _root_.OriginalCoupledSearchComplete

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def effectiveSettings (c : Settings) : Settings :=
  if 0 < c.A then c else proxySettings c

noncomputable def effectiveY (c : Settings) (x y : E) : E := if 0 < c.A then y else x

noncomputable def coupledProgram (c : Settings) (deltaY : ℝ) (x y : E) :=
  positiveProgram (effectiveSettings c) deltaY x (effectiveY c x y)

def ActualValid (g : E → ℝ) (c : Settings) (getter : E × ℝ → Answer E)
    (deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  if 0 < c.A then ValidResult g c (observedGradientBound getter c x y) deltaY x y value
  else FixedValidResult g c deltaY x value

theorem effective_legal (c : Settings) (hc : CommonLegal c) : Legal (effectiveSettings c) := by
  by_cases hA : 0 < c.A
  · simpa only [effectiveSettings, if_pos hA] using positive_legal c hc hA
  · simpa only [effectiveSettings, if_neg hA] using proxy_legal c hc

theorem effective_fields (c : Settings) :
    (effectiveSettings c).mu = c.mu ∧ (effectiveSettings c).Lg = c.Lg ∧
    (effectiveSettings c).M = c.M ∧ (effectiveSettings c).rho = c.rho := by
  by_cases hA : 0 < c.A <;> simp [effectiveSettings, hA, proxySettings]

theorem coupled_search_from_certified_getters
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    let e := effectiveSettings c
    let y' := effectiveY c x y
    let G := observedGradientBound getter e x y'
    ∃ value : Result E,
      (execute getter (coupledProgram c deltaY x y)).1 = .found value ∧
      ActualValid g c getter deltaY x y value ∧
      (0 < c.A ∨ c.A = 0) ∧
      (FangqingHysteresis.execute (classifiedTrial getter e G deltaY x y')
        (searchProgram e G x y')).2 ≤ fuel e G x y' + 2 ∧
      ((fuel e G x y' : ℕ) : ℝ) + 2 ≤
        3 + Real.logb 2 (max 1 ((modulus e G x y' * (upper e - lower e G)) /
          ((thresholdHigh e - thresholdLow e) / 2))) ∧
      (execute getter (coupledProgram c deltaY x y)).2 ≤ 2 * fuel e G x y' + 5 ∧
      0 < precisionFloor e G deltaY ∧
      (∀ q ∈ trace getter (coupledProgram c deltaY x y), precisionFloor e G deltaY ≤ q.2) ∧
      baseCost getter cost (coupledProgram c deltaY x y) ≤
        logarithmicAtomicBound K (precisionFloor e G deltaY) * (2 * fuel e G x y' + 5) := by
  let e := effectiveSettings c
  let y' := effectiveY c x y
  let G := observedGradientBound getter e x y'
  have he := effective_legal c hc
  have hf := effective_fields c
  have hde : deltaY ≤ e.rho / 8 := by simpa only [e, hf.2.2.2] using hdeltaYsmall
  have hsce : StrongConvexOn (Set.univ : Set E) e.mu g := by simpa only [e, hf.1] using hsc
  have hlipe : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ e.Lg * ‖z - w‖ := by
    simpa only [e, hf.2.1] using hlip
  have hHlipe : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ e.M * ‖z - w‖ := by
    simpa only [e, hf.2.2.1] using hHlip
  obtain ⟨value, hrun, hvalid, hcount⟩ := positiveProgram_success_and_getter_calls g e he deltaY
    hdeltaY hde hC2 hsce hlipe hHlipe getter hgetter x y'
  have hbound := observed_bound_is_valid g e he getter hgetter x y'
  obtain ⟨_, _, _, hATSCount⟩ := positive_search_success_and_calls g e he G deltaY hbound.1
    hdeltaY hde hC2 hsce hlipe hHlipe getter hgetter x y' hbound.2
  have hfloor := precisionFloor_positive e he G deltaY hbound.1 hdeltaY
  have hv : ActualValid g c getter deltaY x y value := by
    by_cases hpos : 0 < c.A
    · simpa only [ActualValid, if_pos hpos, e, effectiveSettings, y', effectiveY] using hvalid
    · apply (if_neg hpos).mpr
      apply proxy_result_is_actual_first_step g c deltaY G x value
      simpa only [G, e, effectiveSettings, y', effectiveY, if_neg hpos] using hvalid
  have hcases : 0 < c.A ∨ c.A = 0 := by
    by_cases hp : 0 < c.A
    · exact Or.inl hp
    · exact Or.inr (le_antisymm (le_of_not_gt hp) hA)
  exact ⟨value, hrun, hv, hcases, hATSCount, positive_search_log_bound e G x y', hcount,
    hfloor, positiveProgram_request_precision_floor getter e deltaY x y',
    positiveProgram_logarithmic_base_cost getter cost e deltaY x y' K hK hfloor hatomic hcount⟩

end OriginalCoupledSearchComplete


namespace OriginalZeroCurvatureSearch
open _root_.OriginalZeroCurvatureSearch
open OriginalBetaATSTrial
open OriginalCoupledBetaAlgebra
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def initialBeta (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  OriginalBetaSearchEndpoints.betaHigh A (largeLambda mu sigma rho (‖a.grad‖ + 1 + Lg * ‖x - y‖))
noncomputable def initialLambda (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  lambda A (initialBeta mu Lg A sigma rho x y a)
noncomputable def initialCenter (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : E :=
  center x y (initialBeta mu Lg A sigma rho x y a)
noncomputable def initialTolerance (mu Lg A sigma rho : ℝ) (x y : E) (a : Answer E) : ℝ :=
  OriginalBetaATSUniform.uniformTolerance mu Lg 0
    (initialLambda mu Lg A sigma rho x y a) (initialLambda mu Lg A sigma rho x y a) sigma rho
noncomputable def zeroProgram (mu Lg A sigma rho deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (TrialResult E) :=
  .ask (y, 1) (fun a => trialProgram 0 (initialLambda mu Lg A sigma rho x y a)
    (initialTolerance mu Lg A sigma rho x y a) rho deltaY (initialCenter mu Lg A sigma rho x y a))
noncomputable def zeroPrecisionFloor (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho deltaY : ℝ) (x y : E) : ℝ :=
  min 1 (min (initialTolerance mu Lg A sigma rho x y (getter (y, 1))) deltaY)

theorem zeroProgram_trace_floor (getter : E × ℝ → Answer E)
    (mu Lg A sigma rho deltaY : ℝ) (x y : E) :
    ∀ q ∈ trace getter (zeroProgram mu Lg A sigma rho deltaY x y),
      zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ≤ q.2 := by
  intro q hq
  simp only [zeroProgram, trace, List.mem_cons] at hq
  rcases hq with rfl | htail
  · exact min_le_left _ _
  · apply allRequests_trace getter
      (fun q : E × ℝ => zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ≤ q.2)
      _ _ q htail
    apply allRequests_mono _ _ _ _ (trialProgram_precision_set 0 _ _ rho deltaY _)
    intro r hr
    rcases hr with hr | hr
    · rw [hr]
      exact (min_le_right _ _).trans (min_le_left _ _)
    · rw [hr]
      exact (min_le_right _ _).trans (min_le_right _ _)

theorem zeroProgram_small_gradient_and_logarithmic_cost
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ w : E, (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).1 = .stop w ∧
      ‖gradient g w‖ ≤ rho ∧
      (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).2 ≤ 3 ∧
      0 < zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y ∧
      baseCost getter cost (zeroProgram mu Lg A sigma rho deltaY x y) ≤
        3 * logarithmicAtomicBound K (zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y) := by
  obtain ⟨hb, hb1, hlam, w, hw, hgrad, hcalls⟩ := zero_curvature_observable_coupled_stop g mu Lg A sigma rho deltaY
    hmu hLg hA hsigma0 hsigma1 hrho hdeltaY hdeltaYsmall hC2 hsc hlip hH0 getter hgetter x y
  have hrun : (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).1 = .stop w := hw
  have hcount : (execute getter (zeroProgram mu Lg A sigma rho deltaY x y)).2 ≤ 3 := by
    change (execute getter (trialProgram 0 _ _ rho deltaY _)).2 + 1 ≤ 3
    exact Nat.add_le_add_right hcalls 1
  have hlam' : 0 < initialLambda mu Lg A sigma rho x y (getter (y, 1)) := hlam
  have ht : 0 < initialTolerance mu Lg A sigma rho x y (getter (y, 1)) := by
    exact OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 _ _ sigma rho
      hmu hLg (by norm_num) hlam' hlam' hsigma0 hrho
  have hfloor : 0 < zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y :=
    lt_min (by norm_num) (lt_min ht hdeltaY)
  have hcost := logarithmic_baseCost_bound getter cost Prod.snd
    (zeroProgram mu Lg A sigma rho deltaY x y) K _ hK hfloor
    (zeroProgram_trace_floor getter mu Lg A sigma rho deltaY x y) hatomic
  refine ⟨w, hrun, hgrad, hcount, hfloor, hcost.trans ?_⟩
  calc
    _ ≤ logarithmicAtomicBound K (zeroPrecisionFloor getter mu Lg A sigma rho deltaY x y) * 3 :=
      Nat.mul_le_mul_left _ hcount
    _ = _ := Nat.mul_comm _ _

end OriginalZeroCurvatureSearch


namespace OriginalCoupledSearchComplete
open _root_.OriginalCoupledSearchComplete
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open OriginalZeroCurvatureSearch
open FangqingGetterComposition

structure NonnegativeLegal (c : Settings) : Prop where
  mu_pos : 0 < c.mu
  Lg_nonneg : 0 ≤ c.Lg
  M_nonneg : 0 ≤ c.M
  sigma_pos : 0 < c.sigma
  sigma_lt_one : c.sigma < 1
  low_pos : 0 < c.sigmaLow
  low_lt_up : c.sigmaLow < c.sigmaUp
  gap : c.sigmaLow * (1 + c.sigma) < c.sigmaUp * (1 - c.sigma)
  rho_pos : 0 < c.rho

theorem positive_common (c : Settings) (hc : NonnegativeLegal c) (hM : 0 < c.M) : CommonLegal c :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hM, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def zeroAsOutcome : TrialResult E → FangqingHysteresis.Outcome (Result E)
  | .stop w => .found (.stop w)
  | .step _ _ => .bracket 0 1

noncomputable def allCurvatureProgram (c : Settings) (deltaY : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  if 0 < c.M then coupledProgram c deltaY x y
  else FangqingGetterComposition.map zeroAsOutcome
    (zeroProgram c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY x (effectiveY c x y))

noncomputable def allPrecisionFloor (getter : E × ℝ → Answer E)
    (c : Settings) (deltaY : ℝ) (x y : E) : ℝ :=
  if 0 < c.M then precisionFloor (effectiveSettings c)
    (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) deltaY
  else zeroPrecisionFloor getter c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY x (effectiveY c x y)

noncomputable def allGetterBudget (getter : E × ℝ → Answer E)
    (c : Settings) (x y : E) : ℕ :=
  if 0 < c.M then 2 * fuel (effectiveSettings c)
    (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) x (effectiveY c x y) + 5
  else 3

noncomputable def allATSCalls (getter : E × ℝ → Answer E)
    (c : Settings) (deltaY : ℝ) (x y : E) : ℕ :=
  if 0 < c.M then (FangqingHysteresis.execute
    (classifiedTrial getter (effectiveSettings c)
      (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) deltaY x (effectiveY c x y))
    (searchProgram (effectiveSettings c)
      (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)) x (effectiveY c x y))).2
  else 1

noncomputable def allATSLogBound (getter : E × ℝ → Answer E)
    (c : Settings) (x y : E) : ℝ :=
  if 0 < c.M then 3 + Real.logb 2 (max 1
    ((modulus (effectiveSettings c) (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y))
      x (effectiveY c x y) * (upper (effectiveSettings c) -
        lower (effectiveSettings c) (observedGradientBound getter (effectiveSettings c) x (effectiveY c x y)))) /
      ((thresholdHigh (effectiveSettings c) - thresholdLow (effectiveSettings c)) / 2)))
  else 1

def AllValid (g : E → ℝ) (c : Settings) (getter : E × ℝ → Answer E)
    (deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  if 0 < c.M then ActualValid g c getter deltaY x y value
  else match value with
    | .stop w => ‖gradient g w‖ ≤ c.rho
    | .window _ _ _ => False

theorem baseCost_map_actual {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ)
    (f : R → S) (p : GetterProgram Q A R) :
    baseCost getter cost (FangqingGetterComposition.map f p) = baseCost getter cost p := by
  induction p with
  | pure r => rfl
  | ask q next ih =>
    change cost q + baseCost getter cost (FangqingGetterComposition.map f (next (getter q))) =
      cost q + baseCost getter cost (next (getter q))
    rw [ih]

theorem coupled_search_all_nonnegative_curvatures
    (g : E → ℝ) (c : Settings) (hc : NonnegativeLegal c) (hA : 0 ≤ c.A)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (allCurvatureProgram c deltaY x y)).1 = .found value ∧
      AllValid g c getter deltaY x y value ∧
      (allATSCalls getter c deltaY x y : ℝ) ≤ allATSLogBound getter c x y ∧
      (execute getter (allCurvatureProgram c deltaY x y)).2 ≤ allGetterBudget getter c x y ∧
      0 < allPrecisionFloor getter c deltaY x y ∧
      baseCost getter cost (allCurvatureProgram c deltaY x y) ≤
        logarithmicAtomicBound K (allPrecisionFloor getter c deltaY x y) * allGetterBudget getter c x y := by
  classical
  by_cases hM : 0 < c.M
  · obtain ⟨value, hrun, hvalid, _, hATS, hlog, hcount, hfloor, _, hcost⟩ :=
      coupled_search_from_certified_getters g c (positive_common c hc hM) hA deltaY hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter cost K hK hatomic x y
    have hreal := Nat.cast_le (α := ℝ).mpr hATS
    simp only [Nat.cast_add, Nat.cast_ofNat] at hreal
    have hb : (allATSCalls getter c deltaY x y : ℝ) ≤ allATSLogBound getter c x y := by
      simp only [allATSCalls, allATSLogBound, if_pos hM]
      exact hreal.trans hlog
    exact ⟨value, by simpa only [allCurvatureProgram, if_pos hM] using hrun,
      by simpa only [AllValid, if_pos hM] using hvalid, hb,
      by simpa only [allCurvatureProgram, allGetterBudget, if_pos hM] using hcount,
      by simpa only [allPrecisionFloor, if_pos hM] using hfloor,
      by simpa only [allCurvatureProgram, allPrecisionFloor, allGetterBudget, if_pos hM] using hcost⟩
  · have hM0 : c.M = 0 := le_antisymm (le_of_not_gt hM) hc.M_nonneg
    have hH0 : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
      simpa only [hM0] using hHlip
    have hAe : 0 < (effectiveSettings c).A := by
      by_cases hpos : 0 < c.A
      · simpa only [effectiveSettings, if_pos hpos] using hpos
      · simp only [effectiveSettings, if_neg hpos, proxySettings]; norm_num
    obtain ⟨w, hrun, hg, hcount, hfloor, hcost⟩ :=
      zeroProgram_small_gradient_and_logarithmic_cost g c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY
        hc.mu_pos hc.Lg_nonneg hAe hc.sigma_pos hc.sigma_lt_one hc.rho_pos hdeltaY hdeltaYsmall
        hC2 hsc hlip hH0 getter hgetter cost K hK hatomic x (effectiveY c x y)
    refine ⟨.stop w, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [allCurvatureProgram, if_neg hM, execute_map, hrun, zeroAsOutcome]
    · simpa only [AllValid, if_neg hM] using hg
    · simp only [allATSCalls, allATSLogBound, if_neg hM, Nat.cast_one, le_refl]
    · simpa only [allCurvatureProgram, allGetterBudget, if_neg hM, execute_map] using hcount
    · simpa only [allPrecisionFloor, if_neg hM] using hfloor
    · simpa only [allCurvatureProgram, allPrecisionFloor, allGetterBudget, if_neg hM,
        baseCost_map_actual, Nat.mul_comm] using hcost

end OriginalCoupledSearchComplete


namespace OriginalTrialQueryGeometry
open _root_.OriginalTrialQueryGeometry
open OriginalBetaATSTrial
open OriginalTaylorProxStability
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem observable_model_step_norm_bound
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam delta G : ℝ)
    (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z : E) (a : Answer E) (hgrad : ‖a.grad - gradient g z‖ ≤ delta)
    (hhess : ‖a.hess - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hdelta : delta ≤ mu / 4) (hG : ‖gradient g z‖ ≤ G) :
    ‖exactStep a.grad a.hess M lam‖ ≤ 2 * (G + delta) / mu := by
  have hcoer : ∀ d : E, mu / 2 * ‖d‖ ^ 2 ≤ inner ℝ (a.hess d) d := by
    intro d
    have hh := CertifiedATS.approximate_hessian_coercive g hC2 mu hsc z a.hess delta hhess hdelta d
    rw [CertifiedATS.sympart_same_quadratic] at hh
    have hn := sq_nonneg ‖d‖
    nlinarith only [hh, hn, hmu]
  have hsize := exactStep_size_bound a.grad a.hess M lam (mu / 2) hM hlam (by positivity) hcoer
  have ha : ‖a.grad‖ ≤ G + delta := by
    have ht := norm_le_norm_sub_add a.grad (gradient g z)
    linarith only [ht, hgrad, hG]
  have hn : 0 ≤ lam⁻¹ * ‖exactStep a.grad a.hess M lam‖ := by positivity
  apply (le_div_iff₀ hmu).mpr
  nlinarith only [hsize, ha, hn]

theorem trial_trace_query_points
    (getter : E × ℝ → Answer E) (M lam delta rho deltaY : ℝ) (z : E) :
    ∀ q ∈ trace getter (trialProgram M lam delta rho deltaY z),
      q.1 = z ∨ q.1 = z + exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam := by
  classical
  intro q hq
  by_cases hs : ‖(getter (z, delta)).grad‖ + delta ≤ rho
  · simp only [trialProgram, trace, hs, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hq
    exact Or.inl (congrArg Prod.fst hq)
  · let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
    by_cases hy : ‖(getter (z + d, deltaY)).grad‖ + deltaY ≤ rho
    · simp only [trialProgram, trace, hs, ↓reduceIte, d, hy, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq
      · exact Or.inl (congrArg Prod.fst hq)
      · exact Or.inr (congrArg Prod.fst hq)
    · simp only [trialProgram, trace, hs, ↓reduceIte, d, hy, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with hq | hq
      · exact Or.inl (congrArg Prod.fst hq)
      · exact Or.inr (congrArg Prod.fst hq)

theorem actual_trial_query_distance_bound
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam delta rho deltaY G Bz : ℝ)
    (hmu : 0 < mu) (hM : 0 ≤ M) (hlam : 0 < lam)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (getter : E × ℝ → Answer E) (z w : E)
    (hgrad : ‖(getter (z, delta)).grad - gradient g z‖ ≤ delta)
    (hhess : ‖(getter (z, delta)).hess - fderiv ℝ (gradient g) z‖ ≤ delta)
    (hdelta : delta ≤ mu / 4) (hG : ‖gradient g z‖ ≤ G) (hcenter : ‖z - w‖ ≤ Bz) :
    ∀ q ∈ trace getter (trialProgram M lam delta rho deltaY z),
      ‖q.1 - w‖ ≤ Bz + 2 * (G + delta) / mu := by
  let d := exactStep (getter (z, delta)).grad (getter (z, delta)).hess M lam
  have hd : ‖d‖ ≤ 2 * (G + delta) / mu :=
    observable_model_step_norm_bound g hC2 mu M lam delta G hmu hM hlam hsc z _ hgrad hhess hdelta hG
  have hb : 0 ≤ 2 * (G + delta) / mu := (norm_nonneg d).trans hd
  intro q hq
  rcases trial_trace_query_points getter M lam delta rho deltaY z q hq with heq | heq
  · rw [heq]
    exact hcenter.trans (le_add_of_nonneg_right hb)
  · rw [heq]
    have hsplit : z + d - w = (z - w) + d := by abel
    change ‖z + d - w‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hcenter hd)

end OriginalTrialQueryGeometry


namespace OriginalCoupledQueryGeometry
open _root_.OriginalCoupledQueryGeometry
open OriginalBetaATSTrial
open OriginalTaylorProxStability
open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalCoupledBetaSearch
open OriginalCoupledGetterProgram
open OriginalTrialQueryGeometry
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def AllAsks {Reply R : Type*} (P : ℝ → Prop) : FangqingHysteresis.Program Reply R → Prop
  | .pure _ => True
  | .ask b next => P b ∧ ∀ reply, AllAsks P (next reply)

theorem bisect_allAsks_interval {R : Type*} (n : ℕ) (L U l r : ℝ)
    (hL : L ≤ l) (hlr : l ≤ r) (hU : r ≤ U) :
    AllAsks (fun b => b ∈ Set.Icc L U) (FangqingHysteresis.bisect (R := R) n l r) := by
  induction n generalizing l r with
  | zero => exact True.intro
  | succ n ih =>
    change ((l + r) / 2 ∈ Set.Icc L U) ∧ _
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    intro reply
    cases reply with
    | accept v => exact True.intro
    | low => exact ih _ _ (by linarith) (by linarith) hU
    | high => exact ih _ _ hL (by linarith) (by linarith)

theorem search_allAsks_interval (c : Settings) (G : ℝ) (x y : E)
    (hLU : lower c G ≤ upper c) :
    AllAsks (fun b => b ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) (searchProgram c G x y) := by
  change (lower c G ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) ∧ _
  refine ⟨⟨le_rfl, hLU⟩, ?_⟩
  intro left
  cases left with
  | accept v => exact True.intro
  | low | high =>
    change (upper c ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c)) ∧ _
    refine ⟨⟨hLU, le_rfl⟩, ?_⟩
    intro right
    cases right with
    | accept v => exact True.intro
    | low | high => exact bisect_allAsks_interval _ _ _ _ _ le_rfl hLU le_rfl

theorem trace_bind_actual {Q A R S : Type*} (getter : Q → A)
    (p : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    trace getter (bind p next) = trace getter p ++ trace getter (next (execute getter p).1) := by
  induction p with
  | pure r => rfl
  | ask q cont ih => simp only [FangqingGetterComposition.bind, trace, execute, ih, List.cons_append]

theorem trace_map_actual {Q A R S : Type*} (getter : Q → A)
    (f : R → S) (p : GetterProgram Q A R) : trace getter (FangqingGetterComposition.map f p) = trace getter p := by
  simp only [FangqingGetterComposition.map, trace_bind_actual, trace, List.append_nil]

theorem actual_lower_trace_on_domain {Q A Reply R : Type*}
    (getter : Q → A) (trials : ℝ → GetterProgram Q A Reply)
    (domain : ℝ → Prop) (P : Q → Prop)
    (p : FangqingHysteresis.Program Reply R) (hp : AllAsks domain p)
    (htrials : ∀ b, domain b → ∀ q ∈ trace getter (trials b), P q) :
    ∀ q ∈ trace getter (FangqingGetterComposition.lower trials p), P q := by
  induction p with
  | pure v => simp only [FangqingGetterComposition.lower, trace, List.not_mem_nil, false_implies, implies_true]
  | ask b next ih =>
    intro q hq
    rw [FangqingGetterComposition.lower, trace_bind_actual, List.mem_append] at hq
    rcases hq with hq | hq
    · exact htrials b hp.1 q hq
    · exact ih (execute getter (trials b)).1 (hp.2 _) q hq

noncomputable def queryRadius (c : Settings) (G : ℝ) (x y : E) : ℝ :=
  ‖x - y‖ + 2 * (G + c.mu / 4) / c.mu

theorem positiveProgram_actual_query_ball
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (positiveProgram c deltaY x y),
      ‖q.1 - y‖ ≤ queryRadius c (observedGradientBound getter c x y) x y := by
  let G := observedGradientBound getter c x y
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  have hp := compact_properties c hc G hbound.1
  have ht := precisionFloor_positive c hc G 1 hbound.1 (by norm_num)
  have htol : 0 < tolerance c G :=
    ht.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : tolerance c G ≤ c.mu / 4 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hG0 : 0 ≤ G := hbound.1
  have hR : 0 ≤ queryRadius c G x y := by
    dsimp [queryRadius]
    have hmu := hc.mu_pos
    positivity
  intro q hq
  change q ∈ trace getter (.ask (y, 1) (fun a =>
    FangqingGetterComposition.lower (trials c (initialBound c x y a) deltaY x y)
      (searchProgram c (initialBound c x y a) x y))) at hq
  simp only [trace, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [sub_self, norm_zero] using hR
  · apply actual_lower_trace_on_domain getter (trials c G deltaY x y)
      (fun b => b ∈ Set.Icc (OriginalCoupledBetaSearch.lower c G) (upper c))
      (fun q : E × ℝ => ‖q.1 - y‖ ≤ queryRadius c G x y)
      (searchProgram c G x y)
      (search_allAsks_interval c G x y hp.2.2.2.2.2.2.1) _ q hq
    intro b hb r hr
    have hinterval := interval_lambda_bounds c hc G hbound.1 b hb
    have hcenter : ‖center x y b - y‖ ≤ ‖x - y‖ := by
      have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hinterval.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hinterval.2.1.le
    have hG : ‖gradient g (center x y b)‖ ≤ G :=
      (center_gradient_bound g c.Lg hc.Lg_nonneg hlip x y b hinterval.1.le hinterval.2.1.le).trans hbound.2
    have herrors := hgetter (center x y b) (tolerance c G) htol
    have htrace : r ∈ trace getter (trialProgram c.M (lambda c.A b) (tolerance c G)
        c.rho deltaY (center x y b)) := by
      simpa only [trials, mappedTaylorTrial, trace_map_actual] using hr
    have hh := actual_trial_query_distance_bound g hC2 c.mu c.M (lambda c.A b) (tolerance c G)
      c.rho deltaY G ‖x - y‖ hc.mu_pos hc.M_pos.le hinterval.2.2.1 hsc getter
      (center x y b) y herrors.1 herrors.2 hsmall hG hcenter r htrace
    have hfrac : 2 * (G + tolerance c G) / c.mu ≤ 2 * (G + c.mu / 4) / c.mu :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl hsmall) (by norm_num)) hc.mu_pos.le
    exact hh.trans (add_le_add le_rfl hfrac)

end OriginalCoupledQueryGeometry


namespace OriginalZeroQueryGeometry
open _root_.OriginalZeroQueryGeometry
open OriginalBetaATSTrial
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalCoupledBetaAlgebra
open OriginalZeroCurvatureSearch
open OriginalTrialQueryGeometry
open OriginalCoupledQueryGeometry
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem zeroProgram_actual_query_ball
    (g : E → ℝ) (mu Lg A sigma rho deltaY : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hA : 0 < A)
    (hsigma : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (zeroProgram mu Lg A sigma rho deltaY x y),
      ‖q.1 - y‖ ≤ ‖x - y‖ + 2 * (observedBound getter Lg x y + mu / 4) / mu := by
  let G := observedBound getter Lg x y
  let b := initialBeta mu Lg A sigma rho x y (getter (y, 1))
  let lam := initialLambda mu Lg A sigma rho x y (getter (y, 1))
  let delta := initialTolerance mu Lg A sigma rho x y (getter (y, 1))
  have hG0 : 0 ≤ G := by dsimp [G, observedBound]; positivity
  have hG : gradientBound g Lg x y ≤ G :=
    gradient_upper_from_certificate g Lg x y _ 1 (hgetter y 1 (by norm_num)).1
  have hH : 0 ≤ largeLambda mu sigma rho G := by dsimp [largeLambda]; positivity
  have hb := betaHigh_properties A (largeLambda mu sigma rho G) hA hH
  have hb0 : 0 < b := by change 0 < betaHigh A (largeLambda mu sigma rho G); linarith only [hb.2.2.1]
  have hb1 : b < 1 := hb.2.2.2.1
  have hlam : 0 < lam := (coupled_weights A b hA hb0 hb1).1
  have hd : 0 < delta := OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 lam lam sigma rho
    hmu hLg (by norm_num) hlam hlam hsigma hrho
  have hsmall : delta ≤ mu / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcenter : ‖center x y b - y‖ ≤ ‖x - y‖ := by
    have heq : center x y b - y = b • (x - y) := by dsimp [center]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hb0]
    exact mul_le_of_le_one_left (norm_nonneg _) hb1.le
  have hgrad : ‖gradient g (center x y b)‖ ≤ G :=
    (center_gradient_bound g Lg hLg hlip x y b hb0.le hb1.le).trans hG
  have herrors := hgetter (center x y b) delta hd
  have hR : 0 ≤ ‖x - y‖ + 2 * (G + mu / 4) / mu := by positivity
  intro q hq
  simp only [zeroProgram, trace, List.mem_cons] at hq
  rcases hq with rfl | hq
  · simpa only [sub_self, norm_zero] using hR
  · have hh := actual_trial_query_distance_bound g hC2 mu 0 lam delta rho deltaY G ‖x - y‖
      hmu (by norm_num) hlam hsc getter (center x y b) y herrors.1 herrors.2 hsmall hgrad hcenter q hq
    exact hh.trans (add_le_add le_rfl (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsmall) (by norm_num)) hmu.le))

end OriginalZeroQueryGeometry

namespace OriginalZeroQueryGeometry
open _root_.OriginalZeroQueryGeometry
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledSearchComplete
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open OriginalCoupledQueryGeometry
open FangqingGetterComposition
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def allQueryRadius (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  let y' := effectiveY c x y
  ‖x - y'‖ + 2 * (observedGradientBound getter (effectiveSettings c) x y' + c.mu / 4) / c.mu

theorem allProgram_actual_query_ball
    (g : E → ℝ) (c : Settings) (hc : NonnegativeLegal c) (deltaY : ℝ)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) :
    ∀ q ∈ trace getter (allCurvatureProgram c deltaY x y),
      ‖q.1 - effectiveY c x y‖ ≤ allQueryRadius getter c x y := by
  classical
  have hf := effective_fields c
  by_cases hM : 0 < c.M
  · have he := effective_legal c (positive_common c hc hM)
    have hsce : StrongConvexOn (Set.univ : Set E) (effectiveSettings c).mu g := by
      simpa only [hf.1] using hsc
    have hlipe : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ (effectiveSettings c).Lg * ‖z - w‖ := by
      simpa only [hf.2.1] using hlip
    have hh := positiveProgram_actual_query_ball g (effectiveSettings c) he deltaY hC2 hsce hlipe getter hgetter
      x (effectiveY c x y)
    simpa only [allCurvatureProgram, if_pos hM, coupledProgram, queryRadius, allQueryRadius, hf.1] using hh
  · have hAe : 0 < (effectiveSettings c).A := by
      by_cases hpos : 0 < c.A
      · simpa only [effectiveSettings, if_pos hpos] using hpos
      · simp only [effectiveSettings, if_neg hpos, proxySettings]; norm_num
    have hh := zeroProgram_actual_query_ball g c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY
      hc.mu_pos hc.Lg_nonneg hAe hc.sigma_pos hc.sigma_lt_one hc.rho_pos hC2 hsc hlip getter hgetter
      x (effectiveY c x y)
    simpa only [allCurvatureProgram, if_neg hM, trace_map_actual, allQueryRadius,
      OriginalZeroCurvatureSearch.observedBound, observedGradientBound, hf.2.1] using hh

end OriginalZeroQueryGeometry


namespace OriginalDualGetterImplementation
open _root_.OriginalDualGetterImplementation
open OriginalSaddleImplicit
open OriginalDualCurvature
open OriginalDualResidualQueryBound
open OriginalBetaATSTrial
open FangqingGetterComposition

noncomputable def liftQuery {Q A R : Type*} : OriginalDualOracleProgram.QueryProgram Q A R → GetterProgram Q A R
  | .pure r => .pure r
  | .ask q next => .ask q (fun a => liftQuery (next a))

theorem execute_liftQuery {Q A R : Type*} (oracle : Q → A)
    (p : OriginalDualOracleProgram.QueryProgram Q A R) :
    OriginalBetaATSTrial.execute oracle (liftQuery p) = OriginalDualOracleProgram.execute oracle p := by
  induction p with
  | pure r => rfl
  | ask q next ih => simp only [liftQuery, OriginalBetaATSTrial.execute, OriginalDualOracleProgram.execute, ih]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def accuracyRadius (L rho eta : ℝ) : ℝ := min 1 (eta / (1 + 3 * L + 4 * rho))

noncomputable def oracleProgram (L rho : ℝ) (x u0 : E) (q : F × ℝ) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Answer F) :=
  FangqingGetterComposition.map
    (fun s : OriginalDualOracleProgram.QueryState E F =>
      ⟨OriginalDualOracleProgram.gradientOutput s, OriginalDualOracleProgram.hessianOutput L s⟩)
    (liftQuery (OriginalDualOracleProgram.simulator L x q.1 u0 (accuracyRadius L rho q.2)))

noncomputable def actualGetter (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) : F × ℝ → Answer F :=
  implementedGetter (OriginalDualOracleProgram.actualOracle J) (oracleProgram L rho x u0)
noncomputable def actualCost (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) : F × ℝ → ℕ :=
  implementedCost (OriginalDualOracleProgram.actualOracle J) (oracleProgram L rho x u0)

theorem actual_getter_accuracy
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (x u0 : E) (y : F) (eta : ℝ) (heta : 0 < eta) :
    ‖(actualGetter J L rho x u0 (y, eta)).grad - gradient (psi J L x) y‖ ≤ eta ∧
    ‖(actualGetter J L rho x u0 (y, eta)).hess - fderiv ℝ (gradient (psi J L x)) y‖ ≤ eta := by
  have hh := OriginalDualOracleProgram.arbitrary_accuracy_simulation J L rho hL hrho hC2 hLip hHess x u0 y eta heta
  simpa only [actualGetter, implementedGetter, oracleProgram, execute_map, execute_liftQuery,
    accuracyRadius] using And.intro hh.2.2.1 hh.2.2.2.1

theorem actual_cost_is_original_bundled_queries
    (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E) (q : F × ℝ) :
    actualCost J L rho x u0 q =
      (OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalDualOracleProgram.simulator L x q.1 u0 (accuracyRadius L rho q.2))).2 := by
  simp only [actualCost, implementedCost, oracleProgram, execute_map, execute_liftQuery]

theorem accuracyRadius_positive (L rho eta : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho) (heta : 0 < eta) :
    0 < accuracyRadius L rho eta := by unfold accuracyRadius; positivity

theorem accuracyRadius_mono (L rho floor eta : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho) (hfloor : floor ≤ eta) :
    accuracyRadius L rho floor ≤ accuracyRadius L rho eta := by
  exact min_le_min le_rfl (div_le_div_of_nonneg_right hfloor (by positivity))

noncomputable def queryBallBudget (J : Joint E F → ℝ) (L rho : ℝ) (x u0 : E)
    (y0 : F) (B floor : ℝ) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho floor))

theorem actual_cost_on_query_ball_with_precision_floor
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x u0 : E) (y y0 : F) (B floor eta : ℝ)
    (hfloor : 0 < floor) (hprecision : floor ≤ eta) (hball : ‖y - y0‖ ≤ B) :
    actualCost J L rho x u0 (y, eta) ≤ queryBallBudget J L rho x u0 y0 B floor := by
  have hf := accuracyRadius_positive L rho floor hL hrho hfloor
  have he := accuracyRadius_positive L rho eta hL hrho (hfloor.trans_le hprecision)
  have hb : 0 ≤ B := (norm_nonneg _).trans hball
  have hobs : 0 ≤ observedRadius J L x u0 y0 := by unfold observedRadius; positivity
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x u0 y y0 B
    (accuracyRadius L rho eta) he hball
  rw [← actual_cost_is_original_bundled_queries J L rho x u0 (y, eta)] at hc
  have heFloor := accuracyRadius_mono L rho floor eta hL hrho hprecision
  have hfrac := div_le_div_of_nonneg_left (show 0 ≤ 3 * (observedRadius J L x u0 y0 + B) by positivity)
    hf heFloor
  have hlog : Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho eta) ≤
      Real.log (1 + 3 * (observedRadius J L x u0 y0 + B) / accuracyRadius L rho floor) :=
    Real.log_le_log (by positivity) (add_le_add le_rfl hfrac)
  apply (Nat.cast_le (α := ℝ)).mp
  exact (hc.trans (by linarith only [hlog])).trans (Nat.le_ceil _)

end OriginalDualGetterImplementation


namespace OriginalActualDualCoupledSearch
open _root_.OriginalActualDualCoupledSearch
open OriginalSaddleImplicit
open OriginalDualCurvature
open OriginalDualGetterImplementation
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledSearchComplete
open OriginalZeroQueryGeometry
open OriginalCoupledQueryGeometry
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def actualOriginalProgram (L rho : ℝ) (proxCenter uInit : E)
    (c : Settings) (deltaY : ℝ) (X Y : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F))
      (FangqingHysteresis.Outcome (Result F)) :=
  primitiveLower (oracleProgram L rho proxCenter uInit) (allCurvatureProgram c deltaY X Y)

noncomputable def originalQueryBudget (J : Joint E F → ℝ) (L rho : ℝ) (proxCenter uInit : E)
    (c : Settings) (deltaY : ℝ) (X Y : F) : ℕ :=
  let getter := actualGetter J L rho proxCenter uInit
  queryBallBudget J L rho proxCenter uInit (effectiveY c X Y) (allQueryRadius getter c X Y)
    (allPrecisionFloor getter c deltaY X Y) * allGetterBudget getter c X Y

theorem coupled_search_with_actual_original_oracle
    (J : Joint E F → ℝ) (L mu rho : ℝ) (hL : 0 < L) (hmu : 0 < mu) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u, y))))
    (proxCenter uInit : E) (c : Settings) (hc : NonnegativeLegal c) (hA : 0 ≤ c.A)
    (hmuField : c.mu = mu) (hLgField : c.Lg = 2 * L) (hMField : c.M = (4 * Real.sqrt 2) * rho)
    (deltaY : ℝ) (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (X Y : F) :
    let getter := actualGetter J L rho proxCenter uInit
    ∃ value : Result F,
      (OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
        (actualOriginalProgram L rho proxCenter uInit c deltaY X Y)).1 = .found value ∧
      AllValid (psi J L proxCenter) c getter deltaY X Y value ∧
      (allATSCalls getter c deltaY X Y : ℝ) ≤ allATSLogBound getter c X Y ∧
      0 < allPrecisionFloor getter c deltaY X Y ∧
      (OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
        (actualOriginalProgram L rho proxCenter uInit c deltaY X Y)).2 ≤
          originalQueryBudget J L rho proxCenter uInit c deltaY X Y := by
  let getter := actualGetter J L rho proxCenter uInit
  let p := allCurvatureProgram c deltaY X Y
  let floor := allPrecisionFloor getter c deltaY X Y
  let B := allQueryRadius getter c X Y
  let budget := queryBallBudget J L rho proxCenter uInit (effectiveY c X Y) B floor
  have hd := dual_curvature_from_standing_joint J L mu rho hL hmu hrho hC2 hLip hHess hconcave proxCenter
  have hgsc : StrongConvexOn (Set.univ : Set F) c.mu (psi J L proxCenter) := by
    simpa only [hmuField] using hd.2.2.2.2.2.1
  have hglip : ∀ z w : F, ‖gradient (psi J L proxCenter) z - gradient (psi J L proxCenter) w‖ ≤ c.Lg * ‖z - w‖ := by
    simpa only [hLgField] using hd.2.2.2.2.2.2
  have hgHess : ∀ z w : F,
      ‖fderiv ℝ (gradient (psi J L proxCenter)) z - fderiv ℝ (gradient (psi J L proxCenter)) w‖ ≤ c.M * ‖z - w‖ := by
    simpa only [hMField] using hd.2.2.2.2.1
  have hgetter : ∀ z : F, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient (psi J L proxCenter) z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient (psi J L proxCenter)) z‖ ≤ eta :=
    actual_getter_accuracy J L rho hL hrho hC2 hLip hHess proxCenter uInit
  obtain ⟨value, hrun, hvalid, hATS, hcount, hfloor, _⟩ :=
    coupled_search_all_nonnegative_curvatures (psi J L proxCenter) c hc hA deltaY hdeltaY hdeltaYsmall
      hd.1 hgsc hglip hgHess getter hgetter (fun _ => 0) 0 (by norm_num)
      (fun _ _ => Nat.zero_le _) X Y
  have hpoints := allProgram_actual_query_ball (psi J L proxCenter) c hc deltaY hd.1 hgsc hglip getter hgetter X Y
  have hprecisions : ∀ q ∈ trace getter p, floor ≤ q.2 := by
    by_cases hM : 0 < c.M
    · simpa only [p, floor, allCurvatureProgram, if_pos hM, coupledProgram, allPrecisionFloor] using
        OriginalCoupledGetterProgram.positiveProgram_request_precision_floor getter (effectiveSettings c) deltaY X (effectiveY c X Y)
    · simpa only [p, floor, allCurvatureProgram, if_neg hM, trace_map_actual, allPrecisionFloor] using
        OriginalZeroCurvatureSearch.zeroProgram_trace_floor getter c.mu c.Lg (effectiveSettings c).A c.sigma c.rho deltaY X (effectiveY c X Y)
  have hcost : baseCost getter (actualCost J L rho proxCenter uInit) p ≤ budget * (execute getter p).2 := by
    apply baseCost_le_mul_count
    intro q hq
    exact actual_cost_on_query_ball_with_precision_floor J L rho hL hrho hLip proxCenter uInit q.1
      (effectiveY c X Y) B floor q.2 hfloor (hprecisions q hq) (hpoints q hq)
  have hbase := primitiveLower_execution (OriginalDualOracleProgram.actualOracle J)
    (oracleProgram L rho proxCenter uInit) p
  have hbase' : execute (OriginalDualOracleProgram.actualOracle J)
      (actualOriginalProgram L rho proxCenter uInit c deltaY X Y) =
      ((execute getter p).1, baseCost getter (actualCost J L rho proxCenter uInit) p) := hbase
  refine ⟨value, ?_, hvalid, hATS, hfloor, ?_⟩
  · rw [hbase']
    exact hrun
  · rw [hbase']
    exact hcost.trans (Nat.mul_le_mul_left _ hcount)

end OriginalActualDualCoupledSearch


namespace OriginalDualGetterResourceComposition
open _root_.OriginalDualGetterResourceComposition
open OriginalSaddleImplicit
open OriginalDualGetterImplementation
open OriginalBetaATSTrial
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem actual_original_queries_from_realized_geometry {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x uInit : E) (y0 : F) (B floor : ℝ) (hfloor : 0 < floor)
    (p : GetterProgram (F × ℝ) (Answer F) R)
    (hpoint : ∀ q ∈ trace (actualGetter J L rho x uInit) p, ‖q.1 - y0‖ ≤ B)
    (hprecision : ∀ q ∈ trace (actualGetter J L rho x uInit) p, floor ≤ q.2) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).2 ≤
      queryBallBudget J L rho x uInit y0 B floor * (execute (actualGetter J L rho x uInit) p).2 := by
  rw [primitiveLower_execution]
  apply baseCost_le_mul_count
  intro q hq
  exact actual_cost_on_query_ball_with_precision_floor J L rho hL hrho hLip x uInit q.1 y0
    B floor q.2 hfloor (hprecision q hq) (hpoint q hq)

theorem actual_original_queries_from_checked_getter_budget {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x uInit : E) (y0 : F) (B floor : ℝ) (hfloor : 0 < floor)
    (p : GetterProgram (F × ℝ) (Answer F) R) (N : ℕ)
    (hpoint : ∀ q ∈ trace (actualGetter J L rho x uInit) p, ‖q.1 - y0‖ ≤ B)
    (hprecision : ∀ q ∈ trace (actualGetter J L rho x uInit) p, floor ≤ q.2)
    (hcount : (execute (actualGetter J L rho x uInit) p).2 ≤ N) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).2 ≤
      queryBallBudget J L rho x uInit y0 B floor * N :=
  (actual_original_queries_from_realized_geometry J L rho hL hrho hLip x uInit y0 B floor hfloor p
    hpoint hprecision).trans (Nat.mul_le_mul_left _ hcount)

theorem actual_original_program_result {R : Type*}
    (J : Joint E F → ℝ) (L rho : ℝ) (x uInit : E)
    (p : GetterProgram (F × ℝ) (Answer F) R) :
    (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L rho x uInit) p)).1 =
      (execute (actualGetter J L rho x uInit) p).1 := by
  rw [primitiveLower_execution]
  rfl

end OriginalDualGetterResourceComposition


namespace OriginalDualMinimizer
open _root_.OriginalDualMinimizer

open OriginalSaddleImplicit OriginalPrimalElimination OriginalDualCurvature
open OriginalSaddleTransfer

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem primal_at_actual_dual_saddle
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) :
    primal J L x (vStar (JointSliceRegularity.curry J) L x) =
      uStar (JointSliceRegularity.curry J) L x := by
  let f := JointSliceRegularity.curry J
  have hdiffX := JointSliceRegularity.differentiable_x_slice J hJ
  have hdiffY := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx : ∀ y : F, ∀ u u' : E,
      ‖gradient (fun t => f t y) u - gradient (fun t => f t y) u'‖ ≤ L * ‖u - u'‖ :=
    fun y u u' => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u u' y
  have hxy : ∀ u : E, ∀ y y' : F,
      ‖gradient (fun t => f t y) u - gradient (fun t => f t y') u‖ ≤ L * ‖y - y'‖ :=
    fun u y y' => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y y'
  apply ((primal_is_unique_minimizer J L hL hJ hLip x (vStar f L x)).2 (uStar f L x) ?_).symm
  intro u
  have hh := OriginalSaddleStability.fixed_dual_quadratic_growth f L mu hL hmu
    hdiffX hdiffY hsc hxx hxy x u
  change f (uStar f L x) (vStar f L x) + L * ‖uStar f L x - x‖ ^ 2 +
      L / 2 * ‖u - uStar f L x‖ ^ 2 ≤ f u (vStar f L x) + L * ‖u - x‖ ^ 2 at hh
  have hn : 0 ≤ L / 2 * ‖u - uStar f L x‖ ^ 2 := by positivity
  linarith only [hh, hn]

theorem actual_dual_saddle_minimizes
    (J : Joint E F → ℝ) (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : Differentiable ℝ J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) :
    ∀ y : F, psi J L x (vStar (JointSliceRegularity.curry J) L x) ≤ psi J L x y := by
  intro y
  let f := JointSliceRegularity.curry J
  let u := uStar f L x
  let v := vStar f L x
  have hprimal := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hmin := (primal_is_unique_minimizer J L hL hJ hLip x y).1 u
  have hmax := yStar_maximizes f mu hmu hsc
    (JointSliceRegularity.differentiable_y_slice J hJ) u y
  change f u y ≤ f u v at hmax
  rw [psi_eq_value_at_primal J L hL hJ hLip, psi_eq_value_at_primal J L hL hJ hLip]
  simp only [graph, hprimal]
  change -(f u v + L * ‖u - x‖ ^ 2) ≤
    -(f (primal J L x y) y + L * ‖primal J L x y - x‖ ^ 2)
  linarith only [hmin, hmax]

end OriginalDualMinimizer


namespace FrozenAudit
open _root_.FrozenAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

def EpsilonSubgradient (g : E → ℝ) (y v : E) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ w : E, g y + inner ℝ v (w - y) - ε ≤ g w

theorem strongConvex_support
    (g : E → ℝ) (μ : ℝ)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (hdiff : Differentiable ℝ g) (y w : E) :
    g y + inner ℝ (gradient g y) (w - y) +
      μ / 2 * ‖w - y‖ ^ 2 ≤ g w := by
  let h : E → ℝ := fun z => g z - μ / 2 * ‖z‖ ^ 2
  have hc : ConvexOn ℝ (Set.univ : Set E) h :=
    strongConvexOn_iff_convex.mp hsc
  let a : ℝ → E := fun t => y + t • (w - y)
  have ha0 : a 0 = y := by simp [a]
  have ha1 : a 1 = w := by
    dsimp [a]
    simp only [one_smul]
    abel
  have hline : ConvexOn ℝ (Set.univ : Set ℝ)
      (fun t : ℝ => h (a t)) := by
    refine ⟨convex_univ, ?_⟩
    intro s hs t ht p q hp hq hpq
    have haff : a (p * s + q * t) = p • a s + q • a t := by
      calc
        a (p * s + q * t) =
            (p + q) • y + (p * s + q * t) • (w - y) := by
          simp only [a, hpq, one_smul]
        _ = p • a s + q • a t := by
          simp only [a, smul_add, add_smul, mul_smul]
          abel
    have hh := hc.2 (Set.mem_univ (a s)) (Set.mem_univ (a t)) hp hq hpq
    simpa only [smul_eq_mul, ← haff] using hh
  have hcurve : HasDerivAt a (w - y) (0 : ℝ) := by
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).smul_const (w - y)).const_add y)
  have hgy : HasFDerivAt g (fderiv ℝ g y) (a 0) := by
    rw [ha0]
    exact (hdiff y).hasFDerivAt
  have hgcurve : HasDerivAt (fun t : ℝ => g (a t))
      (inner ℝ (gradient g y) (w - y)) 0 := by
    simpa only [Function.comp_def, inner_gradient_left] using
      (hgy.comp_hasDerivAt (0 : ℝ) hcurve)
  have hnormcurve : HasDerivAt (fun t : ℝ => ‖a t‖ ^ 2)
      (2 * inner ℝ y (w - y)) 0 := by
    simpa only [ha0] using hcurve.norm_sq
  have hder : HasDerivAt (fun t : ℝ => h (a t))
      (inner ℝ (gradient g y) (w - y) -
        μ / 2 * (2 * inner ℝ y (w - y))) 0 := by
    simpa only [h, Pi.sub_def] using
      (hgcurve.sub (hnormcurve.const_mul (μ / 2)))
  have htangent := hline.le_slope_of_hasDerivAt
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) hder
  have ht : inner ℝ (gradient g y) (w - y) -
      μ / 2 * (2 * inner ℝ y (w - y)) ≤
      (g w - μ / 2 * ‖w‖ ^ 2) -
        (g y - μ / 2 * ‖y‖ ^ 2) := by
    simpa only [slope_def_field, ha0, ha1, h, sub_zero, div_one]
      using htangent
  rw [inner_sub_right (𝕜 := ℝ) y w y,
    real_inner_self_eq_norm_sq] at ht
  rw [norm_sub_sq_real, real_inner_comm y w]
  nlinarith only [ht]

theorem gradient_enlargement
    (g : E → ℝ) (μ δ : ℝ) (y v : E)
    (hμ : 0 < μ) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) μ g)
    (herror : ‖v - gradient g y‖ ≤ δ) :
    EpsilonSubgradient g y v (δ ^ 2 / (2 * μ)) := by
  constructor
  · positivity
  · intro w
    have hs := strongConvex_support g μ hsc hdiff y w
    have he : inner ℝ (v - gradient g y) (w - y) ≤ δ * ‖w - y‖ := by
      calc
        inner ℝ (v - gradient g y) (w - y) ≤
            ‖v - gradient g y‖ * ‖w - y‖ := real_inner_le_norm _ _
        _ ≤ δ * ‖w - y‖ :=
          mul_le_mul_of_nonneg_right herror (norm_nonneg _)
    rw [inner_sub_left] at he
    have hden : 0 < 2 * μ := by positivity
    have hcancel : (δ ^ 2 / (2 * μ)) * (2 * μ) = δ ^ 2 :=
      div_mul_cancel₀ _ (ne_of_gt hden)
    have hquad : δ * ‖w - y‖ ≤
        μ / 2 * ‖w - y‖ ^ 2 + δ ^ 2 / (2 * μ) := by
      apply (mul_le_mul_iff_right₀ hμ).mp
      nlinarith only [hcancel, sq_nonneg (μ * ‖w - y‖ - δ)]
    nlinarith only [hs, he, hquad]

end FrozenAudit

namespace RobustAHPE
open _root_.RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def chosenSlack (gamma sigma0 : ℝ) : ℝ := (sigma0 - gamma) / 4
noncomputable def outputGradientTolerance (mu lam eta r : ℝ) : ℝ :=
  eta * r * min lam⁻¹ (min 1 (mu / lam))

theorem chosenSlack_properties (gamma sigma0 : ℝ) (hgamma : 0 ≤ gamma) (hmargin : gamma < sigma0) :
    0 < chosenSlack gamma sigma0 ∧
    (gamma + chosenSlack gamma sigma0) ^ 2 + (chosenSlack gamma sigma0) ^ 2 < sigma0 ^ 2 := by
  have hg : 0 < sigma0 - gamma := sub_pos.mpr hmargin
  have hp := mul_nonneg hgamma hg.le
  have hs := sq_pos_of_pos hg
  unfold chosenSlack
  constructor <;> nlinarith only [hg, hp, hs]

theorem outputGradientTolerance_positive (mu lam eta r : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (heta : 0 < eta) (hr : 0 < r) :
    0 < outputGradientTolerance mu lam eta r := by
  unfold outputGradientTolerance
  positivity

theorem outputGradientTolerance_suffices (mu lam eta r delta : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (heta : 0 ≤ eta) (hr : 0 ≤ r) (hdelta : 0 ≤ delta)
    (hsmall : delta ≤ outputGradientTolerance mu lam eta r) :
    lam * delta ≤ eta * r ∧ lam * delta ^ 2 / mu ≤ eta ^ 2 * r ^ 2 := by
  let c := min lam⁻¹ (min 1 (mu / lam))
  have hc0 : 0 < c := by dsimp only [c]; positivity
  have hc1 : c ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc2 : c ≤ mu / lam := le_trans (min_le_right _ _) (min_le_right _ _)
  have hcLam : c * lam ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_left lam⁻¹ (min 1 (mu / lam))) hlam.le
    rw [inv_mul_cancel₀ (ne_of_gt hlam)] at hh
    exact hh
  have hsmall' : delta ≤ eta * r * c := hsmall
  have hcsq : c ^ 2 ≤ mu / lam := by
    have hh : c ^ 2 ≤ c := by nlinarith only [hc0.le, hc1]
    exact le_trans hh hc2
  constructor
  · have hm := mul_le_mul_of_nonneg_left hsmall' hlam.le
    have hc := mul_le_mul_of_nonneg_left hcLam (mul_nonneg heta hr)
    nlinarith only [hm, hc]
  · have hsq : delta ^ 2 ≤ (eta * r * c) ^ 2 :=
      (sq_le_sq₀ hdelta (by positivity)).mpr hsmall'
    have hm := mul_le_mul_of_nonneg_left hsq hlam.le
    have hc := (le_div_iff₀ hlam).mp hcsq
    have hcmul := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ eta ^ 2 * r ^ 2)
    apply (div_le_iff₀ hmu).mpr
    nlinarith only [hm, hcmul]

theorem enlarged_gradient_relative_certificate
    (g : E → ℝ) (mu lam gamma eta sigma0 delta : ℝ)
    (hmu : 0 < mu) (hlam : 0 < lam) (hgamma : 0 ≤ gamma) (heta : 0 ≤ eta)
    (hslack : (gamma + eta) ^ 2 + eta ^ 2 ≤ sigma0 ^ 2)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (y d v : E) (herror : ‖v - gradient g y‖ ≤ delta)
    (hres : ‖lam • gradient g y + d‖ ≤ gamma * ‖d‖)
    (htol1 : lam * delta ≤ eta * ‖d‖)
    (htol2 : lam * delta ^ 2 / mu ≤ eta ^ 2 * ‖d‖ ^ 2) :
    FrozenAudit.EpsilonSubgradient g y v (delta ^ 2 / (2 * mu)) ∧
      ‖lam • v + d‖ ^ 2 + 2 * lam * (delta ^ 2 / (2 * mu)) ≤ sigma0 ^ 2 * ‖d‖ ^ 2 := by
  refine ⟨FrozenAudit.gradient_enlargement g mu delta y v hmu hdiff hsc herror, ?_⟩
  have he : lam • v + d = (lam • gradient g y + d) + lam • (v - gradient g y) := by module
  have hn : ‖lam • v + d‖ ≤ (gamma + eta) * ‖d‖ := by
    have ht := norm_add_le (lam • gradient g y + d) (lam • (v - gradient g y))
    rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at ht
    have hm := mul_le_mul_of_nonneg_left herror hlam.le
    nlinarith only [ht, hm, hres, htol1]
  have hsq := (sq_le_sq₀ (norm_nonneg (lam • v + d)) (by positivity : 0 ≤ (gamma + eta) * ‖d‖)).mpr hn
  have hc := mul_le_mul_of_nonneg_right hslack (sq_nonneg ‖d‖)
  have heps : 2 * lam * (delta ^ 2 / (2 * mu)) = lam * delta ^ 2 / mu := by field_simp <;> ring
  rw [heps]
  nlinarith only [hsq, hc, htol2]

theorem small_gradient_contracts_distance (g : E → ℝ) (mu D : ℝ) (hmu : 0 < mu)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (xstar y : E) (hmin : ∀ w : E, g xstar ≤ g w) (hsmall : ‖gradient g y‖ ≤ mu * D / 2) :
    ‖y - xstar‖ ≤ D / 2 := by
  have hs := PacketCore.strongConvex_gradient_distance g mu hmu hsc hdiff xstar hmin y
  nlinarith only [hs, hsmall, hmu]

theorem output_tolerance_lower_bound_from_window (mu M lam eta sigmaL r : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (hwindow : sigmaL / M ≤ lam * r) :
    eta * sigmaL * min lam⁻¹ (min 1 (mu / lam)) / (M * lam) ≤
      outputGradientTolerance mu lam eta r := by
  have hc : 0 ≤ min lam⁻¹ (min 1 (mu / lam)) := by positivity
  have hw : sigmaL / (M * lam) ≤ r := by
    apply (div_le_iff₀ (mul_pos hM hlam)).mpr
    have hh := (div_le_iff₀ hM).mp hwindow
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg heta hc)
  dsimp only [outputGradientTolerance]
  convert! hm using 1 <;> field_simp <;> ring

end RobustAHPE

namespace RobustAHPE
open _root_.RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_search_output_to_relative_tuple
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam sigmaHat sigmaL sigmaU sigma0 : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaL : 0 < sigmaL) (hsigmaU : 0 ≤ sigmaU)
    (hmargin : sigmaHat + sigmaU < sigma0)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindowLower : sigmaL / M ≤ lam * ‖d‖) (hwindowUpper : lam * ‖d‖ ≤ sigmaU / M) :
    let eta := chosenSlack (sigmaHat + sigmaU) sigma0
    let tol := outputGradientTolerance mu lam eta ‖d‖
    0 < tol ∧
    eta * sigmaL * min lam⁻¹ (min 1 (mu / lam)) / (M * lam) ≤ tol ∧
    (∀ v : E, ‖v - gradient g (z + d)‖ ≤ tol →
      FrozenAudit.EpsilonSubgradient g (z + d) v (tol ^ 2 / (2 * mu)) ∧
      ‖lam • v + d‖ ^ 2 + 2 * lam * (tol ^ 2 / (2 * mu)) ≤ sigma0 ^ 2 * ‖d‖ ^ 2 ∧
      sigmaL / M ≤ lam * ‖d‖) := by
  dsimp only
  have hgamma : 0 ≤ sigmaHat + sigmaU := add_nonneg hsigmaHat hsigmaU
  have heta := chosenSlack_properties (sigmaHat + sigmaU) sigma0 hgamma hmargin
  have hd : 0 < ‖d‖ := by
    by_contra hf
    have hz : ‖d‖ = 0 := le_antisymm (le_of_not_gt hf) (norm_nonneg d)
    rw [hz, mul_zero] at hwindowLower
    exact not_le_of_gt (div_pos hsigmaL hM) hwindowLower
  have htol := outputGradientTolerance_positive mu lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖ hmu hlam heta.1 hd
  refine ⟨htol, output_tolerance_lower_bound_from_window mu M lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL ‖d‖ hmu hM hlam heta.1.le hwindowLower, ?_⟩
  intro v hv
  have hacc := outputGradientTolerance_suffices mu lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖
    (outputGradientTolerance mu lam (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖)
    hmu hlam heta.1.le (norm_nonneg d) htol.le le_rfl
  have hres := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindowUpper
  have hr := enlarged_gradient_relative_certificate g mu lam (sigmaHat + sigmaU)
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigma0
    (outputGradientTolerance mu lam (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖)
    hmu hlam hgamma heta.1.le heta.2.le (hC2.differentiable (by norm_num)) hsc
    (z + d) d v hv hres hacc.1 hacc.2
  exact ⟨hr.1, hr.2, hwindowLower⟩

end RobustAHPE

namespace RobustAHPE
open _root_.RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def globalMinimizer (g : E → ℝ) : E :=
  Classical.epsilon (fun z => ∀ w : E, g z ≤ g w)

theorem globalMinimizer_is_actual [FiniteDimensional ℝ E]
    (g : E → ℝ) (mu : ℝ) (hmu : 0 < mu) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g) :
    ∀ w : E, g (globalMinimizer g) ≤ g w := by
  have hex : ∃ z : E, ∀ w : E, g z ≤ g w := by
    obtain ⟨z, hz⟩ := PacketCore.exists_inner_maximizer_finiteDimensional g mu 0 0 0 0
      hmu (by simpa using hsc) hdiff (0 : E)
    exact ⟨z, fun w => by simpa [PacketCore.saddleValue] using hz w⟩
  exact Classical.epsilon_spec hex

theorem globalMinimizer_unique [FiniteDimensional ℝ E]
    (g : E → ℝ) (mu : ℝ) (hmu : 0 < mu) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g) (y : E) (hy : ∀ w : E, g y ≤ g w) :
    y = globalMinimizer g := by
  have hz := globalMinimizer_is_actual g mu hmu hdiff hsc
  have hzero := PacketCore.gradient_eq_zero_at_global_min g (globalMinimizer g) hz
  have hs := PacketCore.strongConvex_support g mu hsc hdiff (globalMinimizer g) y
  rw [hzero, inner_zero_left, add_zero] at hs
  have hym := hy (globalMinimizer g)
  have hsq : ‖y - globalMinimizer g‖ ^ 2 ≤ 0 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < mu / 2)).mp
    nlinarith only [hs, hym]
  have hn : ‖y - globalMinimizer g‖ = 0 := by
    nlinarith only [hsq, norm_nonneg (y - globalMinimizer g)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem small_gradient_actual_minimizer_contract [FiniteDimensional ℝ E]
    (g : E → ℝ) (mu D : ℝ) (hmu : 0 < mu) (hdiff : Differentiable ℝ g)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (y : E) (hsmall : ‖gradient g y‖ ≤ mu * D / 2) :
    ‖y - globalMinimizer g‖ ≤ D / 2 :=
  small_gradient_contracts_distance g mu D hmu hdiff hsc (globalMinimizer g) y
    (globalMinimizer_is_actual g mu hmu hdiff hsc) hsmall

end RobustAHPE

namespace RobustAHPE
open _root_.RobustAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def uniformOutputGradientTolerance (mu M lamHi eta sigmaL : ℝ) : ℝ :=
  eta * sigmaL * min lamHi⁻¹ (min 1 (mu / lamHi)) / (M * lamHi)

theorem uniformOutputGradientTolerance_positive (mu M lamHi eta sigmaL : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hHi : 0 < lamHi) (heta : 0 < eta) (hL : 0 < sigmaL) :
    0 < uniformOutputGradientTolerance mu M lamHi eta sigmaL := by
  unfold uniformOutputGradientTolerance
  positivity

theorem output_tolerance_coefficient_antitone (mu lam lamHi : ℝ)
    (hmu : 0 ≤ mu) (hlam : 0 < lam) (hbound : lam ≤ lamHi) :
    min lamHi⁻¹ (min 1 (mu / lamHi)) ≤ min lam⁻¹ (min 1 (mu / lam)) := by
  exact min_le_min (inv_anti₀ hlam hbound)
    (min_le_min le_rfl (div_le_div_of_nonneg_left hmu hlam hbound))

theorem uniform_output_tolerance_le_actual (mu M lam lamHi eta sigmaL r : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (heta : 0 ≤ eta) (hL : 0 ≤ sigmaL)
    (hbound : lam ≤ lamHi) (hwindow : sigmaL / M ≤ lam * r) :
    uniformOutputGradientTolerance mu M lamHi eta sigmaL ≤ outputGradientTolerance mu lam eta r := by
  have hHi : 0 < lamHi := lt_of_lt_of_le hlam hbound
  have hc := output_tolerance_coefficient_antitone mu lam lamHi hmu.le hlam hbound
  have hcHi : 0 ≤ min lamHi⁻¹ (min 1 (mu / lamHi)) := by positivity
  have htop := output_tolerance_lower_bound_from_window mu M lam eta sigmaL r hmu hM hlam heta hwindow
  unfold uniformOutputGradientTolerance
  calc
    eta * sigmaL * min lamHi⁻¹ (min 1 (mu / lamHi)) / (M * lamHi)
      ≤ eta * sigmaL * min lamHi⁻¹ (min 1 (mu / lamHi)) / (M * lam) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hM hlam)
          (mul_le_mul_of_nonneg_left hbound hM.le)
    _ ≤ eta * sigmaL * min lam⁻¹ (min 1 (mu / lam)) / (M * lam) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (mul_nonneg heta hL)) (by positivity)
    _ ≤ outputGradientTolerance mu lam eta r := htop

theorem actual_search_output_to_uniform_relative_tuple
    (g : E → ℝ) (hC2 : ContDiff ℝ 2 g) (mu M lam lamHi sigmaHat sigmaL sigmaU sigma0 : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hlamHi : lam ≤ lamHi)
    (hsigmaHat : 0 ≤ sigmaHat) (hsigmaL : 0 < sigmaL) (hsigmaU : 0 ≤ sigmaU)
    (hmargin : sigmaHat + sigmaU < sigma0)
    (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient g) x - fderiv ℝ (gradient g) y‖ ≤ M * ‖x - y‖)
    (z d : E) (hATS : ‖lam • trueModelVector g z M d + d‖ ≤ sigmaHat * ‖d‖)
    (hwindowLower : sigmaL / M ≤ lam * ‖d‖) (hwindowUpper : lam * ‖d‖ ≤ sigmaU / M) :
    let eta := chosenSlack (sigmaHat + sigmaU) sigma0
    let tol := uniformOutputGradientTolerance mu M lamHi eta sigmaL
    0 < tol ∧
    (∀ v : E, ‖v - gradient g (z + d)‖ ≤ tol →
      FrozenAudit.EpsilonSubgradient g (z + d) v (tol ^ 2 / (2 * mu)) ∧
      ‖lam • v + d‖ ^ 2 + 2 * lam * (tol ^ 2 / (2 * mu)) ≤ sigma0 ^ 2 * ‖d‖ ^ 2 ∧
      sigmaL / M ≤ lam * ‖d‖) := by
  dsimp only
  have hgamma : 0 ≤ sigmaHat + sigmaU := add_nonneg hsigmaHat hsigmaU
  have heta := chosenSlack_properties (sigmaHat + sigmaU) sigma0 hgamma hmargin
  have hHi : 0 < lamHi := lt_of_lt_of_le hlam hlamHi
  have htol := uniformOutputGradientTolerance_positive mu M lamHi
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL hmu hM hHi heta.1 hsigmaL
  have hbound := uniform_output_tolerance_le_actual mu M lam lamHi
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL ‖d‖ hmu hM hlam heta.1.le hsigmaL.le hlamHi hwindowLower
  refine ⟨htol, ?_⟩
  intro v hv
  have hacc := outputGradientTolerance_suffices mu lam
    (chosenSlack (sigmaHat + sigmaU) sigma0) ‖d‖
    (uniformOutputGradientTolerance mu M lamHi (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL)
    hmu hlam heta.1.le (norm_nonneg d) htol.le hbound
  have hres := true_gradient_residual_from_ATS g hC2 M lam sigmaHat sigmaU hM hlam hH z d hATS hwindowUpper
  have hr := enlarged_gradient_relative_certificate g mu lam (sigmaHat + sigmaU)
    (chosenSlack (sigmaHat + sigmaU) sigma0) sigma0
    (uniformOutputGradientTolerance mu M lamHi (chosenSlack (sigmaHat + sigmaU) sigma0) sigmaL)
    hmu hlam hgamma heta.1.le heta.2.le (hC2.differentiable (by norm_num)) hsc
    (z + d) d v hv hres hacc.1 hacc.2
  exact ⟨hr.1, hr.2, hwindowLower⟩

end RobustAHPE


namespace OriginalCertifiedCoupledAHPE
open _root_.OriginalCertifiedCoupledAHPE

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

noncomputable def effective (c : Settings) : Settings :=
  if c.A = 0 then proxySettings c else c

noncomputable def effectiveY {E : Type*} (c : Settings) (x y : E) : E :=
  if c.A = 0 then x else y

theorem effective_mu (c : Settings) : (effective c).mu = c.mu := by
  unfold effective
  split_ifs <;> rfl

theorem effective_Lg (c : Settings) : (effective c).Lg = c.Lg := by
  unfold effective
  split_ifs <;> rfl

theorem effective_M (c : Settings) : (effective c).M = c.M := by
  unfold effective
  split_ifs <;> rfl

theorem effective_sigma (c : Settings) : (effective c).sigma = c.sigma := by
  unfold effective
  split_ifs <;> rfl

theorem effective_low (c : Settings) : (effective c).sigmaLow = c.sigmaLow := by
  unfold effective
  split_ifs <;> rfl

theorem effective_up (c : Settings) : (effective c).sigmaUp = c.sigmaUp := by
  unfold effective
  split_ifs <;> rfl

theorem effective_rho (c : Settings) : (effective c).rho = c.rho := by
  unfold effective
  split_ifs <;> rfl

theorem effective_legal (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A) : Legal (effective c) := by
  unfold effective
  split_ifs with hzero
  · exact proxy_legal c hc
  · exact positive_legal c hc (lt_of_le_of_ne hA (Ne.symm hzero))

noncomputable def outputTolerance (c : Settings) (sigma0 : ℝ) : ℝ :=
  RobustAHPE.uniformOutputGradientTolerance c.mu c.M (lambdaMax c)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow

noncomputable def outputQueryPrecision (c : Settings) (sigma0 : ℝ) : ℝ :=
  min (c.rho / 8) (outputTolerance c sigma0)

theorem outputTolerance_positive (c : Settings) (hc : Legal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0) : 0 < outputTolerance c sigma0 := by
  have hup : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hslack := RobustAHPE.chosenSlack_properties (c.sigma + c.sigmaUp) sigma0
    (add_nonneg hc.sigma_pos.le hup.le) hmargin
  have hp := compact_properties c hc 0 (by norm_num)
  exact RobustAHPE.uniformOutputGradientTolerance_positive c.mu c.M (lambdaMax c)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
    hc.mu_pos hc.M_pos hp.2.2.2.2.2.2.2.2 hslack.1 hc.low_pos

theorem outputQueryPrecision_positive (c : Settings) (hc : Legal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0) : 0 < outputQueryPrecision c sigma0 :=
  lt_min (by exact div_pos hc.rho_pos (by norm_num)) (outputTolerance_positive c hc sigma0 hmargin)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def program (c : Settings) (sigma0 : ℝ) (x y : E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  positiveProgram (effective c) (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y)

noncomputable def actualLambda (c : Settings) (b : ℝ) : ℝ := lambda (effective c).A b
noncomputable def actualWeight (c : Settings) (b : ℝ) : ℝ :=
  (actualLambda c b + Real.sqrt (actualLambda c b ^ 2 + 4 * actualLambda c b * c.A)) / 2
noncomputable def actualCenter (c : Settings) (x y : E) (b : ℝ) : E :=
  center x (effectiveY c x y) b

noncomputable def getterBound (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℝ :=
  observedGradientBound getter (effective c) x (effectiveY c x y)

noncomputable def queryFloor (getter : E × ℝ → Answer E) (c : Settings)
    (sigma0 : ℝ) (x y : E) : ℝ :=
  precisionFloor (effective c) (getterBound getter c x y) (outputQueryPrecision (effective c) sigma0)

noncomputable def trialFuel (getter : E × ℝ → Answer E) (c : Settings) (x y : E) : ℕ :=
  fuel (effective c) (getterBound getter c x y) x (effectiveY c x y)

theorem actual_coupled_center (c : Settings) (hA : 0 ≤ c.A) (x y : E) (b : ℝ)
    (hb : 0 < b) (hb1 : b < 1) :
    0 < actualLambda c b ∧ 0 < actualWeight c b ∧ 0 < c.A + actualWeight c b ∧
      actualCenter c x y b =
        (c.A / (c.A + actualWeight c b)) • y +
          (actualWeight c b / (c.A + actualWeight c b)) • x := by
  by_cases hzero : c.A = 0
  · have hpos : 0 < actualLambda c b := by
      simpa only [actualLambda, effective, if_pos hzero, proxySettings] using
        (coupled_weights 1 b (by norm_num) hb hb1).1
    have hw : actualWeight c b = actualLambda c b := by
      simpa only [actualWeight, hzero] using (zero_weight_first_step (actualLambda c b) hpos x y).1
    have hc : actualCenter c x y b = x := by
      simp only [actualCenter, effectiveY, if_pos hzero]
      exact center_same x b
    refine ⟨hpos, by rwa [hw], by simpa only [hzero, zero_add, hw] using hpos, ?_⟩
    rw [hc, hzero, hw]
    exact (zero_weight_first_step (actualLambda c b) hpos x y).2.symm
  · have hApos : 0 < c.A := lt_of_le_of_ne hA (Ne.symm hzero)
    have hlam : actualLambda c b = lambda c.A b := by simp only [actualLambda, effective, if_neg hzero]
    have hw : actualWeight c b = weight c.A b := by
      rw [actualWeight, hlam]
      exact (coupled_square_root_formula c.A b hApos hb hb1).symm
    have hp := coupled_weights c.A b hApos hb hb1
    refine ⟨by rw [hlam]; exact hp.1, by rw [hw]; exact hp.2.1,
      by rw [hw]; exact add_pos hApos hp.2.1, ?_⟩
    rw [hw]
    change center x (effectiveY c x y) b = _
    rw [effectiveY, if_neg hzero]
    exact (coupled_center c.A b hApos hb hb1 x y).symm

noncomputable def ValidOutput (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (x y : E) : Result E → Prop
  | .stop w => ‖w - RobustAHPE.globalMinimizer g‖ ≤ D / 2
  | .window b d aY =>
      0 < actualLambda c b ∧ 0 < actualWeight c b ∧ 0 < c.A + actualWeight c b ∧
      actualCenter c x y b =
        (c.A / (c.A + actualWeight c b)) • y +
          (actualWeight c b / (c.A + actualWeight c b)) • x ∧
      FrozenAudit.EpsilonSubgradient g (actualCenter c x y b + d) aY.grad
        ((outputTolerance (effective c) sigma0) ^ 2 / (2 * c.mu)) ∧
      ‖actualLambda c b • aY.grad + d‖ ^ 2 +
        2 * actualLambda c b * ((outputTolerance (effective c) sigma0) ^ 2 / (2 * c.mu)) ≤
          sigma0 ^ 2 * ‖d‖ ^ 2 ∧
      c.sigmaLow / c.M ≤ actualLambda c b * ‖d‖

theorem valid_search_gives_original_tuple
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (sigma0 D G : ℝ) (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hrho : c.rho = c.mu * D / 2) (hG : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hH : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (x y : E) (value : Result E)
    (hvalid : ValidResult g (effective c) G (outputQueryPrecision (effective c) sigma0)
      x (effectiveY c x y) value) : ValidOutput g c sigma0 D x y value := by
  have he := effective_legal c hc hA
  cases value with
  | stop w =>
    apply RobustAHPE.small_gradient_actual_minimizer_contract g c.mu D hc.mu_pos
      (hC2.differentiable (by norm_num)) hsc w
    simpa only [ValidResult, effective_rho, hrho] using hvalid
  | window b d aY =>
    rcases hvalid with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
    have hbounds := interval_lambda_bounds (effective c) he G hG b hb
    have htuple := RobustAHPE.actual_search_output_to_uniform_relative_tuple g hC2
      (effective c).mu (effective c).M (lambda (effective c).A b) (lambdaMax (effective c))
      (effective c).sigma (effective c).sigmaLow (effective c).sigmaUp sigma0
      he.mu_pos he.M_pos hlam hbounds.2.2.2.2 he.sigma_pos.le he.low_pos
      (he.low_pos.trans he.low_lt_up).le
      (by simpa only [effective_sigma, effective_up] using hmargin)
      (by simpa only [effective_mu] using hsc)
      (by simpa only [effective_M] using hH)
      (center x (effectiveY c x y) b) d hATS hlow hhigh
    have herrTol : ‖aY.grad - gradient g (center x (effectiveY c x y) b + d)‖ ≤
        outputTolerance (effective c) sigma0 :=
      herr.trans (min_le_right _ _)
    have hcert := htuple.2 aY.grad herrTol
    have hcouple := actual_coupled_center c hA x y b hb0 hb1
    exact ⟨hcouple.1, hcouple.2.1, hcouple.2.2.1, hcouple.2.2.2,
      by simpa only [actualCenter, outputTolerance, effective_mu] using hcert.1,
      by simpa only [actualLambda, outputTolerance, effective_mu] using hcert.2.1,
      by simpa only [actualLambda, effective_low, effective_M] using hcert.2.2⟩

end OriginalCertifiedCoupledAHPE

namespace OriginalCertifiedCoupledAHPE
open _root_.OriginalCertifiedCoupledAHPE
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCoupledBetaAlgebra
open OriginalFirstCoupledStep
open OriginalCoupledGetterProgram
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem original_certified_coupled_ahpe_step
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (sigma0 D : ℝ) (hmargin : c.sigma + c.sigmaUp < sigma0) (hsigma0 : sigma0 < 1)
    (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute getter (program c sigma0 x y)).1 = .found value ∧
      ValidOutput g c sigma0 D x y value ∧
      0 < queryFloor getter c sigma0 x y ∧
      (∀ q ∈ trace getter (program c sigma0 x y), queryFloor getter c sigma0 x y ≤ q.2) ∧
      (execute getter (program c sigma0 x y)).2 ≤ 2 * trialFuel getter c x y + 5 ∧
      baseCost getter cost (program c sigma0 x y) ≤
        logarithmicAtomicBound K (queryFloor getter c sigma0 x y) * (2 * trialFuel getter c x y + 5) ∧
      ((execute getter (program c sigma0 x y)).2 : ℝ) ≤
        7 + 2 * Real.logb 2 (max 1
          ((modulus (effective c) (getterBound getter c x y) x (effectiveY c x y) *
            (upper (effective c) - lower (effective c) (getterBound getter c x y))) /
              ((thresholdHigh (effective c) - thresholdLow (effective c)) / 2))) := by
  have he := effective_legal c hc hA
  have hmarginE : (effective c).sigma + (effective c).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up] using hmargin
  have hprecision := outputQueryPrecision_positive (effective c) he sigma0 hmarginE
  have hbound := observed_bound_is_valid g (effective c) he getter hgetter x (effectiveY c x y)
  obtain ⟨value, hrun, hvalid, hcount⟩ := positiveProgram_success_and_getter_calls g
    (effective c) he (outputQueryPrecision (effective c) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu] using hsc)
    (by simpa only [effective_Lg] using hlip) (by simpa only [effective_M] using hHlip)
    getter hgetter x (effectiveY c x y)
  have hfloor := precisionFloor_positive (effective c) he _ _ hbound.1 hprecision
  have hcost := positiveProgram_logarithmic_base_cost getter cost (effective c)
    (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y) K hK hfloor hatomic hcount
  have hlog := positiveProgram_getter_log_bound getter (effective c)
    (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y) hcount
  refine ⟨value, hrun,
    valid_search_gives_original_tuple g c hc hA sigma0 D _ hmargin hrho hbound.1 hC2 hsc hHlip x y value hvalid,
    hfloor, positiveProgram_request_precision_floor getter (effective c)
      (outputQueryPrecision (effective c) sigma0) x (effectiveY c x y), hcount, hcost, hlog⟩

end OriginalCertifiedCoupledAHPE

namespace OriginalCertifiedCoupledAHPE
open _root_.OriginalCertifiedCoupledAHPE
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem original_certified_step_actual_base_program
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (hA : 0 ≤ c.A)
    (sigma0 D : ℝ) (hmargin : c.sigma + c.sigmaUp < sigma0) (hsigma0 : sigma0 < 1)
    (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(implementedGetter baseAnswer oracle (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(implementedGetter baseAnswer oracle (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 →
      (execute baseAnswer (oracle q)).2 ≤ logarithmicAtomicBound K q.2)
    (x y : E) :
    ∃ value : Result E,
      (execute baseAnswer (primitiveLower oracle (program c sigma0 x y))).1 = .found value ∧
      ValidOutput g c sigma0 D x y value ∧
      0 < queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y ∧
      (execute baseAnswer (primitiveLower oracle (program c sigma0 x y))).2 ≤
        logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) *
          (2 * trialFuel (implementedGetter baseAnswer oracle) c x y + 5) ∧
      ((execute baseAnswer (primitiveLower oracle (program c sigma0 x y))).2 : ℝ) ≤
        (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) : ℝ) *
          (7 + 2 * Real.logb 2 (max 1
            ((modulus (effective c) (getterBound (implementedGetter baseAnswer oracle) c x y) x (effectiveY c x y) *
              (upper (effective c) - lower (effective c) (getterBound (implementedGetter baseAnswer oracle) c x y))) /
                ((thresholdHigh (effective c) - thresholdLow (effective c)) / 2)))) := by
  obtain ⟨value, hrun, hvalid, hfloor, hprecision, hcount, hcost, hlog⟩ :=
    original_certified_coupled_ahpe_step g c hc hA sigma0 D hmargin hsigma0 hrho hC2 hsc hlip hHlip
      (implementedGetter baseAnswer oracle) hgetter (implementedCost baseAnswer oracle) K hK hatomic x y
  have hlocal := logarithmic_baseCost_bound (implementedGetter baseAnswer oracle)
    (implementedCost baseAnswer oracle) Prod.snd (program c sigma0 x y) K _ hK hfloor hprecision hatomic
  have hcast : (baseCost (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
      (program c sigma0 x y) : ℝ) ≤
        (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) : ℝ) *
          ((execute (implementedGetter baseAnswer oracle) (program c sigma0 x y)).2 : ℝ) := by
    exact_mod_cast hlocal
  have hscaled := mul_le_mul_of_nonneg_left hlog
    (Nat.cast_nonneg (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y)) :
      (0 : ℝ) ≤ (logarithmicAtomicBound K (queryFloor (implementedGetter baseAnswer oracle) c sigma0 x y) : ℝ))
  rw [primitiveLower_execution]
  exact ⟨value, hrun, hvalid, hfloor, hcost, hcast.trans hscaled⟩

end OriginalCertifiedCoupledAHPE


namespace LargeStepAHPE
open _root_.LargeStepAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def potential (g : E → ℝ) (A : ℝ) (x y xstar : E) : ℝ :=
  A * (g y - g xstar) + ‖x - xstar‖ ^ 2 / 2

def EpsilonSubgradient (g : E → ℝ) (y v : E) (eps : ℝ) : Prop :=
  0 ≤ eps ∧ ∀ w : E, g y + inner ℝ v (w - y) - eps ≤ g w

theorem a_formula_properties (A lam : ℝ) (hA : 0 ≤ A) (hlam : 0 < lam) :
    let a := (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2
    0 < a ∧ 0 < A + a ∧ a ^ 2 = lam * (A + a) := by
  dsimp only
  have hrad : 0 ≤ lam ^ 2 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (lam ^ 2 + 4 * lam * A)
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith only [hs]

theorem one_step_potential
    (g : E → ℝ) (Aold Anew a lam sigma eps : ℝ)
    (xold yold xnew ynew z v xstar : E)
    (hAold : 0 ≤ Aold) (hAnew : 0 < Anew) (ha : 0 ≤ a) (hlam : 0 < lam)
    (hAsum : Anew = Aold + a) (hasquare : a ^ 2 = lam * Anew)
    (hz : Anew • z = Aold • yold + a • xold)
    (hx : xnew = xold - a • v)
    (hsubgrad : EpsilonSubgradient g ynew v eps)
    (hrelative : ‖lam • v + (ynew - z)‖ ^ 2 + 2 * lam * eps ≤ sigma ^ 2 * ‖ynew - z‖ ^ 2) :
    potential g Anew xnew ynew xstar ≤ potential g Aold xold yold xstar -
      ((1 - sigma ^ 2) / 2) * (Anew / lam) * ‖ynew - z‖ ^ 2 := by
  have hold := mul_le_mul_of_nonneg_left (hsubgrad.2 yold) hAold
  have hstar := mul_le_mul_of_nonneg_left (hsubgrad.2 xstar) ha
  have hi : Aold * inner ℝ v (yold - ynew) + a * inner ℝ v (xstar - ynew) =
      -Anew * inner ℝ v (ynew - z) - a * inner ℝ v (xold - xstar) := by
    have hh := congrArg (fun t : E => inner ℝ v t) hz
    simp only [inner_smul_right, inner_add_right] at hh
    simp only [inner_sub_right]
    rw [hAsum] at hh ⊢
    nlinarith only [hh]
  have hsupport : Anew * (g ynew - g xstar) ≤
      Aold * (g yold - g xstar) + Anew * eps + Anew * inner ℝ v (ynew - z) +
        a * inner ℝ v (xold - xstar) := by
    rw [hAsum] at hi ⊢
    nlinarith only [hold, hstar, hi]
  have hxnorm : ‖xnew - xstar‖ ^ 2 = ‖xold - xstar‖ ^ 2 -
      2 * a * inner ℝ v (xold - xstar) + a ^ 2 * ‖v‖ ^ 2 := by
    rw [hx]
    have he : xold - a • v - xstar = (xold - xstar) - a • v := by abel
    rw [he, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      inner_smul_right, real_inner_comm (xold - xstar) v]
    ring
  have hr := hrelative
  rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, abs_of_pos hlam,
    mul_pow, real_inner_smul_left] at hr
  have hbase : 2 * lam * eps + 2 * lam * inner ℝ v (ynew - z) + lam ^ 2 * ‖v‖ ^ 2 ≤
      -(1 - sigma ^ 2) * ‖ynew - z‖ ^ 2 := by nlinarith only [hr]
  have hm := mul_le_mul_of_nonneg_left hbase hAnew.le
  have hR : Anew * eps + Anew * inner ℝ v (ynew - z) + (a ^ 2 / 2) * ‖v‖ ^ 2 ≤
      -((1 - sigma ^ 2) / 2) * (Anew / lam) * ‖ynew - z‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * lam)).mp
    convert! hm using 1
    · rw [hasquare]
      ring
    · field_simp
      <;> ring
  dsimp only [potential]
  nlinarith only [hsupport, hxnorm, hR]

end LargeStepAHPE

namespace LargeStepAHPE
open _root_.LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem prefix_parameter_properties
    (A a lam : ℕ → ℝ) (n : ℕ) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k) :
    (∀ k ≤ n, 0 ≤ A k) ∧
    (∀ k < n, 0 < a k ∧ 0 < A (k + 1) ∧ (a k) ^ 2 = lam k * A (k + 1)) := by
  have hAnonneg : ∀ k ≤ n, 0 ≤ A k := by
    intro k
    induction k with
    | zero => intro _; rw [hA0]
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      have hp := a_formula_properties (A k) (lam k) (ih (by omega)) (hlam k hkn)
      dsimp only at hp
      rw [← haformula k hkn] at hp
      rw [hrec k hkn]
      exact hp.2.1.le
  refine ⟨hAnonneg, ?_⟩
  intro k hk
  have hp := a_formula_properties (A k) (lam k) (hAnonneg k (by omega)) (hlam k hk)
  dsimp only at hp
  rw [← haformula k hk] at hp
  rw [hrec k hk]
  exact hp

theorem prefix_energy_balance
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma : ℝ) (xstar : E) (n : ℕ) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2) :
    potential g (A n) (x n) (y n) xstar +
      (1 - sigma ^ 2) / 2 *
        (∑ k ∈ Finset.range n, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) ≤
      potential g (A 0) (x 0) (y 0) xstar := by
  have hp := prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have hstep : ∀ k < n,
      potential g (A (k + 1)) (x (k + 1)) (y (k + 1)) xstar ≤
        potential g (A k) (x k) (y k) xstar -
          (1 - sigma ^ 2) / 2 * ((A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) := by
    intro k hk
    have hpos := hp.2 k hk
    have hcenter : A (k + 1) • z k = A k • y k + a k • x k := by
      rw [hz k hk]
      have h1 : A (k + 1) * (A k / A (k + 1)) = A k := by field_simp [ne_of_gt hpos.2.1]
      have h2 : A (k + 1) * (a k / A (k + 1)) = a k := by field_simp [ne_of_gt hpos.2.1]
      simp only [smul_add, smul_smul, h1, h2]
    have hs := one_step_potential g (A k) (A (k + 1)) (a k) (lam k) sigma (err k)
      (x k) (y k) (x (k + 1)) (y (k + 1)) (z k) (v k) xstar
      (hp.1 k (by omega)) hpos.2.1 hpos.1.le (hlam k hk) (hrec k hk) hpos.2.2
      hcenter (hx k hk) (hsubgrad k hk) (hrelative k hk)
    simpa only [mul_assoc] using hs
  have hpartial : ∀ j ≤ n,
      potential g (A j) (x j) (y j) xstar + (1 - sigma ^ 2) / 2 *
        (∑ k ∈ Finset.range j, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) ≤
        potential g (A 0) (x 0) (y 0) xstar := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hjs : j < n := by omega
      have hh := hstep j hjs
      have hi := ih (by omega)
      rw [Finset.sum_range_succ]
      nlinarith only [hh, hi]
  exact hpartial n le_rfl

theorem prefix_energy_and_step_budget
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma D : ℝ) (xstar : E) (n : ℕ) (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hmin : ∀ w : E, g xstar ≤ g w) (hD : ‖x 0 - xstar‖ ≤ D) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2) :
    potential g (A n) (x n) (y n) xstar ≤ D ^ 2 / 2 ∧
    2 * A n * (g (y n) - g xstar) ≤ D ^ 2 ∧
    (∑ k ∈ Finset.range n, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2) ≤
      D ^ 2 / (1 - sigma ^ 2) := by
  have hp := prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have hb := prefix_energy_balance g A a lam x y z v err sigma xstar n hA0 hlam haformula hrec hz hx hsubgrad hrelative
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  have hP0 : potential g (A 0) (x 0) (y 0) xstar ≤ D ^ 2 / 2 := by
    simp only [potential, hA0, zero_mul, zero_add]
    have hn := norm_nonneg (x 0 - xstar)
    nlinarith only [hD, hn]
  have hPnonneg : 0 ≤ potential g (A n) (x n) (y n) xstar := by
    unfold potential
    exact add_nonneg (mul_nonneg (hp.1 n le_rfl) (sub_nonneg.mpr (hmin _))) (by positivity)
  have hsum : 0 ≤ ∑ k ∈ Finset.range n, (A (k + 1) / lam k) * ‖y (k + 1) - z k‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact mul_nonneg (div_nonneg (hp.2 k hkn).2.1.le (hlam k hkn).le) (sq_nonneg _)
  have hupper : potential g (A n) (x n) (y n) xstar ≤ D ^ 2 / 2 := by
    nlinarith only [hb, hP0, mul_nonneg halpha.le hsum]
  refine ⟨hupper, ?_, ?_⟩
  · dsimp only [potential] at hupper
    have hn := sq_nonneg ‖x n - xstar‖
    nlinarith only [hupper, hn]
  · apply (le_div_iff₀ halpha).mpr
    nlinarith only [hb, hP0, hPnonneg]

end LargeStepAHPE

namespace LargeStepAHPE
open _root_.LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem large_step_ratio_bound (A lam M theta r : ℝ)
    (hA : 0 ≤ A) (hlam : 0 < lam) (hM : 0 < M) (htheta : 0 < theta) (hr : 0 ≤ r)
    (hlarge : theta / M ≤ lam * r) :
    (theta ^ 2 / M ^ 2) * (A / lam ^ 3) ≤ (A / lam) * r ^ 2 := by
  have hs := (div_le_iff₀ hM).mp hlarge
  have hsq : theta ^ 2 ≤ ((lam * r) * M) ^ 2 :=
    (sq_le_sq₀ htheta.le (by positivity)).mpr hs
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ A / (M ^ 2 * lam ^ 3))
  convert! hm using 1 <;> field_simp <;> ring

theorem reciprocal_budget_from_weighted_budget (A lam r : ℕ → ℝ) (n : ℕ)
    (alpha M theta D : ℝ) (halpha : 0 < alpha) (hM : 0 < M) (htheta : 0 < theta)
    (hA : ∀ k < n, 0 ≤ A (k + 1)) (hlam : ∀ k < n, 0 < lam k)
    (hr : ∀ k < n, 0 ≤ r k) (hlarge : ∀ k < n, theta / M ≤ lam k * r k)
    (hbudget : (∑ k ∈ Finset.range n, (A (k + 1) / lam k) * (r k) ^ 2) ≤ D ^ 2 / alpha) :
    (∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3) ≤ M ^ 2 * D ^ 2 / (theta ^ 2 * alpha) := by
  have hsum : (theta ^ 2 / M ^ 2) * (∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3) ≤
      ∑ k ∈ Finset.range n, (A (k + 1) / lam k) * (r k) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact large_step_ratio_bound (A (k + 1)) (lam k) M theta (r k)
      (hA k hkn) (hlam k hkn) hM htheta (hr k hkn) (hlarge k hkn)
  have hh := le_trans hsum hbudget
  apply (le_div_iff₀ (by positivity : 0 < theta ^ 2 * alpha)).mpr
  have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ M ^ 2 * alpha)
  convert! hm using 1 <;> field_simp <;> ring

end LargeStepAHPE


namespace OriginalAHPEWeightGrowth
open _root_.OriginalAHPEWeightGrowth

open scoped BigOperators

theorem rpow_pow_nat (x p : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    (x ^ p) ^ n = x ^ (p * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem reciprocal_sixth_moment_bound
    {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 < b i) :
    (s.card : ℝ) ^ 7 ≤ (∑ i ∈ s, b i) ^ 6 * ∑ i ∈ s, 1 / (b i) ^ 6 := by
  let f := fun i => (b i) ^ (6 / 7 : ℝ)
  let g := fun i => (b i) ^ (-6 / 7 : ℝ)
  have hpq : Real.HolderConjugate (7 / 6) 7 := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq
    (f := f) (g := g) (fun i hi => Real.rpow_nonneg (hb i hi).le _)
    (fun i hi => Real.rpow_nonneg (hb i hi).le _)
  have hfg : ∑ i ∈ s, f i * g i = (s.card : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp only [f, g]
        rw [← Real.rpow_add (hb i hi)]
        norm_num
      _ = _ := by simp
  have hfp : ∑ i ∈ s, (f i) ^ (7 / 6 : ℝ) = ∑ i ∈ s, b i := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    rw [← Real.rpow_mul (hb i hi).le]
    norm_num
  have hgp : ∑ i ∈ s, (g i) ^ (7 : ℝ) = ∑ i ∈ s, 1 / (b i) ^ 6 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [g]
    rw [← Real.rpow_mul (hb i hi).le]
    norm_num [Real.rpow_neg, Real.rpow_natCast] <;> rfl
  rw [hfg, hfp, hgp] at hh
  have hexp : (1 : ℝ) / (7 / 6) = 6 / 7 := by norm_num
  rw [hexp] at hh
  have hs : 0 ≤ ∑ i ∈ s, b i := Finset.sum_nonneg (fun i hi => (hb i hi).le)
  have ht : 0 ≤ ∑ i ∈ s, 1 / (b i) ^ 6 := by positivity
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (s.card : ℝ)) hh 7
  rw [mul_pow, rpow_pow_nat _ _ hs, rpow_pow_nat _ _ ht] at hpow
  norm_num [Real.rpow_natCast] at hpow
  simpa only [one_div] using hpow

theorem cube_root_increment_bound
    (x y a : ℝ) (hx : 0 ≤ x) (hy : 0 < y) (hrec : y = x + a) :
    a / y ^ (2 / 3 : ℝ) ≤ 3 * (y ^ (1 / 3 : ℝ) - x ^ (1 / 3 : ℝ)) := by
  let u := y ^ (1 / 3 : ℝ)
  let v := x ^ (1 / 3 : ℝ)
  have hu : 0 ≤ u := Real.rpow_nonneg hy.le _
  have hv : 0 ≤ v := Real.rpow_nonneg hx _
  have hu3 : u ^ 3 = y := by
    dsimp only [u]
    rw [rpow_pow_nat y _ hy.le]
    norm_num
  have hv3 : v ^ 3 = x := by
    dsimp only [v]
    rw [rpow_pow_nat x _ hx]
    norm_num
  have hu2 : u ^ 2 = y ^ (2 / 3 : ℝ) := by
    dsimp only [u]
    rw [rpow_pow_nat y _ hy.le]
    congr 1
    norm_num
  have hp := mul_nonneg (sq_nonneg (u - v)) (by positivity : 0 ≤ 2 * u + v)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hy _)).mpr
  rw [← hu2]
  change a ≤ 3 * (u - v) * u ^ 2
  nlinarith only [hp, hu3, hv3, hrec]

theorem sum_range_differences (c : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (c (k + 1) - c k)) = c n - c 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem sum_weight_bound
    (A a : ℕ → ℝ) (n : ℕ) (hA0 : A 0 = 0)
    (hA : ∀ k ≤ n, 0 ≤ A k)
    (hAp : ∀ k < n, 0 < A (k + 1))
    (hrec : ∀ k < n, A (k + 1) = A k + a k) :
    (∑ k ∈ Finset.range n, a k / (A (k + 1)) ^ (2 / 3 : ℝ)) ≤
      3 * (A n) ^ (1 / 3 : ℝ) := by
  have hsum : (∑ k ∈ Finset.range n, a k / (A (k + 1)) ^ (2 / 3 : ℝ)) ≤
      ∑ k ∈ Finset.range n, 3 * ((A (k + 1)) ^ (1 / 3 : ℝ) - (A k) ^ (1 / 3 : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact cube_root_increment_bound (A k) (A (k + 1)) (a k)
      (hA k (by omega)) (hAp k hkn) (hrec k hkn)
  rw [← Finset.mul_sum] at hsum
  rw [sum_range_differences (fun k => (A k) ^ (1 / 3 : ℝ)) n, hA0] at hsum
  norm_num at hsum
  exact hsum

theorem reciprocal_weight_identity
    (A a lam : ℝ) (hA : 0 < A) (ha : 0 < a) (hlam : 0 < lam)
    (hrel : a ^ 2 = lam * A) :
    1 / (a / A ^ (2 / 3 : ℝ)) ^ 6 = A / lam ^ 3 := by
  have hApow : (A ^ (2 / 3 : ℝ)) ^ 6 = A ^ 4 := by
    rw [rpow_pow_nat A _ hA.le]
    norm_num [Real.rpow_natCast]
  have ha6 : a ^ 6 = lam ^ 3 * A ^ 3 := by
    calc
      a ^ 6 = (a ^ 2) ^ 3 := by ring
      _ = (lam * A) ^ 3 := by rw [hrel]
      _ = _ := by ring
  rw [div_pow, hApow, ha6]
  field_simp
  <;> ring

theorem ahpe_weight_growth_squared
    (A a lam : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hA0 : A 0 = 0) (hA : ∀ k ≤ n, 0 ≤ A k)
    (ha : ∀ k < n, 0 < a k) (hlam : ∀ k < n, 0 < lam k)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hrel : ∀ k < n, (a k) ^ 2 = lam k * A (k + 1))
    (hB : 0 ≤ B)
    (hbudget : ∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3 ≤ B) :
    (n : ℝ) ^ 7 ≤ 3 ^ 6 * B * (A n) ^ 2 := by
  let b := fun k => a k / (A (k + 1)) ^ (2 / 3 : ℝ)
  have hAp : ∀ k < n, 0 < A (k + 1) := by
    intro k hk
    rw [hrec k hk]
    exact add_pos_of_nonneg_of_pos (hA k (by omega)) (ha k hk)
  have hb : ∀ k ∈ Finset.range n, 0 < b k := by
    intro k hk
    have hkn := Finset.mem_range.mp hk
    dsimp only [b]
    exact div_pos (ha k hkn) (Real.rpow_pos_of_pos (hAp k hkn) _)
  have hi : (∑ k ∈ Finset.range n, 1 / (b k) ^ 6) =
      ∑ k ∈ Finset.range n, A (k + 1) / (lam k) ^ 3 := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkn := Finset.mem_range.mp hk
    exact reciprocal_weight_identity (A (k + 1)) (a k) (lam k)
      (hAp k hkn) (ha k hkn) (hlam k hkn) (hrel k hkn)
  have ht : ∑ k ∈ Finset.range n, 1 / (b k) ^ 6 ≤ B := by rwa [hi]
  have hs := sum_weight_bound A a n hA0 hA hAp hrec
  have hs0 : 0 ≤ ∑ k ∈ Finset.range n, b k := Finset.sum_nonneg (fun k hk => (hb k hk).le)
  have hh := reciprocal_sixth_moment_bound (Finset.range n) b hb
  simp only [Finset.card_range] at hh
  have hs6 := pow_le_pow_left₀ hs0 hs 6
  have hr : ((A n) ^ (1 / 3 : ℝ)) ^ 6 = (A n) ^ 2 := by
    rw [rpow_pow_nat _ _ (hA n le_rfl)]
    norm_num [Real.rpow_natCast]
  calc
    (n : ℝ) ^ 7 ≤ (∑ k ∈ Finset.range n, b k) ^ 6 *
        ∑ k ∈ Finset.range n, 1 / (b k) ^ 6 := hh
    _ ≤ (∑ k ∈ Finset.range n, b k) ^ 6 * B :=
      mul_le_mul_of_nonneg_left ht (pow_nonneg hs0 _)
    _ ≤ (3 * (A n) ^ (1 / 3 : ℝ)) ^ 6 * B := mul_le_mul_of_nonneg_right hs6 hB
    _ = 3 ^ 6 * B * (A n) ^ 2 := by rw [mul_pow, hr]; ring

end OriginalAHPEWeightGrowth

namespace LargeStepAHPE
open _root_.LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def rateConstant (sigma theta : ℝ) : ℝ :=
  1 + 729 / (4 * theta ^ 2 * (1 - sigma ^ 2))

theorem coarse_square_root_bound (q t K : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hbound : q ^ 2 ≤ K * t ^ 2) : q ≤ (K + 1) * t := by
  by_contra hfail
  have hc : 0 ≤ (K + 1) * t := by positivity
  have hs := (sq_lt_sq₀ hc hq).mpr (lt_of_not_ge hfail)
  have hk : K ≤ (K + 1) ^ 2 := by nlinarith only [sq_nonneg K, hK]
  have hm := mul_le_mul_of_nonneg_right hk (sq_nonneg t)
  rw [mul_pow] at hs
  linarith only [hs, hm, hbound]

theorem gap_rate_from_energy_and_growth
    (G A D M theta sigma : ℝ) (n : ℕ)
    (hG : 0 ≤ G) (hA : 0 ≤ A) (hD : 0 ≤ D) (hM : 0 < M) (htheta : 0 < theta)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hn : 1 ≤ n)
    (henergy : 2 * A * G ≤ D ^ 2)
    (hgrowth : (n : ℝ) ^ 7 ≤ 3 ^ 6 * (M ^ 2 * D ^ 2 / (theta ^ 2 * (1 - sigma ^ 2))) * A ^ 2) :
    G ≤ rateConstant sigma theta * M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  have hden : 0 < theta ^ 2 * (1 - sigma ^ 2) := by positivity
  have hE := (sq_le_sq₀ (by positivity : 0 ≤ 2 * A * G) (sq_nonneg D)).mpr henergy
  have hGrowthClear : (theta ^ 2 * (1 - sigma ^ 2)) * (n : ℝ) ^ 7 ≤
      729 * M ^ 2 * D ^ 2 * A ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hgrowth hden.le
    convert! hh using 1 <;> field_simp <;> ring
  have h1 := mul_le_mul_of_nonneg_right hGrowthClear (by positivity : 0 ≤ 4 * G ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 729 * M ^ 2 * D ^ 2)
  have hcombined : 4 * (theta ^ 2 * (1 - sigma ^ 2)) * G ^ 2 * (n : ℝ) ^ 7 ≤
      729 * M ^ 2 * D ^ 6 := by
    nlinarith only [h1, h2]
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hn
  have hnPow : 0 < (n : ℝ) ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos hnr _
  have hnSq : ((n : ℝ) ^ (7 / 2 : ℝ)) ^ 2 = (n : ℝ) ^ 7 := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (7 / 2 : ℝ)) 2, ← Real.rpow_mul hnr.le]
    norm_num [Real.rpow_natCast]
  let K := 729 / (4 * theta ^ 2 * (1 - sigma ^ 2))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hsq : (G * (n : ℝ) ^ (7 / 2 : ℝ)) ^ 2 ≤ K * (M * D ^ 3) ^ 2 := by
    dsimp only [K]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * theta ^ 2 * (1 - sigma ^ 2))).mpr
    rw [mul_pow, hnSq]
    convert! hcombined using 1 <;> ring
  have hroot := coarse_square_root_bound (G * (n : ℝ) ^ (7 / 2 : ℝ)) (M * D ^ 3) K
    (by positivity) (by positivity) hK hsq
  apply (le_div_iff₀ hnPow).mpr
  convert! hroot using 1 <;> dsimp only [rateConstant, K] <;> ring

theorem large_step_ahpe_convergence
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma theta M D : ℝ) (xstar : E) (n : ℕ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (htheta : 0 < theta) (hM : 0 < M) (hn : 1 ≤ n)
    (hmin : ∀ w : E, g xstar ≤ g w) (hD : ‖x 0 - xstar‖ ≤ D) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2)
    (hlarge : ∀ k < n, theta / M ≤ lam k * ‖y (k + 1) - z k‖) :
    g (y n) - g xstar ≤ rateConstant sigma theta * M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  have hp := prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have he := prefix_energy_and_step_budget g A a lam x y z v err sigma D xstar n
    hsigma0 hsigma1 hmin hD hA0 hlam haformula hrec hz hx hsubgrad hrelative
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  have hb := reciprocal_budget_from_weighted_budget A lam (fun k => ‖y (k + 1) - z k‖) n
    (1 - sigma ^ 2) M theta D halpha hM htheta (fun k hk => (hp.2 k hk).2.1.le)
    hlam (fun k _ => norm_nonneg _) hlarge he.2.2
  have hg := OriginalAHPEWeightGrowth.ahpe_weight_growth_squared A a lam n
    (M ^ 2 * D ^ 2 / (theta ^ 2 * (1 - sigma ^ 2))) hA0 hp.1
    (fun k hk => (hp.2 k hk).1) hlam hrec (fun k hk => (hp.2 k hk).2.2) (by positivity) hb
  exact gap_rate_from_energy_and_growth (g (y n) - g xstar) (A n) D M theta sigma n
    (sub_nonneg.mpr (hmin _)) (hp.1 n le_rfl) (le_trans (norm_nonneg _) hD) hM htheta
    hsigma0 hsigma1 hn he.2.1 hg

end LargeStepAHPE

namespace LargeStepAHPE
open _root_.LargeStepAHPE

theorem rateConstant_positive (sigma theta : ℝ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (htheta : 0 < theta) :
    0 < rateConstant sigma theta := by
  have halpha : 0 < 1 - sigma ^ 2 := by nlinarith only [hsigma0, hsigma1]
  unfold rateConstant
  positivity

end LargeStepAHPE

namespace LargeStepAHPE
open _root_.LargeStepAHPE
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def solutionSet (g : E → ℝ) : Set E := {w | ∀ u : E, g w ≤ g u}

theorem solutionSet_isClosed (g : E → ℝ)
    (hclosed : IsClosed {p : E × ℝ | g p.1 ≤ p.2}) : IsClosed (solutionSet g) := by
  have hlower : LowerSemicontinuous g := lowerSemicontinuous_iff_isClosed_epigraph.mpr hclosed
  have he : solutionSet g = ⋂ u : E, {w : E | g w ≤ g u} := by
    ext w
    simp only [solutionSet, Set.mem_setOf_eq, Set.mem_iInter]
  rw [he]
  exact isClosed_iInter (fun u => hlower.isClosed_preimage (g u))

theorem original_large_step_ahpe_blackbox
    (g : E → ℝ) (A a lam : ℕ → ℝ) (x y z v : ℕ → E) (err : ℕ → ℝ)
    (sigma theta M D : ℝ) (xstar : E) (n : ℕ)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (htheta : 0 < theta) (hM : 0 < M) (hn : 1 ≤ n)
    (hclosed : IsClosed {p : E × ℝ | g p.1 ≤ p.2})
    (hconvex : ConvexOn ℝ (Set.univ : Set E) g)
    (hmin : ∀ w : E, g xstar ≤ g w)
    (hD : Metric.infDist (x 0) (solutionSet g) ≤ D) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k)
    (hz : ∀ k < n, z k = (A k / A (k + 1)) • y k + (a k / A (k + 1)) • x k)
    (hx : ∀ k < n, x (k + 1) = x k - a k • v k)
    (hsubgrad : ∀ k < n, EpsilonSubgradient g (y (k + 1)) (v k) (err k))
    (hrelative : ∀ k < n, ‖lam k • v k + (y (k + 1) - z k)‖ ^ 2 + 2 * lam k * err k ≤
      sigma ^ 2 * ‖y (k + 1) - z k‖ ^ 2)
    (hlarge : ∀ k < n, theta / M ≤ lam k * ‖y (k + 1) - z k‖) :
    g (y n) - g xstar ≤ rateConstant sigma theta * M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  have hne : (solutionSet g).Nonempty := ⟨xstar, hmin⟩
  obtain ⟨w, hw, hdistance⟩ := (solutionSet_isClosed g hclosed).exists_infDist_eq_dist hne (x 0)
  have hDpoint : ‖x 0 - w‖ ≤ D := by
    have he : ‖x 0 - w‖ = Metric.infDist (x 0) (solutionSet g) := by
      simpa only [dist_eq_norm] using hdistance.symm
    rw [he]
    exact hD
  have hminw : ∀ u : E, g w ≤ g u := hw
  have hvalue : g w = g xstar := le_antisymm (hminw xstar) (hmin w)
  have hr := large_step_ahpe_convergence g A a lam x y z v err sigma theta M D w n
    hsigma0 hsigma1 htheta hM hn hminw hDpoint hA0 hlam haformula hrec hz hx hsubgrad hrelative hlarge
  rw [hvalue] at hr
  exact hr

end LargeStepAHPE


namespace OriginalSecondOrderCount
open _root_.OriginalSecondOrderCount

noncomputable def iterations (C M D mu : ℝ) : ℕ :=
  max 1 (Nat.ceil ((8 * C * M * D / mu) ^ (2 / 7 : ℝ)))

theorem rounded_iteration_properties (C M D mu : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D) (hmu : 0 < mu) :
    1 ≤ iterations C M D mu ∧
    (iterations C M D mu : ℝ) ≤ 1 + (8 * C) ^ (2 / 7 : ℝ) * (M * D / mu) ^ (2 / 7 : ℝ) ∧
    8 * C * M * D / mu ≤ (iterations C M D mu : ℝ) ^ (7 / 2 : ℝ) := by
  let x := 8 * C * M * D / mu
  have hx : 0 ≤ x := by dsimp only [x]; positivity
  have hr : 0 ≤ x ^ (2 / 7 : ℝ) := Real.rpow_nonneg hx _
  have hceil := (Nat.ceil_lt_add_one hr).le
  have hroot : x ^ (2 / 7 : ℝ) ≤ (iterations C M D mu : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 (Nat.ceil (x ^ (2 / 7 : ℝ))))
  have hupper : (iterations C M D mu : ℝ) ≤ 1 + x ^ (2 / 7 : ℝ) := by
    unfold iterations
    rw [Nat.cast_max, Nat.cast_one]
    apply max_le
    · linarith only [hr]
    · linarith only [hceil]
  have hfactor : x ^ (2 / 7 : ℝ) =
      (8 * C) ^ (2 / 7 : ℝ) * (M * D / mu) ^ (2 / 7 : ℝ) := by
    have he : x = (8 * C) * (M * D / mu) := by dsimp only [x]; ring
    rw [he, Real.mul_rpow (by positivity) (by positivity)]
  have hpower := Real.rpow_le_rpow hr hroot (by norm_num : (0 : ℝ) ≤ 7 / 2)
  rw [← Real.rpow_mul hx] at hpower
  norm_num only [show (2 / 7 : ℝ) * (7 / 2) = 1 by norm_num, Real.rpow_one] at hpower
  refine ⟨le_max_left _ _, ?_, hpower⟩
  rw [hfactor] at hupper
  exact hupper

theorem contraction_gap_budget (C M D mu : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hD : 0 ≤ D) (hmu : 0 < mu) :
    C * M * D ^ 3 / (iterations C M D mu : ℝ) ^ (7 / 2 : ℝ) ≤ mu * D ^ 2 / 8 := by
  have hp := rounded_iteration_properties C M D mu hC hM hD hmu
  have hn : (0 : ℝ) < (iterations C M D mu : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hp.1
  have hnPow : 0 < (iterations C M D mu : ℝ) ^ (7 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
  have hm := (div_le_iff₀ hmu).mp hp.2.2
  have hDs := mul_le_mul_of_nonneg_right hm (sq_nonneg D)
  apply (div_le_iff₀ hnPow).mpr
  nlinarith only [hDs]

theorem distance_from_contracted_gap (mu D r G : ℝ)
    (hmu : 0 < mu) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hlower : mu / 2 * r ^ 2 ≤ G) (hgap : G ≤ mu * D ^ 2 / 8) :
    r ≤ D / 2 := by
  have hs : r ^ 2 ≤ (D / 2) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hmu).mp
    nlinarith only [hlower, hgap]
  exact (sq_le_sq₀ hr (by positivity)).mp hs

end OriginalSecondOrderCount


namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory

open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure State (E : Type*) where
  weight : ℝ
  x : E
  y : E

noncomputable def settingsAt (c : Settings) (s : State E) : Settings := {c with A := s.weight}
noncomputable def stepProgram (c : Settings) (sigma0 : ℝ) (s : State E) :
    GetterProgram (E × ℝ) (Answer E) (FangqingHysteresis.Outcome (Result E)) :=
  OriginalCertifiedCoupledAHPE.program (settingsAt c s) sigma0 s.x s.y

noncomputable def nextWindow (c : Settings) (s : State E) (b : ℝ) (d : E) (aY : Answer E) : State E :=
  ⟨s.weight + actualWeight (settingsAt c s) b,
    s.x - actualWeight (settingsAt c s) b • aY.grad,
    actualCenter (settingsAt c s) s.x s.y b + d⟩

noncomputable def advanceValue (c : Settings) (s : State E) : FangqingHysteresis.Outcome (Result E) → State E
  | .found (.window b d aY) => nextWindow c s b d aY
  | _ => s

noncomputable def choice (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) :
    FangqingHysteresis.Outcome (Result E) := (execute getter (stepProgram c sigma0 s)).1

noncomputable def advance (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) : State E :=
  advanceValue c s (choice getter c sigma0 s)

noncomputable def states (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : State E :=
  (advance getter c sigma0)^[k] s

theorem states_zero (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) :
    states getter c sigma0 s 0 = s := rfl

theorem states_succ (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) :
    states getter c sigma0 s (k + 1) = advance getter c sigma0 (states getter c sigma0 s k) :=
  Function.iterate_succ_apply' _ _ _

theorem states_shift (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) :
    states getter c sigma0 s (k + 1) = states getter c sigma0 (advance getter c sigma0 s) k :=
  Function.iterate_succ_apply _ _ _

inductive Outcome (E : Type*) where
  | stop (point : E)
  | finished (state : State E)
  | failure

noncomputable def loopProgram (c : Settings) (sigma0 : ℝ) : ℕ → State E → GetterProgram (E × ℝ) (Answer E) (Outcome E)
  | 0, s => .pure (.finished s)
  | n + 1, s => bind (stepProgram c sigma0 s) (fun result => match result with
      | .found (.stop w) => .pure (.stop w)
      | .found (.window b d aY) => loopProgram c sigma0 n (nextWindow c s b d aY)
      | .bracket _ _ => .pure .failure)

def WindowPrefix (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (n : ℕ) : Prop :=
  ∀ k < n, ∃ b d aY, choice getter c sigma0 (states getter c sigma0 s k) = .found (.window b d aY)

theorem settingsAt_common (c : Settings) (hc : CommonLegal c) (s : State E) : CommonLegal (settingsAt c s) :=
  ⟨hc.mu_pos, hc.Lg_nonneg, hc.M_pos, hc.sigma_pos, hc.sigma_lt_one,
    hc.low_pos, hc.low_lt_up, hc.gap, hc.rho_pos⟩

theorem actual_step_is_valid
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 D : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0) (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (s : State E) (hs : 0 ≤ s.weight) :
    ∃ value : Result E, choice getter c sigma0 s = .found value ∧
      ValidOutput g (settingsAt c s) sigma0 D s.x s.y value := by
  let cs := settingsAt c s
  have hcs := settingsAt_common c hc s
  have he := effective_legal cs hcs hs
  have hmarginE : (effective cs).sigma + (effective cs).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up, cs, settingsAt] using hmargin
  have hprecision := outputQueryPrecision_positive (effective cs) he sigma0 hmarginE
  have hbound := OriginalCoupledBetaSearch.observed_bound_is_valid g (effective cs) he getter hgetter s.x (effectiveY cs s.x s.y)
  obtain ⟨value, hrun, hvalid, hcount⟩ := OriginalCoupledGetterProgram.positiveProgram_success_and_getter_calls g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu, cs, settingsAt] using hsc)
    (by simpa only [effective_Lg, cs, settingsAt] using hlip) (by simpa only [effective_M, cs, settingsAt] using hHlip)
    getter hgetter s.x (effectiveY cs s.x s.y)
  exact ⟨value, hrun, valid_search_gives_original_tuple g cs hcs hs sigma0 D _ hmargin hrho
    hbound.1 hC2 hsc hHlip s.x s.y value hvalid⟩

theorem all_states_nonnegative
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (s : State E) (hs : 0 ≤ s.weight) : ∀ k, 0 ≤ (states getter c sigma0 s k).weight := by
  intro k
  induction k with
  | zero => exact hs
  | succ k ih =>
    rw [states_succ]
    obtain ⟨value, hv, hvalid⟩ := hstep _ ih
    cases value with
    | stop w => simpa only [advance, hv, advanceValue] using ih
    | window b d aY =>
      exact (by simpa only [advance, hv, advanceValue, nextWindow, settingsAt] using hvalid.2.2.1.le)

def LoopInvariant (g : E → ℝ) (getter : E × ℝ → Answer E) (c : Settings)
    (sigma0 D : ℝ) (s : State E) (n : ℕ) : Outcome E → Prop
  | .stop w => ‖w - RobustAHPE.globalMinimizer g‖ ≤ D / 2
  | .finished final => final = states getter c sigma0 s n ∧ WindowPrefix getter c sigma0 s n
  | .failure => False

theorem loop_actual_execution_prefix
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (n : ℕ) (s : State E) (hs : 0 ≤ s.weight) :
    LoopInvariant g getter c sigma0 D s n (execute getter (loopProgram c sigma0 n s)).1 := by
  induction n generalizing s with
  | zero => exact ⟨rfl, by intro k hk; omega⟩
  | succ n ih =>
    obtain ⟨value, hvalue, hvalid⟩ := hstep s hs
    have hrun := execute_bind getter (stepProgram c sigma0 s)
      (fun result => match result with
        | .found (.stop w) => _root_.OriginalBetaATSTrial.GetterProgram.pure (.stop w)
        | .found (.window b d aY) => loopProgram c sigma0 n (nextWindow c s b d aY)
        | .bracket _ _ => _root_.OriginalBetaATSTrial.GetterProgram.pure .failure)
    change (execute getter (stepProgram c sigma0 s)).1 = .found value at hvalue
    cases value with
    | stop w =>
      simpa only [loopProgram, execute_bind, hvalue, execute, LoopInvariant, ValidOutput] using hvalid
    | window b d aY =>
      have hnext : 0 ≤ (nextWindow c s b d aY).weight := hvalid.2.2.1.le
      have hi := ih (nextWindow c s b d aY) hnext
      have hadv : advance getter c sigma0 s = nextWindow c s b d aY := by
        unfold advance choice
        rw [hvalue]
        rfl
      simp only [loopProgram, execute_bind, hvalue] at hi ⊢
      cases hout : (execute getter (loopProgram c sigma0 n (nextWindow c s b d aY))).1 with
      | failure => simpa only [hout, LoopInvariant] using hi
      | stop w => simpa only [hout, LoopInvariant] using hi
      | finished final =>
        simp only [hout, LoopInvariant] at hi ⊢
        refine ⟨by rw [states_shift, hadv]; exact hi.1, ?_⟩
        intro k hk
        cases k with
        | zero => exact ⟨b, d, aY, hvalue⟩
        | succ k =>
          rw [states_shift, hadv]
          exact hi.2 k (by omega)

end OriginalRobustTrajectory

namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure Frame (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  beta : ℝ
  displacement : E
  answer : Answer E

noncomputable def record : FangqingHysteresis.Outcome (Result E) → Frame E
  | .found (.window b d aY) => ⟨b, d, aY⟩
  | _ => ⟨0, 0, ⟨0, 0⟩⟩

noncomputable def frames (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : Frame E :=
  record (choice getter c sigma0 (states getter c sigma0 s k))

noncomputable def weights (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  (states getter c sigma0 s k).weight
noncomputable def increments (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  actualWeight (settingsAt c (states getter c sigma0 s k)) (frames getter c sigma0 s k).beta
noncomputable def lambdas (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  actualLambda (settingsAt c (states getter c sigma0 s k)) (frames getter c sigma0 s k).beta
noncomputable def xpoints (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  (states getter c sigma0 s k).x
noncomputable def ypoints (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  (states getter c sigma0 s k).y
noncomputable def centers (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  actualCenter (settingsAt c (states getter c sigma0 s k)) (states getter c sigma0 s k).x
    (states getter c sigma0 s k).y (frames getter c sigma0 s k).beta
noncomputable def vectors (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : E :=
  (frames getter c sigma0 s k).answer.grad
noncomputable def errors (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ) (s : State E) (k : ℕ) : ℝ :=
  outputTolerance (effective (settingsAt c (states getter c sigma0 s k))) sigma0 ^ 2 / (2 * c.mu)

theorem actual_prefix_is_ahpe
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (s : State E) (hs : 0 ≤ s.weight) (n : ℕ) (hp : WindowPrefix getter c sigma0 s n) :
    ∀ k < n,
      0 < lambdas getter c sigma0 s k ∧
      increments getter c sigma0 s k =
        (lambdas getter c sigma0 s k + Real.sqrt (lambdas getter c sigma0 s k ^ 2 +
          4 * lambdas getter c sigma0 s k * weights getter c sigma0 s k)) / 2 ∧
      weights getter c sigma0 s (k + 1) = weights getter c sigma0 s k + increments getter c sigma0 s k ∧
      centers getter c sigma0 s k =
        (weights getter c sigma0 s k / weights getter c sigma0 s (k + 1)) • ypoints getter c sigma0 s k +
          (increments getter c sigma0 s k / weights getter c sigma0 s (k + 1)) • xpoints getter c sigma0 s k ∧
      xpoints getter c sigma0 s (k + 1) = xpoints getter c sigma0 s k -
        increments getter c sigma0 s k • vectors getter c sigma0 s k ∧
      LargeStepAHPE.EpsilonSubgradient g (ypoints getter c sigma0 s (k + 1))
        (vectors getter c sigma0 s k) (errors getter c sigma0 s k) ∧
      ‖lambdas getter c sigma0 s k • vectors getter c sigma0 s k +
        (ypoints getter c sigma0 s (k + 1) - centers getter c sigma0 s k)‖ ^ 2 +
          2 * lambdas getter c sigma0 s k * errors getter c sigma0 s k ≤
            sigma0 ^ 2 * ‖ypoints getter c sigma0 s (k + 1) - centers getter c sigma0 s k‖ ^ 2 ∧
      c.sigmaLow / c.M ≤ lambdas getter c sigma0 s k *
        ‖ypoints getter c sigma0 s (k + 1) - centers getter c sigma0 s k‖ := by
  intro k hk
  obtain ⟨b, d, aY, hout⟩ := hp k hk
  obtain ⟨value, hvalue, hvalid⟩ := hstep (states getter c sigma0 s k)
    (all_states_nonnegative g c sigma0 D getter hstep s hs k)
  have heq : value = .window b d aY := FangqingHysteresis.Outcome.found.inj (hvalue.symm.trans hout)
  rw [heq] at hvalid
  rcases hvalid with ⟨hlam, ha, hAnew, hz, hsub, hrel, hlarge⟩
  have hnext : states getter c sigma0 s (k + 1) = nextWindow c (states getter c sigma0 s k) b d aY := by
    rw [states_succ]
    unfold advance
    rw [hout]
    rfl
  simp only [lambdas, increments, weights, centers, xpoints, ypoints, vectors, errors,
    frames, record, hout, hnext, nextWindow, settingsAt, add_sub_cancel_left]
  exact ⟨hlam, rfl, True.intro, hz, True.intro, hsub, hrel, hlarge⟩

end OriginalRobustTrajectory

namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def contractionIterations (c : Settings) (sigma0 D : ℝ) : ℕ :=
  OriginalSecondOrderCount.iterations (LargeStepAHPE.rateConstant sigma0 c.sigmaLow) c.M D c.mu

noncomputable def resultPoint : Outcome E → E
  | .stop w => w
  | .finished s => s.y
  | .failure => 0

theorem actual_prefix_gap_rate
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (hsigma0 : 0 < sigma0) (hsigma1 : sigma0 < 1)
    (htheta : 0 < c.sigmaLow) (hM : 0 < c.M)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (xstar start : E) (hmin : ∀ w : E, g xstar ≤ g w) (hD : ‖start - xstar‖ ≤ D)
    (n : ℕ) (hn : 1 ≤ n) (hp : WindowPrefix getter c sigma0 ⟨0, start, start⟩ n) :
    g (ypoints getter c sigma0 ⟨0, start, start⟩ n) - g xstar ≤
      LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * D ^ 3 / (n : ℝ) ^ (7 / 2 : ℝ) := by
  let initial : State E := ⟨0, start, start⟩
  have hpref := actual_prefix_is_ahpe g c sigma0 D getter hstep initial (by norm_num [initial]) n hp
  exact LargeStepAHPE.large_step_ahpe_convergence g
    (weights getter c sigma0 initial) (increments getter c sigma0 initial) (lambdas getter c sigma0 initial)
    (xpoints getter c sigma0 initial) (ypoints getter c sigma0 initial) (centers getter c sigma0 initial)
    (vectors getter c sigma0 initial) (errors getter c sigma0 initial)
    sigma0 c.sigmaLow c.M D xstar n hsigma0 hsigma1 htheta hM hn hmin hD rfl
    (fun k hk => (hpref k hk).1) (fun k hk => (hpref k hk).2.1)
    (fun k hk => (hpref k hk).2.2.1) (fun k hk => (hpref k hk).2.2.2.1)
    (fun k hk => (hpref k hk).2.2.2.2.1) (fun k hk => (hpref k hk).2.2.2.2.2.1)
    (fun k hk => (hpref k hk).2.2.2.2.2.2.1) (fun k hk => (hpref k hk).2.2.2.2.2.2.2)

theorem actual_finite_second_order_contraction
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 D : ℝ) (hD : 0 < D)
    (hmargin : c.sigma + c.sigmaUp < sigma0) (hsigma1 : sigma0 < 1)
    (hrho : c.rho = c.mu * D / 2)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    ‖resultPoint (execute getter (loopProgram c sigma0 (contractionIterations c sigma0 D) ⟨0, start, start⟩)).1 -
        RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      (contractionIterations c sigma0 D : ℝ) ≤
        1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
          (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  have hstep := actual_step_is_valid g c hc sigma0 D hmargin hrho hC2 hsc hlip hHlip getter hgetter
  have hup : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hsigma0 : 0 < sigma0 := lt_trans (add_pos hc.sigma_pos hup) hmargin
  have hC := LargeStepAHPE.rateConstant_positive sigma0 c.sigmaLow hsigma0 hsigma1 hc.low_pos
  have hn := OriginalSecondOrderCount.rounded_iteration_properties
    (LargeStepAHPE.rateConstant sigma0 c.sigmaLow) c.M D c.mu hC.le hc.M_pos.le hD.le hc.mu_pos
  have hrun := loop_actual_execution_prefix g c sigma0 D getter hstep
    (contractionIterations c sigma0 D) ⟨0, start, start⟩ (by norm_num)
  refine ⟨?_, hn.2.1⟩
  generalize hout : (execute getter (loopProgram c sigma0 (contractionIterations c sigma0 D) ⟨0, start, start⟩)).1 = out at hrun ⊢
  cases out with
  | stop w => exact hrun
  | failure => exact False.elim hrun
  | finished final =>
    have hgap := actual_prefix_gap_rate g c sigma0 D hsigma0 hsigma1 hc.low_pos hc.M_pos getter hstep
      (RobustAHPE.globalMinimizer g) start
      (RobustAHPE.globalMinimizer_is_actual g c.mu hc.mu_pos (hC2.differentiable (by norm_num)) hsc)
      hstart (contractionIterations c sigma0 D) hn.1 hrun.2
    have hbudget := OriginalSecondOrderCount.contraction_gap_budget
      (LargeStepAHPE.rateConstant sigma0 c.sigmaLow) c.M D c.mu hC.le hc.M_pos.le hD.le hc.mu_pos
    have hmin := RobustAHPE.globalMinimizer_is_actual g c.mu hc.mu_pos (hC2.differentiable (by norm_num)) hsc
    have hzero := PacketCore.gradient_eq_zero_at_global_min g (RobustAHPE.globalMinimizer g) hmin
    have hlower := PacketCore.strongConvex_support g c.mu hsc (hC2.differentiable (by norm_num))
      (RobustAHPE.globalMinimizer g) final.y
    rw [hzero, inner_zero_left, add_zero] at hlower
    have hfinal : ypoints getter c sigma0 ⟨0, start, start⟩ (contractionIterations c sigma0 D) = final.y :=
      congrArg State.y hrun.1.symm
    rw [hfinal] at hgap
    exact OriginalSecondOrderCount.distance_from_contracted_gap c.mu D ‖final.y - RobustAHPE.globalMinimizer g‖
      (g final.y - g (RobustAHPE.globalMinimizer g)) hc.mu_pos hD.le (norm_nonneg _)
      (by linarith only [hlower]) (hgap.trans hbudget)

end OriginalRobustTrajectory


namespace OriginalCoupledSearchExtended
open _root_.OriginalCoupledSearchExtended
open OriginalCoupledBetaAlgebra
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints
open OriginalCoupledBetaSearch
open OriginalBetaATSTrial (Answer TrialResult)
open FangqingHysteresis (Decision Outcome)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def NonterminalGradient (g : E → ℝ) (c : Settings) (x y : E) : Result E → Prop
  | .stop _ => True
  | .window b d _ => c.rho / 2 < ‖gradient g (center x y b + d)‖

def ExtendedValidResult (g : E → ℝ) (c : Settings) (G deltaY : ℝ) (x y : E) (value : Result E) : Prop :=
  ValidResult g c G deltaY x y value ∧ NonterminalGradient g c x y value

theorem classified_accept_nonterminal
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    NonterminalGradient g c x y value := by
  classical
  have ht := interval_trial_spec g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb
  have hl := interval_lambda_bounds c hc G hG0 b hb
  cases hr : OriginalBetaATSTrial.trial getter c.M (lambda c.A b) (tolerance c G) c.rho deltaY (center x y b) with
  | stop w =>
    simp only [classifiedTrial, hr] at haccept
    have hv := Decision.accept.inj haccept
    rw [← hv]
    rw [hr] at ht
    exact True.intro
  | step d aY =>
    rw [hr] at ht
    by_cases hw : c.sigmaLow / c.M ≤ lambda c.A b * ‖d‖ ∧ lambda c.A b * ‖d‖ ≤ c.sigmaUp / c.M
    · simp only [classifiedTrial, hr, if_pos hw] at haccept
      have hv := Decision.accept.inj haccept
      rw [← hv]
      exact ht.2.2
    · simp only [classifiedTrial, hr, if_neg hw] at haccept
      split_ifs at haccept <;> cases haccept

theorem classified_accept_valid_extended
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (hb : b ∈ Set.Icc (lower c G) (upper c))
    (value : Result E) (haccept : classifiedTrial getter c G deltaY x y b = .accept value) :
    ExtendedValidResult g c G deltaY x y value := by
  exact ⟨classified_accept_valid g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value haccept,
    classified_accept_nonterminal g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value haccept⟩

theorem bisection_after_endpoints_extended
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G)
    (hleft : classifiedTrial getter c G deltaY x y (lower c G) = .low)
    (hright : classifiedTrial getter c G deltaY x y (upper c) = .high) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).1 = .found value ∧
      ExtendedValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y)
        (FangqingHysteresis.bisect (fuel c G x y) (lower c G) (upper c))).2 ≤ fuel c G x y := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  have hK := actual_modulus_spec g c hc G hG0 hC2 hsc hlip hHlip x y hG
  exact FangqingHysteresis.bisection_success_and_calls
    (classifiedTrial getter c G deltaY x y) (betaSize g c.M c.A x y) (ExtendedValidResult g c G deltaY x y)
    (thresholdLow c) (thresholdHigh c) (lower c G) (upper c) (modulus c G x y)
    (threshold_gap c hc) hK.1 hp.2.2.2.2.2.2.1
    (classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL hleft)
    (classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU hright)
    hK.2
    (fun b hb value hv => classified_accept_valid_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb value hv)
    (fun b hb hv => classified_low_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)
    (fun b hb hv => classified_high_threshold g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y b hb hv)


theorem positive_search_success_and_calls_extended
    (g : E → ℝ) (c : Settings) (hc : Legal c) (G deltaY : ℝ) (hG0 : 0 ≤ G)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (hG : gradientBound g c.Lg x y ≤ G) :
    ∃ value : Result E,
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).1 = .found value ∧
      ExtendedValidResult g c G deltaY x y value ∧
      (FangqingHysteresis.execute (classifiedTrial getter c G deltaY x y) (searchProgram c G x y)).2 ≤ fuel c G x y + 2 := by
  have hp := compact_properties c hc G hG0
  have hbL : lower c G ∈ Set.Icc (lower c G) (upper c) := ⟨le_rfl, hp.2.2.2.2.2.2.1⟩
  have hbU : upper c ∈ Set.Icc (lower c G) (upper c) := ⟨hp.2.2.2.2.2.2.1, le_rfl⟩
  cases hleft : classifiedTrial getter c G deltaY x y (lower c G) with
  | accept value =>
    refine ⟨value, ?_, ?_, ?_⟩
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
    · exact classified_accept_valid_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbL value hleft
    · simp only [searchProgram, FangqingHysteresis.execute, hleft]
      omega
  | high => exact False.elim (lower_endpoint_not_high g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y hG hleft)
  | low =>
    cases hright : classifiedTrial getter c G deltaY x y (upper c) with
    | accept value =>
      refine ⟨value, ?_, ?_, ?_⟩
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
      · exact classified_accept_valid_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip getter hgetter x y _ hbU value hright
      · simp only [searchProgram, FangqingHysteresis.execute, hleft, hright]
        omega
    | low => exact False.elim (upper_endpoint_not_low g c hc G deltaY hG0 hdeltaY hdeltaYsmall hC2 hsc hlip hHlip getter hgetter x y hright)
    | high =>
      obtain ⟨value, hrun, hvalid, hcount⟩ := bisection_after_endpoints_extended g c hc G deltaY hG0 hdeltaY hdeltaYsmall
        hC2 hsc hlip hHlip getter hgetter x y hG hleft hright
      refine ⟨value, ?_, hvalid, ?_⟩
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright] using hrun
      · simpa only [searchProgram, FangqingHysteresis.execute, hleft, hright, Nat.add_assoc] using Nat.add_le_add_right hcount 2


theorem positiveProgram_found_window_has_nonterminal_gradient
    (g : E → ℝ) (c : Settings) (hc : Legal c) (deltaY : ℝ)
    (hdeltaY : 0 < deltaY) (hdeltaYsmall : deltaY ≤ c.rho / 8)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (x y : E) (b : ℝ) (d : E) (aY : Answer E)
    (hfound : (OriginalBetaATSTrial.execute getter
      (OriginalCoupledGetterProgram.positiveProgram c deltaY x y)).1 = .found (.window b d aY)) :
    c.rho / 2 < ‖gradient g (center x y b + d)‖ := by
  have hbound := observed_bound_is_valid g c hc getter hgetter x y
  obtain ⟨value, hrun, hv, _⟩ := positive_search_success_and_calls_extended g c hc
    (observedGradientBound getter c x y) deltaY hbound.1 hdeltaY hdeltaYsmall
    hC2 hsc hlip hHlip getter hgetter x y hbound.2
  have hp := (OriginalCoupledGetterProgram.positiveProgram_result_and_count getter c deltaY x y).1
  have heq := FangqingHysteresis.Outcome.found.inj ((hp.symm.trans hfound).symm.trans hrun)
  rw [← heq] at hv
  exact hv.2

end OriginalCoupledSearchExtended


namespace OriginalAcceptedLambdaLowerBound
open _root_.OriginalAcceptedLambdaLowerBound
open OriginalTaylorProxStability
open OriginalBetaCurveBounds
open OriginalBetaSearchEndpoints

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def lambdaFloor (mu M sigma sigmaLow G : ℝ) : ℝ :=
  sigmaLow * mu * (1 - sigma) / (M * (1 + G))

theorem lambdaFloor_positive (mu M sigma sigmaLow G : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hsigma : sigma < 1) (hLow : 0 < sigmaLow) (hG : 0 ≤ G) :
    0 < lambdaFloor mu M sigma sigmaLow G := by dsimp [lambdaFloor]; positivity

theorem accepted_lambda_lower_bound_from_gradient
    (g : E → ℝ) (mu M lam sigma sigmaLow G : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hlam : 0 < lam) (hsigma : sigma < 1) (hG0 : 0 ≤ G)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (z d : E) (hG : ‖gradient g z‖ ≤ G)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : sigmaLow / M ≤ lam * ‖d‖) :
    lambdaFloor mu M sigma sigmaLow G ≤ lam := by
  have hsize := exactStep_size_bound (gradient g z) (fderiv ℝ (gradient g) z) M lam mu
    hM.le hlam hmu.le (CertifiedATS.actual_hessian_coercive g hC2 mu hsc z)
  have hn : 0 ≤ lam⁻¹ * ‖actualStep g M z lam‖ := by positivity
  change (mu + lam⁻¹) * ‖actualStep g M z lam‖ ≤ _ at hsize
  have hexact : mu * ‖actualStep g M z lam‖ ≤ G := by nlinarith only [hsize, hG, hn]
  have hbr := (actual_approximate_norm_bracket g mu M lam sigma hmu hM.le hlam hC2 hsc z d hATS).1
  have hb : (1 - sigma) * ‖d‖ ≤ ‖actualStep g M z lam‖ := by
    apply (mul_le_mul_iff_right₀ hlam).mp
    nlinarith only [hbr]
  have hnorm : mu * (1 - sigma) * ‖d‖ ≤ G := by
    have hh := mul_le_mul_of_nonneg_left hb hmu.le
    nlinarith only [hh, hexact]
  have hw := (div_le_iff₀ hM).mp hwindow
  have hwm := mul_le_mul_of_nonneg_left hw (show 0 ≤ mu * (1 - sigma) by positivity)
  have hnm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ lam * M by positivity)
  have hsmall : sigmaLow * mu * (1 - sigma) ≤ lam * M * G := by nlinarith only [hwm, hnm]
  unfold lambdaFloor
  apply (div_le_iff₀ (by positivity : 0 < M * (1 + G))).mpr
  have hp : 0 ≤ lam * M := by positivity
  nlinarith only [hsmall, hp]

theorem first_step_lambda_lower_bound_from_actual_minimizer
    (g : E → ℝ) (mu Lg M lam sigma sigmaLow D : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 < M) (hlam : 0 < lam)
    (hsigma : sigma < 1) (hD : 0 ≤ D)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ Lg * ‖z - w‖)
    (z zstar d : E) (hmin : ∀ w : E, g zstar ≤ g w) (hdist : ‖z - zstar‖ ≤ D)
    (hATS : ‖lam • CertifiedATS.trueVector (gradient g z) (fderiv ℝ (gradient g) z) M d + d‖ ≤ sigma * ‖d‖)
    (hwindow : sigmaLow / M ≤ lam * ‖d‖) :
    lambdaFloor mu M sigma sigmaLow (Lg * D) ≤ lam := by
  have hz := PacketCore.gradient_eq_zero_at_global_min g zstar hmin
  have hG : ‖gradient g z‖ ≤ Lg * D := by
    have hh := (hlip z zstar).trans (mul_le_mul_of_nonneg_left hdist hLg)
    simpa only [hz, sub_zero] using hh
  exact accepted_lambda_lower_bound_from_gradient g mu M lam sigma sigmaLow (Lg * D)
    hmu hM hlam hsigma (mul_nonneg hLg hD) hC2 hsc z d hG hATS hwindow

end OriginalAcceptedLambdaLowerBound


namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_window_facts
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (s : State E) (hs : 0 ≤ s.weight) (b : ℝ) (d : E) (aY : Answer E)
    (hout : choice getter c sigma0 s = .found (.window b d aY)) :
    0 < b ∧ b < 1 ∧ 0 < actualLambda (settingsAt c s) b ∧
      c.sigmaLow / c.M ≤ actualLambda (settingsAt c s) b * ‖d‖ ∧
      actualLambda (settingsAt c s) b * ‖d‖ ≤ c.sigmaUp / c.M ∧
      ‖actualLambda (settingsAt c s) b • CertifiedATS.trueVector
        (gradient g (actualCenter (settingsAt c s) s.x s.y b))
        (fderiv ℝ (gradient g) (actualCenter (settingsAt c s) s.x s.y b)) c.M d + d‖ ≤ c.sigma * ‖d‖ ∧
      c.rho / 2 < ‖gradient g (actualCenter (settingsAt c s) s.x s.y b + d)‖ := by
  let cs := settingsAt c s
  have hcs := settingsAt_common c hc s
  have he := effective_legal cs hcs hs
  have hmarginE : (effective cs).sigma + (effective cs).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up, cs, settingsAt] using hmargin
  have hprecision := outputQueryPrecision_positive (effective cs) he sigma0 hmarginE
  obtain ⟨value, hrun, hv, hcount⟩ := OriginalCoupledGetterProgram.positiveProgram_success_and_getter_calls g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu, cs, settingsAt] using hsc)
    (by simpa only [effective_Lg, cs, settingsAt] using hlip)
    (by simpa only [effective_M, cs, settingsAt] using hHlip)
    getter hgetter s.x (effectiveY cs s.x s.y)
  have hfound : (execute getter (OriginalCoupledGetterProgram.positiveProgram (effective cs)
      (outputQueryPrecision (effective cs) sigma0) s.x (effectiveY cs s.x s.y))).1 = .found (.window b d aY) := hout
  have heq : value = .window b d aY := FangqingHysteresis.Outcome.found.inj (hrun.symm.trans hfound)
  rw [heq] at hv
  have haway := OriginalCoupledSearchExtended.positiveProgram_found_window_has_nonterminal_gradient g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    hC2 (by simpa only [effective_mu, cs, settingsAt] using hsc)
    (by simpa only [effective_Lg, cs, settingsAt] using hlip)
    (by simpa only [effective_M, cs, settingsAt] using hHlip)
    getter hgetter s.x (effectiveY cs s.x s.y) b d aY hfound
  rcases hv with ⟨hb, hb0, hb1, hlam, hlow, hhigh, hATS, herr, hweight, hcenter⟩
  refine ⟨hb0, hb1, hlam, ?_, ?_, ?_, ?_⟩
  · simpa only [actualLambda, effective_low, effective_M, cs, settingsAt] using hlow
  · simpa only [actualLambda, effective_up, effective_M, cs, settingsAt] using hhigh
  · simpa only [actualLambda, actualCenter, effective_M, effective_sigma, cs, settingsAt] using hATS
  · simpa only [actualCenter, effective_rho, cs, settingsAt] using haway

noncomputable def lambdaCap (c : Settings) : ℝ :=
  1 + 2 * ((1 + c.sigma + c.sigmaUp) * c.sigmaUp) / (c.M * c.rho)

theorem lambdaCap_positive (c : Settings) (hc : CommonLegal c) : 0 < lambdaCap c := by
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hM := hc.M_pos
  have hrho := hc.rho_pos
  have hsigma := hc.sigma_pos
  unfold lambdaCap
  positivity

theorem actual_window_lambda_cap
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 : ℝ)
    (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (s : State E) (hs : 0 ≤ s.weight) (b : ℝ) (d : E) (aY : Answer E)
    (hout : choice getter c sigma0 s = .found (.window b d aY)) :
    actualLambda (settingsAt c s) b ≤ lambdaCap c := by
  have h := actual_window_facts g c hc sigma0 hmargin hC2 hsc hlip hHlip getter hgetter s hs b d aY hout
  let lam := actualLambda (settingsAt c s) b
  let K := 2 * ((1 + c.sigma + c.sigmaUp) * c.sigmaUp) / (c.M * c.rho)
  have hu : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hM := hc.M_pos
  have hrho := hc.rho_pos
  have hsigma := hc.sigma_pos
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlam : 0 < lam := h.2.2.1
  have hend := RobustAHPE.large_lambda_gradient_endpoint g hC2 c.M lam c.sigma c.sigmaUp
    hc.M_pos hlam hc.sigma_pos.le hu.le hHlip
    (actualCenter (settingsAt c s) s.x s.y b) d h.2.2.2.2.2.1 h.2.2.2.2.1
  have he := (le_div_iff₀ (mul_pos hc.M_pos (sq_pos_of_pos hlam))).mp hend
  have haw := mul_lt_mul_of_pos_right h.2.2.2.2.2.2 (mul_pos hc.M_pos (sq_pos_of_pos hlam))
  have hsquare : lam ^ 2 < K := by
    apply (lt_div_iff₀ (mul_pos hc.M_pos hc.rho_pos)).mpr
    nlinarith only [he, haw]
  change lam ≤ 1 + K
  by_cases hsmall : lam ≤ 1
  · linarith only [hsmall, hK]
  · have hlarge : 1 < lam := lt_of_not_ge hsmall
    have hsq : lam ≤ lam ^ 2 := by nlinarith only [hlarge]
    linarith only [hsq, hsquare]

noncomputable def firstWeightFloor (c : Settings) (D : ℝ) : ℝ :=
  OriginalAcceptedLambdaLowerBound.lambdaFloor c.mu c.M c.sigma c.sigmaLow (c.Lg * D)

theorem firstWeightFloor_positive (c : Settings) (hc : CommonLegal c) (D : ℝ) (hD : 0 ≤ D) :
    0 < firstWeightFloor c D :=
  OriginalAcceptedLambdaLowerBound.lambdaFloor_positive c.mu c.M c.sigma c.sigmaLow (c.Lg * D)
    hc.mu_pos hc.M_pos hc.sigma_lt_one hc.low_pos (mul_nonneg hc.Lg_nonneg hD)

theorem actual_first_window_weight_lower
    (g : E → ℝ) (c : Settings) (hc : CommonLegal c) (sigma0 D : ℝ) (hD : 0 ≤ D)
    (hmargin : c.sigma + c.sigmaUp < sigma0)
    (hC2 : ContDiff ℝ 2 g) (hsc : StrongConvexOn (Set.univ : Set E) c.mu g)
    (hlip : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖)
    (hHlip : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖)
    (getter : E × ℝ → Answer E)
    (hgetter : ∀ z : E, ∀ eta : ℝ, 0 < eta →
      ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
      ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta)
    (start xstar : E) (hmin : ∀ w : E, g xstar ≤ g w) (hdist : ‖start - xstar‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hout : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY)) :
    firstWeightFloor c D ≤ (states getter c sigma0 ⟨0, start, start⟩ 1).weight := by
  let initial : State E := ⟨0, start, start⟩
  have hf := actual_window_facts g c hc sigma0 hmargin hC2 hsc hlip hHlip getter hgetter initial (by norm_num [initial]) b d aY hout
  have hcenter : actualCenter (settingsAt c initial) start start b = start := by
    unfold actualCenter effectiveY
    split_ifs <;> exact OriginalFirstCoupledStep.center_same start b
  have hATS := hf.2.2.2.2.2.1
  change ‖actualLambda (settingsAt c initial) b • CertifiedATS.trueVector
    (gradient g (actualCenter (settingsAt c initial) start start b))
    (fderiv ℝ (gradient g) (actualCenter (settingsAt c initial) start start b)) c.M d + d‖ ≤ c.sigma * ‖d‖ at hATS
  rw [hcenter] at hATS
  have hell := OriginalAcceptedLambdaLowerBound.first_step_lambda_lower_bound_from_actual_minimizer g
    c.mu c.Lg c.M (actualLambda (settingsAt c initial) b) c.sigma c.sigmaLow D
    hc.mu_pos hc.Lg_nonneg hc.M_pos hf.2.2.1 hc.sigma_lt_one hD hC2 hsc hlip
    start xstar d hmin hdist hATS hf.2.2.2.1
  have hweight : actualWeight (settingsAt c initial) b = actualLambda (settingsAt c initial) b := by
    exact (OriginalCoupledBetaAlgebra.zero_weight_first_step (actualLambda (settingsAt c initial) b)
      hf.2.2.1 start start).1
  rw [states_succ]
  simp only [states_zero, advance, hout, advanceValue, nextWindow, initial, zero_add]
  rw [hweight]
  exact hell

end OriginalRobustTrajectory


namespace FangqingGetterComposition
open _root_.FangqingGetterComposition
open OriginalBetaATSTrial

theorem baseCost_bind {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ)
    (p : GetterProgram Q A R) (next : R → GetterProgram Q A S) :
    baseCost getter cost (bind p next) =
      baseCost getter cost p + baseCost getter cost (next (execute getter p).1) := by
  induction p with
  | pure r => simp only [bind, baseCost, execute, Nat.zero_add]
  | ask q cont ih => simp only [bind, baseCost, execute, ih, Nat.add_assoc]

end FangqingGetterComposition

namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem loop_actual_weighted_cost_bound
    (getter : E × ℝ → Answer E) (cost : E × ℝ → ℕ) (c : Settings) (sigma0 : ℝ)
    (n C : ℕ) (s : State E)
    (hcost : ∀ k < n, baseCost getter cost (stepProgram c sigma0 (states getter c sigma0 s k)) ≤ C) :
    baseCost getter cost (loopProgram c sigma0 n s) ≤ C * n := by
  induction n generalizing s with
  | zero => simp only [loopProgram, baseCost, Nat.mul_zero, le_refl]
  | succ n ih =>
    have hfirst := hcost 0 (by omega)
    change baseCost getter cost (stepProgram c sigma0 s) ≤ C at hfirst
    rw [loopProgram, baseCost_bind]
    cases hout : (execute getter (stepProgram c sigma0 s)).1 with
    | bracket l r =>
      simp only [baseCost]
      nlinarith only [hfirst]
    | found value =>
      cases value with
      | stop w =>
        simp only [baseCost]
        nlinarith only [hfirst]
      | window b d aY =>
        have hadv : advance getter c sigma0 s = nextWindow c s b d aY := by
          unfold advance choice
          rw [hout]
          rfl
        have ht : ∀ k < n, baseCost getter cost
            (stepProgram c sigma0 (states getter c sigma0 (nextWindow c s b d aY) k)) ≤ C := by
          intro k hk
          have h := hcost (k + 1) (by omega)
          rw [states_shift, hadv] at h
          exact h
        have htail := ih (nextWindow c s b d aY) ht
        nlinarith only [hfirst, htail]

theorem all_state_weights_nondecreasing
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (s : State E) (hs : 0 ≤ s.weight) :
    Monotone (fun k => (states getter c sigma0 s k).weight) := by
  apply monotone_nat_of_le_succ
  intro k
  obtain ⟨value, hv, hvalid⟩ := hstep _ (all_states_nonnegative g c sigma0 D getter hstep s hs k)
  rw [states_succ]
  cases value with
  | stop w => simp only [advance, hv, advanceValue, le_refl]
  | window b d aY =>
    change (states getter c sigma0 s k).weight ≤ _
    simp only [advance, hv, advanceValue, nextWindow]
    exact le_add_of_nonneg_right hvalid.2.1.le

theorem window_energy_decreases
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (hsigma0 : 0 < sigma0) (hsigma1 : sigma0 < 1)
    (s : State E) (hs : 0 ≤ s.weight) (b : ℝ) (d : E) (aY : Answer E)
    (hvalid : ValidOutput g (settingsAt c s) sigma0 D s.x s.y (.window b d aY)) (xstar : E) :
    LargeStepAHPE.potential g (nextWindow c s b d aY).weight (nextWindow c s b d aY).x
      (nextWindow c s b d aY).y xstar ≤ LargeStepAHPE.potential g s.weight s.x s.y xstar := by
  rcases hvalid with ⟨hlam, ha, hAnew, hz, hsub, hrel, hlarge⟩
  let lam := actualLambda (settingsAt c s) b
  let a := actualWeight (settingsAt c s) b
  let z := actualCenter (settingsAt c s) s.x s.y b
  have htotal : 0 < s.weight + a := hAnew
  have hscaled : (s.weight + a) • z = s.weight • s.y + a • s.x := by
    have hcoef1 : (s.weight + a) * (s.weight / (s.weight + a)) = s.weight := by
      field_simp [ne_of_gt htotal]
    have hcoef2 : (s.weight + a) * (a / (s.weight + a)) = a := by
      field_simp [ne_of_gt htotal]
    change z = (s.weight / (s.weight + a)) • s.y + (a / (s.weight + a)) • s.x at hz
    rw [hz, smul_add, smul_smul, smul_smul, hcoef1, hcoef2]
  have haformula : a = (lam + Real.sqrt (lam ^ 2 + 4 * lam * s.weight)) / 2 := rfl
  have hsquare := LargeStepAHPE.a_formula_properties s.weight lam hs hlam
  dsimp only at hsquare
  rw [← haformula] at hsquare
  have hrelative : ‖lam • aY.grad + ((z + d) - z)‖ ^ 2 +
      2 * lam * (outputTolerance (effective (settingsAt c s)) sigma0 ^ 2 / (2 * c.mu)) ≤
        sigma0 ^ 2 * ‖(z + d) - z‖ ^ 2 := by simpa only [add_sub_cancel_left, settingsAt, lam] using hrel
  have hp := LargeStepAHPE.one_step_potential g s.weight (s.weight + a) a lam sigma0
    (outputTolerance (effective (settingsAt c s)) sigma0 ^ 2 / (2 * c.mu))
    s.x s.y (s.x - a • aY.grad) (z + d) z aY.grad xstar hs hAnew ha.le hlam rfl hsquare.2.2
    hscaled rfl hsub hrelative
  have hnonneg : 0 ≤ (1 - sigma0 ^ 2) / 2 * ((s.weight + a) / lam) * ‖(z + d) - z‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by nlinarith only [hsigma0, hsigma1]) (div_nonneg hAnew.le hlam.le)) (sq_nonneg _)
  exact le_trans hp (sub_le_self _ hnonneg)

theorem all_state_energy_bound
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (hsigma0 : 0 < sigma0) (hsigma1 : sigma0 < 1)
    (getter : E × ℝ → Answer E)
    (hstep : ∀ s : State E, 0 ≤ s.weight → ∃ value : Result E,
      choice getter c sigma0 s = .found value ∧ ValidOutput g (settingsAt c s) sigma0 D s.x s.y value)
    (xstar start : E) (hD : ‖start - xstar‖ ≤ D) :
    ∀ k, LargeStepAHPE.potential g (states getter c sigma0 ⟨0, start, start⟩ k).weight
      (states getter c sigma0 ⟨0, start, start⟩ k).x
      (states getter c sigma0 ⟨0, start, start⟩ k).y xstar ≤ D ^ 2 / 2 := by
  intro k
  induction k with
  | zero =>
    dsimp only [states, Function.iterate_zero, id_eq, LargeStepAHPE.potential]
    nlinarith only [hD, norm_nonneg (start - xstar)]
  | succ k ih =>
    have hs := all_states_nonnegative g c sigma0 D getter hstep ⟨0, start, start⟩ (by norm_num) k
    obtain ⟨value, hv, hvalid⟩ := hstep _ hs
    rw [states_succ]
    cases value with
    | stop w => simpa only [advance, hv, advanceValue] using ih
    | window b d aY =>
      have hp := window_energy_decreases g c sigma0 D hsigma0 hsigma1 _ hs b d aY hvalid xstar
      simpa only [advance, hv, advanceValue] using hp.trans ih

theorem x_radius_from_energy (g : E → ℝ) (A D : ℝ) (x y xstar : E)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hmin : ∀ w : E, g xstar ≤ g w)
    (henergy : LargeStepAHPE.potential g A x y xstar ≤ D ^ 2 / 2) : ‖x - xstar‖ ≤ D := by
  have hgap : 0 ≤ g y - g xstar := sub_nonneg.mpr (hmin y)
  have hprod := mul_nonneg hA hgap
  dsimp only [LargeStepAHPE.potential] at henergy
  have hsq : ‖x - xstar‖ ^ 2 ≤ D ^ 2 := by nlinarith only [henergy, hprod]
  exact (sq_le_sq₀ (norm_nonneg _) hD).mp hsq

noncomputable def geometryRadius (mu ell D : ℝ) : ℝ := D * (1 + (mu * ell)⁻¹)

theorem y_radius_from_energy (g : E → ℝ) (mu ell A D : ℝ)
    (hmu : 0 < mu) (hell : 0 < ell) (hA : ell ≤ A) (hD : 0 ≤ D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (x y xstar : E) (hmin : ∀ w : E, g xstar ≤ g w)
    (henergy : LargeStepAHPE.potential g A x y xstar ≤ D ^ 2 / 2) :
    ‖y - xstar‖ ≤ geometryRadius mu ell D := by
  have hg0 := PacketCore.gradient_eq_zero_at_global_min g xstar hmin
  have hlower := PacketCore.strongConvex_support g mu hsc hdiff xstar y
  rw [hg0, inner_zero_left, add_zero] at hlower
  have hm := mul_le_mul_of_nonneg_left hlower hell.le
  have hgap : 0 ≤ g y - g xstar := sub_nonneg.mpr (hmin y)
  have hprod := mul_le_mul_of_nonneg_right hA hgap
  dsimp only [LargeStepAHPE.potential] at henergy
  have hbase : mu * ell * ‖y - xstar‖ ^ 2 ≤ D ^ 2 := by
    nlinarith only [hm, hprod, henergy, sq_nonneg ‖x - xstar‖]
  have ht : 0 < mu * ell := mul_pos hmu hell
  have hinv : 0 < (mu * ell)⁻¹ := inv_pos.mpr ht
  have hid : mu * ell * (geometryRadius mu ell D) ^ 2 =
      D ^ 2 * (mu * ell + 2 + (mu * ell)⁻¹) := by
    unfold geometryRadius
    field_simp
    <;> ring
  have hR : D ≤ geometryRadius mu ell D := by
    unfold geometryRadius
    nlinarith only [hD, mul_nonneg hD hinv.le]
  have htarget : D ^ 2 ≤ mu * ell * (geometryRadius mu ell D) ^ 2 := by
    rw [hid]
    nlinarith only [sq_nonneg D, mul_nonneg (sq_nonneg D) (add_nonneg ht.le hinv.le)]
  have hsq : ‖y - xstar‖ ^ 2 ≤ geometryRadius mu ell D ^ 2 :=
    (mul_le_mul_iff_right₀ ht).mp (hbase.trans htarget)
  exact (sq_le_sq₀ (norm_nonneg _) (hD.trans hR)).mp hsq

end OriginalRobustTrajectory


namespace OriginalAHPEWeightUpper
open _root_.OriginalAHPEWeightUpper

theorem one_step_weight_upper (lam Lambda A : ℝ) (k : ℕ)
    (hlam : 0 < lam) (hLam : lam ≤ Lambda) (hA : 0 ≤ A)
    (hbound : A ≤ Lambda * (k : ℝ) ^ 2) :
    let a := (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2
    a ≤ Lambda * ((k : ℝ) + 1) ∧
      A + a ≤ Lambda * (((k + 1 : ℕ) : ℝ) ^ 2) := by
  dsimp only
  have hLambda : 0 < Lambda := lt_of_lt_of_le hlam hLam
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hrad : 0 ≤ lam ^ 2 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (lam ^ 2 + 4 * lam * A)
  have hprod := mul_le_mul hLam hbound hA hLambda.le
  have hsq := (sq_le_sq₀ hlam.le hLambda.le).mpr hLam
  have htarget : 0 ≤ Lambda * (2 * (k : ℝ) + 1) := by positivity
  have hradup : lam ^ 2 + 4 * lam * A ≤ (Lambda * (2 * (k : ℝ) + 1)) ^ 2 := by
    nlinarith only [hprod, hsq, mul_nonneg (sq_nonneg Lambda) hk]
  have hroot : Real.sqrt (lam ^ 2 + 4 * lam * A) ≤ Lambda * (2 * (k : ℝ) + 1) := by
    nlinarith only [hs, hn, htarget, hradup]
  have ha : (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2 ≤ Lambda * ((k : ℝ) + 1) := by
    linarith only [hroot, hLam]
  refine ⟨ha, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith only [ha, hbound, mul_nonneg hLambda.le hk]

theorem prefix_weight_upper_bound (A a lam : ℕ → ℝ) (n : ℕ) (Lambda : ℝ)
    (hLambda : 0 < Lambda) (hA0 : A 0 = 0)
    (hlam : ∀ k < n, 0 < lam k) (hlamUpper : ∀ k < n, lam k ≤ Lambda)
    (haformula : ∀ k < n, a k = (lam k + Real.sqrt ((lam k) ^ 2 + 4 * lam k * A k)) / 2)
    (hrec : ∀ k < n, A (k + 1) = A k + a k) :
    (∀ k ≤ n, A k ≤ Lambda * (k : ℝ) ^ 2) ∧
      (∀ k < n, a k ≤ Lambda * ((k : ℝ) + 1)) := by
  have hp := LargeStepAHPE.prefix_parameter_properties A a lam n hA0 hlam haformula hrec
  have hweight : ∀ k ≤ n, A k ≤ Lambda * (k : ℝ) ^ 2 := by
    intro k
    induction k with
    | zero => intro _; norm_num [hA0]
    | succ k ih =>
        intro hk
        have hkn : k < n := by omega
        have hs := one_step_weight_upper (lam k) Lambda (A k) k (hlam k hkn) (hlamUpper k hkn)
          (hp.1 k (by omega)) (ih (by omega))
        dsimp only at hs
        rw [← haformula k hkn, ← hrec k hkn] at hs
        exact hs.2
  refine ⟨hweight, ?_⟩
  intro k hk
  have hs := one_step_weight_upper (lam k) Lambda (A k) k (hlam k hk) (hlamUpper k hk)
    (hp.1 k (by omega)) (hweight k (by omega))
  dsimp only at hs
  rw [← haformula k hk] at hs
  exact hs.1

end OriginalAHPEWeightUpper


namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalFirstCoupledStep (CommonLegal)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

structure Hypotheses (g : E → ℝ) (c : Settings) (sigma0 D : ℝ) (getter : E × ℝ → Answer E) : Prop where
  common : CommonLegal c
  D_pos : 0 < D
  margin : c.sigma + c.sigmaUp < sigma0
  sigma_lt_one : sigma0 < 1
  rho_eq : c.rho = c.mu * D / 2
  C2 : ContDiff ℝ 2 g
  strongly_convex : StrongConvexOn (Set.univ : Set E) c.mu g
  gradient_lipschitz : ∀ z w : E, ‖gradient g z - gradient g w‖ ≤ c.Lg * ‖z - w‖
  hessian_lipschitz : ∀ z w : E, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ c.M * ‖z - w‖
  getter_correct : ∀ z : E, ∀ eta : ℝ, 0 < eta →
    ‖(getter (z, eta)).grad - gradient g z‖ ≤ eta ∧
    ‖(getter (z, eta)).hess - fderiv ℝ (gradient g) z‖ ≤ eta

theorem Hypotheses.sigma_positive {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) : 0 < sigma0 :=
  lt_trans (add_pos H.common.sigma_pos (H.common.low_pos.trans H.common.low_lt_up)) H.margin

theorem Hypotheses.step_valid {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) : ∀ s : State E, 0 ≤ s.weight →
      ∃ value : Result E, choice getter c sigma0 s = .found value ∧
        ValidOutput g (settingsAt c s) sigma0 D s.x s.y value :=
  actual_step_is_valid g c H.common sigma0 D H.margin H.rho_eq H.C2 H.strongly_convex
    H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct

theorem Hypotheses.actual_minimum {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) : ∀ w : E, g (RobustAHPE.globalMinimizer g) ≤ g w :=
  RobustAHPE.globalMinimizer_is_actual g c.mu H.common.mu_pos (H.C2.differentiable (by norm_num)) H.strongly_convex

noncomputable def effectiveWeightFloor (c : Settings) (D : ℝ) : ℝ := min 1 (firstWeightFloor c D)
noncomputable def stateRadius (c : Settings) (D : ℝ) : ℝ := geometryRadius c.mu (firstWeightFloor c D) D
noncomputable def weightCeiling (c : Settings) (n : ℕ) : ℝ := 1 + lambdaCap c * (n : ℝ) ^ 2
noncomputable def observedCeiling (c : Settings) (D : ℝ) : ℝ := 2 + c.Lg * (D + 2 * stateRadius c D)

theorem stateRadius_ge_D (c : Settings) (hc : CommonLegal c) (D : ℝ) (hD : 0 ≤ D) : D ≤ stateRadius c D := by
  have hell := firstWeightFloor_positive c hc D hD
  have hinv : 0 ≤ (c.mu * firstWeightFloor c D)⁻¹ := inv_nonneg.mpr (mul_nonneg hc.mu_pos.le hell.le)
  unfold stateRadius geometryRadius
  nlinarith only [mul_nonneg hD hinv]

theorem actual_state_weight_upper
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E) :
    ∀ k, (states getter c sigma0 ⟨0, start, start⟩ k).weight ≤ lambdaCap c * (k : ℝ) ^ 2 := by
  intro k
  induction k with
  | zero => simp only [states_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, le_refl]
  | succ k ih =>
    let s := states getter c sigma0 ⟨0, start, start⟩ k
    have hs := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
    obtain ⟨value, hv, hvalid⟩ := H.step_valid s hs
    have hvalue := hv
    dsimp only [s] at hvalue
    rw [states_succ]
    cases value with
    | stop w =>
      simp only [advance, hvalue, advanceValue]
      have hm : (k : ℝ) ^ 2 ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
        push_cast
        nlinarith only [(show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
      exact ih.trans (mul_le_mul_of_nonneg_left hm (lambdaCap_positive c H.common).le)
    | window b d aY =>
      have hcap := actual_window_lambda_cap g c H.common sigma0 H.margin H.C2 H.strongly_convex
        H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct s hs b d aY hv
      have hup := OriginalAHPEWeightUpper.one_step_weight_upper
        (actualLambda (settingsAt c s) b) (lambdaCap c) s.weight k hvalid.1 hcap hs ih
      dsimp only at hup
      simp only [advance, hvalue, advanceValue, nextWindow]
      exact hup.2

theorem actual_state_geometry_after_first_window
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hfirst : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY)) :
    ∀ k,
      ‖(states getter c sigma0 ⟨0, start, start⟩ k).x - RobustAHPE.globalMinimizer g‖ ≤ D ∧
      ‖(states getter c sigma0 ⟨0, start, start⟩ k).y - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D ∧
      (1 ≤ k → firstWeightFloor c D ≤ (states getter c sigma0 ⟨0, start, start⟩ k).weight) := by
  have hfloor := actual_first_window_weight_lower g c H.common sigma0 D H.D_pos.le H.margin H.C2 H.strongly_convex
    H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct start (RobustAHPE.globalMinimizer g)
    H.actual_minimum hstart b d aY hfirst
  have hmono := all_state_weights_nondecreasing g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num)
  have henergy := all_state_energy_bound g c sigma0 D H.sigma_positive H.sigma_lt_one getter H.step_valid
    (RobustAHPE.globalMinimizer g) start hstart
  have hell := firstWeightFloor_positive c H.common D H.D_pos.le
  intro k
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have hx := x_radius_from_energy g _ D _ _ (RobustAHPE.globalMinimizer g) hA H.D_pos.le H.actual_minimum (henergy k)
  have hweight : 1 ≤ k → firstWeightFloor c D ≤ (states getter c sigma0 ⟨0, start, start⟩ k).weight :=
    fun hk => hfloor.trans (hmono hk)
  refine ⟨hx, ?_, hweight⟩
  cases k with
  | zero => exact hstart.trans (stateRadius_ge_D c H.common D H.D_pos.le)
  | succ k =>
    exact y_radius_from_energy g c.mu (firstWeightFloor c D) _ D H.common.mu_pos hell (hweight (by omega)) H.D_pos.le
      (H.C2.differentiable (by norm_num)) H.strongly_convex _ _ (RobustAHPE.globalMinimizer g) H.actual_minimum (henergy _)

theorem effective_weight_interval
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hfirst : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY))
    (n k : ℕ) (hk : k ≤ n) :
    0 < effectiveWeightFloor c D ∧
      effectiveWeightFloor c D ≤ (effective (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))).A ∧
      (effective (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))).A ≤ weightCeiling c n := by
  have hell := firstWeightFloor_positive c H.common D H.D_pos.le
  have hgeometry := actual_state_geometry_after_first_window H start hstart b d aY hfirst k
  have hupper := actual_state_weight_upper H start k
  have hcap := lambdaCap_positive c H.common
  have hsq : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    apply (sq_le_sq₀ (Nat.cast_nonneg k) (Nat.cast_nonneg n)).mpr
    exact_mod_cast hk
  refine ⟨lt_min (by norm_num) hell, ?_, ?_⟩
  · unfold effective
    split_ifs with hz
    · exact min_le_left _ _
    · have hkn : 1 ≤ k := by
        by_contra hbad
        have hk0 : k = 0 := by omega
        subst k
        exact hz rfl
      exact (min_le_right _ _).trans (hgeometry.2.2 hkn)
  · unfold effective
    split_ifs
    · change 1 ≤ 1 + lambdaCap c * (n : ℝ) ^ 2
      have hp := mul_nonneg hcap.le (sq_nonneg (n : ℝ))
      linarith only [hp]
    · exact hupper.trans ((mul_le_mul_of_nonneg_left hsq hcap.le).trans (by unfold weightCeiling; linarith))

theorem actual_observed_gradient_upper
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (b : ℝ) (d : E) (aY : Answer E)
    (hfirst : choice getter c sigma0 ⟨0, start, start⟩ = .found (.window b d aY)) (k : ℕ) :
    0 ≤ getterBound getter (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))
      (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y ∧
    getterBound getter (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))
      (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y ≤ observedCeiling c D := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let w := effectiveY (settingsAt c s) s.x s.y
  have hgeom := actual_state_geometry_after_first_window H start hstart b d aY hfirst k
  have hR := stateRadius_ge_D c H.common D H.D_pos.le
  have hw : ‖w - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D := by
    dsimp only [w, effectiveY]
    split_ifs
    · exact hgeom.1.trans hR
    · exact hgeom.2.1
  have hg0 := PacketCore.gradient_eq_zero_at_global_min g (RobustAHPE.globalMinimizer g) H.actual_minimum
  have hG : ‖gradient g w‖ ≤ c.Lg * stateRadius c D := by
    have hh := (H.gradient_lipschitz w (RobustAHPE.globalMinimizer g)).trans (mul_le_mul_of_nonneg_left hw H.common.Lg_nonneg)
    simpa only [hg0, sub_zero] using hh
  have herr := (H.getter_correct w 1 (by norm_num)).1
  have hnorm := (norm_le_norm_sub_add (getter (w, 1)).grad (gradient g w)).trans (add_le_add herr hG)
  have hxy : ‖s.x - w‖ ≤ D + stateRadius c D :=
    (norm_sub_le_norm_sub_add_norm_sub s.x (RobustAHPE.globalMinimizer g) w).trans
      (add_le_add hgeom.1 (by simpa only [norm_sub_rev] using hw))
  have hproduct := mul_le_mul_of_nonneg_left hxy H.common.Lg_nonneg
  have hLg := H.common.Lg_nonneg
  simp only [getterBound, OriginalCoupledBetaSearch.observedGradientBound, effective_Lg, settingsAt]
  constructor
  · change 0 ≤ ‖(getter (w, 1)).grad‖ + 1 + c.Lg * ‖s.x - w‖
    positivity
  · change ‖(getter (w, 1)).grad‖ + 1 + c.Lg * ‖s.x - w‖ ≤ observedCeiling c D
    unfold observedCeiling
    nlinarith only [hnorm, hproduct]

end OriginalRobustTrajectory

namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings Result)
open OriginalCertifiedCoupledAHPE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

def ResourceScene (g : E → ℝ) (getter : E × ℝ → Answer E) (c : Settings)
    (D : ℝ) (n : ℕ) (s : State E) : Prop :=
  0 < effectiveWeightFloor c D ∧
    effectiveWeightFloor c D ≤ (effective (settingsAt c s)).A ∧
    (effective (settingsAt c s)).A ≤ weightCeiling c n ∧
    0 ≤ getterBound getter (settingsAt c s) s.x s.y ∧
    getterBound getter (settingsAt c s) s.x s.y ≤ observedCeiling c D ∧
    ‖s.x - RobustAHPE.globalMinimizer g‖ ≤ D ∧
    ‖s.y - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D

theorem actual_resources_on_stream
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    ∀ k ≤ n, ResourceScene g getter c D n (states getter c sigma0 ⟨0, start, start⟩ k) := by
  let initial : State E := ⟨0, start, start⟩
  obtain ⟨value, hv, hvalid⟩ := H.step_valid initial (by norm_num [initial])
  cases value with
  | window b d aY =>
    intro k hk
    have hA := effective_weight_interval H start hstart b d aY hv n k hk
    have hG := actual_observed_gradient_upper H start hstart b d aY hv k
    have hgeom := actual_state_geometry_after_first_window H start hstart b d aY hv k
    exact ⟨hA.1, hA.2.1, hA.2.2, hG.1, hG.2, hgeom.1, hgeom.2.1⟩
  | stop w =>
    have hadv : advance getter c sigma0 initial = initial := by
      unfold advance
      rw [hv]
      rfl
    have hfixed : ∀ k, states getter c sigma0 initial k = initial := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [states_succ, ih]; exact hadv
    have hell := firstWeightFloor_positive c H.common D H.D_pos.le
    have hR := stateRadius_ge_D c H.common D H.D_pos.le
    have hR0 : 0 ≤ stateRadius c D := H.D_pos.le.trans hR
    have hcap := lambdaCap_positive c H.common
    have hgradzero := PacketCore.gradient_eq_zero_at_global_min g (RobustAHPE.globalMinimizer g) H.actual_minimum
    have hGtrue : ‖gradient g start‖ ≤ c.Lg * D := by
      have h := (H.gradient_lipschitz start (RobustAHPE.globalMinimizer g)).trans
        (mul_le_mul_of_nonneg_left hstart H.common.Lg_nonneg)
      simpa only [hgradzero, sub_zero] using h
    have hnorm := (norm_le_norm_sub_add (getter (start, 1)).grad (gradient g start)).trans
      (add_le_add (H.getter_correct start 1 (by norm_num)).1 hGtrue)
    have hget : getterBound getter (settingsAt c initial) initial.x initial.y = ‖(getter (start, 1)).grad‖ + 1 := by
      simp only [getterBound, OriginalCoupledBetaSearch.observedGradientBound, effective_Lg,
        effectiveY, settingsAt, initial, ite_true, if_pos rfl, sub_self, norm_zero, mul_zero, add_zero]
    have hAeff : (effective (settingsAt c initial)).A = 1 := by
      simp only [effective, settingsAt, initial, ite_true, if_pos rfl, OriginalFirstCoupledStep.proxySettings]
    intro k hk
    change ResourceScene g getter c D n (states getter c sigma0 initial k)
    rw [hfixed]
    refine ⟨lt_min (by norm_num) hell, ?_, ?_, ?_, ?_, hstart, hstart.trans hR⟩
    · rw [hAeff]
      exact min_le_left _ _
    · rw [hAeff]
      change 1 ≤ 1 + lambdaCap c * (n : ℝ) ^ 2
      have hprod := mul_nonneg hcap.le (sq_nonneg (n : ℝ))
      linarith only [hprod]
    · rw [hget]
      positivity
    · rw [hget]
      unfold observedCeiling
      have hprod := mul_nonneg H.common.Lg_nonneg hR0
      nlinarith only [hnorm, hprod]

end OriginalRobustTrajectory


namespace OriginalUniformBetaResources
open _root_.OriginalUniformBetaResources

open OriginalCoupledBetaSearch OriginalBetaSearchEndpoints OriginalBetaATSUniform

noncomputable section

def betaFloor (c : Settings) (Amax Gmax : ℝ) : ℝ :=
  betaLow Amax (lambdaLow c.M c.sigmaLow c.sigma Gmax)

def marginFloor (c : Settings) (Amin : ℝ) : ℝ :=
  highMargin Amin (lambdaHigh c.M c.rho c.sigma c.sigmaUp)

def lambdaFloor (c : Settings) (Amin Amax Gmax : ℝ) : ℝ :=
  Amin * betaFloor c Amax Gmax ^ 2

def lambdaCeiling (c : Settings) (Amax : ℝ) : ℝ :=
  4 * Amax + 8 * (1 + lambdaHigh c.M c.rho c.sigma c.sigmaUp)

theorem endpoint_bounds (c : Settings) (hc : Legal c) (Amin Amax Gmax G : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) :
    0 < betaFloor c Amax Gmax ∧ betaFloor c Amax Gmax ≤ lower c G ∧
    0 < marginFloor c Amin ∧ marginFloor c Amin ≤ margin c ∧
    0 < lambdaFloor c Amin Amax Gmax ∧ lambdaFloor c Amin Amax Gmax ≤ lambdaMin c G ∧
    0 < lambdaCeiling c Amax ∧ lambdaMax c ≤ lambdaCeiling c Amax := by
  have hA := hc.A_pos
  have hM := hc.M_pos
  have hAmax : 0 < Amax := hc.A_pos.trans_le hAhi
  have hGmax : 0 ≤ Gmax := hG.trans hGhi
  let H := lambdaHigh c.M c.rho c.sigma c.sigmaUp
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have hH : 0 ≤ H := by
    dsimp only [H, lambdaHigh]
    have hM := hc.M_pos
    have hrho := hc.rho_pos
    have hsigma := hc.sigma_pos
    positivity
  have hell := lambdaLow_positive c.M c.sigmaLow c.sigma Gmax hc.M_pos hc.low_pos hc.sigma_lt_one hGmax
  have hbeta := (betaLow_properties Amax _ hAmax hell.1).1
  have hellMono : lambdaLow c.M c.sigmaLow c.sigma Gmax ≤ lambdaLow c.M c.sigmaLow c.sigma G := by
    unfold lambdaLow
    apply min_le_min le_rfl
    apply div_le_div_of_nonneg_left (by
      have hh := hc.low_pos
      have hs := hc.sigma_lt_one
      positivity) (by
        have hh := hc.M_pos
        positivity)
    have hh := mul_le_mul_of_nonneg_left hGhi (by positivity : 0 ≤ 2 * c.M)
    nlinarith only [hh]
  have hbetaBound : betaFloor c Amax Gmax ≤ lower c G := by
    unfold betaFloor lower betaLow
    apply min_le_min le_rfl
    calc
      _ ≤ lambdaLow c.M c.sigmaLow c.sigma Gmax / (4 * (1 + c.A)) :=
        div_le_div_of_nonneg_left hell.1.le (by positivity) (by linarith only [hAhi])
      _ ≤ _ := div_le_div_of_nonneg_right hellMono (by positivity)
  have hmargin : 0 < marginFloor c Amin := by
    unfold marginFloor highMargin
    change 0 < min (1 / 4 : ℝ) (Amin / (8 * (1 + H)))
    positivity
  have hmarginBound : marginFloor c Amin ≤ margin c := by
    unfold marginFloor margin highMargin
    apply min_le_min le_rfl
    exact div_le_div_of_nonneg_right hAlo (by change 0 ≤ 8 * (1 + H); positivity)
  have hp := compact_properties c hc G hG
  have hsq := (sq_le_sq₀ hbeta.le hp.1.le).mpr hbetaBound
  have hlambdaFloor : 0 < lambdaFloor c Amin Amax Gmax := by
    unfold lambdaFloor
    exact mul_pos hAmin (sq_pos_of_pos hbeta)
  have hloBound : lambdaFloor c Amin Amax Gmax ≤ lambdaMin c G :=
    mul_le_mul hAlo hsq (sq_nonneg _) hc.A_pos.le
  have hceiling : 0 < lambdaCeiling c Amax := by
    change 0 < 4 * Amax + 8 * (1 + H)
    positivity
  have hmaxBound : lambdaMax c ≤ lambdaCeiling c Amax := by
    unfold lambdaMax margin highMargin
    change c.A / min (1 / 4 : ℝ) (c.A / (8 * (1 + H))) ≤ 4 * Amax + 8 * (1 + H)
    rcases le_total (1 / 4 : ℝ) (c.A / (8 * (1 + H))) with hleft | hright
    · rw [min_eq_left hleft]
      norm_num
      nlinarith only [hAhi, hH]
    · rw [min_eq_right hright]
      have hid : c.A / (c.A / (8 * (1 + H))) = 8 * (1 + H) := by
        field_simp [ne_of_gt hc.A_pos]
      rw [hid]
      linarith only [hAmax]
  exact ⟨hbeta, hbetaBound, hmargin, hmarginBound, hlambdaFloor, hloBound, hceiling, hmaxBound⟩

theorem uniform_tolerance_mono
    (mu Lg M lo up lo' up' sigma rho : ℝ)
    (hmu : 0 < mu) (hLg : 0 ≤ Lg) (hM : 0 ≤ M)
    (hlo : 0 < lo) (hlole : lo ≤ lo') (hup' : 0 < up') (huple : up' ≤ up)
    (hsigma : 0 < sigma) (hrho : 0 < rho) :
    uniformTolerance mu Lg M lo up sigma rho ≤ uniformTolerance mu Lg M lo' up' sigma rho := by
  have hstep := uniformStepFloor_le mu Lg M lo lo' rho hmu hLg hM hlo hlole hrho
  change uniformStepFloor mu Lg M lo rho ≤ uniformStepFloor mu Lg M lo' rho at hstep
  have hstep0 := (uniformStepFloor_positive mu Lg M lo rho hmu hLg hM hlo hrho).le
  have hterm : sigma * uniformStepFloor mu Lg M lo rho / (2 * up) ≤
      sigma * uniformStepFloor mu Lg M lo' rho / (2 * up') := by
    calc
      _ ≤ sigma * uniformStepFloor mu Lg M lo rho / (2 * up') :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [huple])
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hsigma.le) (by positivity)
  have hterm4 : sigma / (2 * up) ≤ sigma / (2 * up') :=
    div_le_div_of_nonneg_left hsigma.le (by positivity) (by linarith only [huple])
  exact min_le_min le_rfl (min_le_min le_rfl (min_le_min hterm hterm4))

def centerPrecisionFloor (c : Settings) (Amin Amax Gmax : ℝ) : ℝ :=
  uniformTolerance c.mu c.Lg c.M (lambdaFloor c Amin Amax Gmax) (lambdaCeiling c Amax) c.sigma c.rho

theorem center_precision_bounds (c : Settings) (hc : Legal c) (Amin Amax Gmax G : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) :
    0 < centerPrecisionFloor c Amin Amax Gmax ∧
      centerPrecisionFloor c Amin Amax Gmax ≤ tolerance c G := by
  have he := endpoint_bounds c hc Amin Amax Gmax G hAmin hAlo hAhi hG hGhi
  have hp := compact_properties c hc G hG
  refine ⟨uniformTolerance_positive c.mu c.Lg c.M _ _ c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le he.2.2.2.2.1 he.2.2.2.2.2.2.1 hc.sigma_pos hc.rho_pos, ?_⟩
  exact uniform_tolerance_mono c.mu c.Lg c.M _ _ _ _ c.sigma c.rho hc.mu_pos hc.Lg_nonneg
    hc.M_pos.le he.2.2.2.2.1 he.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2 he.2.2.2.2.2.2.2 hc.sigma_pos hc.rho_pos

theorem uniform_output_tolerance_antitone (mu M up up' eta sigmaL : ℝ)
    (hmu : 0 < mu) (hM : 0 < M) (hup' : 0 < up') (huple : up' ≤ up)
    (heta : 0 ≤ eta) (hsigmaL : 0 ≤ sigmaL) :
    RobustAHPE.uniformOutputGradientTolerance mu M up eta sigmaL ≤
      RobustAHPE.uniformOutputGradientTolerance mu M up' eta sigmaL := by
  have hup : 0 < up := hup'.trans_le huple
  have hc := RobustAHPE.output_tolerance_coefficient_antitone mu up' up hmu.le hup' huple
  have hc0 : 0 ≤ min up⁻¹ (min 1 (mu / up)) := by positivity
  unfold RobustAHPE.uniformOutputGradientTolerance
  calc
    _ ≤ eta * sigmaL * min up⁻¹ (min 1 (mu / up)) / (M * up') :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left huple hM.le)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (mul_nonneg heta hsigmaL)) (by positivity)

def outputPrecisionFloor (c : Settings) (Amax sigma0 : ℝ) : ℝ :=
  min (c.rho / 8) (RobustAHPE.uniformOutputGradientTolerance c.mu c.M (lambdaCeiling c Amax)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow)

theorem output_precision_bounds (c : Settings) (hc : Legal c) (Amax sigma0 : ℝ)
    (hAhi : c.A ≤ Amax) (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < outputPrecisionFloor c Amax sigma0 ∧
      outputPrecisionFloor c Amax sigma0 ≤ OriginalCertifiedCoupledAHPE.outputQueryPrecision c sigma0 := by
  have he := endpoint_bounds c hc c.A Amax 0 0 hc.A_pos le_rfl hAhi le_rfl le_rfl
  have hp := compact_properties c hc 0 le_rfl
  have hUp : 0 < c.sigmaUp := hc.low_pos.trans hc.low_lt_up
  have heta := (RobustAHPE.chosenSlack_properties (c.sigma + c.sigmaUp) sigma0
    (add_nonneg hc.sigma_pos.le hUp.le) hmargin).1
  have htol := RobustAHPE.uniformOutputGradientTolerance_positive c.mu c.M (lambdaCeiling c Amax)
    (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
    hc.mu_pos hc.M_pos he.2.2.2.2.2.2.1 heta hc.low_pos
  refine ⟨lt_min (div_pos hc.rho_pos (by norm_num)) htol, ?_⟩
  exact min_le_min le_rfl (uniform_output_tolerance_antitone c.mu c.M (lambdaCeiling c Amax)
    (lambdaMax c) (RobustAHPE.chosenSlack (c.sigma + c.sigmaUp) sigma0) c.sigmaLow
    hc.mu_pos hc.M_pos hp.2.2.2.2.2.2.2.2 he.2.2.2.2.2.2.2 heta.le hc.low_pos.le)

def queryPrecisionFloor (c : Settings) (Amin Amax Gmax sigma0 : ℝ) : ℝ :=
  min 1 (min (centerPrecisionFloor c Amin Amax Gmax) (outputPrecisionFloor c Amax sigma0))

theorem all_query_precision_bounds (c : Settings) (hc : Legal c) (Amin Amax Gmax G sigma0 : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) (hmargin : c.sigma + c.sigmaUp < sigma0) :
    0 < queryPrecisionFloor c Amin Amax Gmax sigma0 ∧
      queryPrecisionFloor c Amin Amax Gmax sigma0 ≤
        OriginalCoupledGetterProgram.precisionFloor c G
          (OriginalCertifiedCoupledAHPE.outputQueryPrecision c sigma0) := by
  have hcTol := center_precision_bounds c hc Amin Amax Gmax G hAmin hAlo hAhi hG hGhi
  have hoTol := output_precision_bounds c hc Amax sigma0 hAhi hmargin
  exact ⟨lt_min zero_lt_one (lt_min hcTol.1 hoTol.1),
    min_le_min le_rfl (min_le_min hcTol.2 hoTol.2)⟩

def modulusCeiling (c : Settings) (Amin Amax Gmax Dmax : ℝ) : ℝ :=
  let T := 2 * Amax / marginFloor c Amin ^ 2
  let I := T / lambdaFloor c Amin Amax Gmax ^ 2
  T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
    ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)

theorem size_modulus_uniform_bound (c : Settings) (hc : Legal c) (Amin Amax Gmax G D Dmax : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) (hD : 0 ≤ D) (hDhi : D ≤ Dmax) :
    0 ≤ modulusCeiling c Amin Amax Gmax Dmax ∧
      OriginalBetaCurveBounds.sizeModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G D ≤
        modulusCeiling c Amin Amax Gmax Dmax := by
  have he := endpoint_bounds c hc Amin Amax Gmax G hAmin hAlo hAhi hG hGhi
  rcases he with ⟨hb0, hb, ht0, ht, hlo0, hlo, hup0, hup⟩
  have hp := compact_properties c hc G hG
  have hA := hc.A_pos
  have hmu := hc.mu_pos
  have hM := hc.M_pos
  have hLg := hc.Lg_nonneg
  have hAmax : 0 < Amax := hc.A_pos.trans_le hAhi
  have hGmax : 0 ≤ Gmax := hG.trans hGhi
  have hDmax : 0 ≤ Dmax := hD.trans hDhi
  have hm : 0 < margin c := hp.2.2.1
  have hl : 0 < lambdaMin c G := hp.2.2.2.2.2.2.2.1
  let T := 2 * Amax / marginFloor c Amin ^ 2
  let I := T / lambdaFloor c Amin Amax Gmax ^ 2
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hI0 : 0 ≤ I := by dsimp only [I]; positivity
  have hT : 2 * c.A / margin c ^ 2 ≤ T := by
    dsimp only [T]
    calc
      _ ≤ 2 * Amax / margin c ^ 2 := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        ((sq_le_sq₀ ht0.le hm.le).mpr ht)
  have hI : OriginalBetaCurveBounds.inverseLambdaModulus c.A (lower c G) (margin c) ≤ I := by
    change (2 * c.A / margin c ^ 2) / (lambdaMin c G) ^ 2 ≤ T / lambdaFloor c Amin Amax Gmax ^ 2
    calc
      _ ≤ T / (lambdaMin c G) ^ 2 := div_le_div_of_nonneg_right hT (sq_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hT0 (by positivity)
        ((sq_le_sq₀ hlo0.le hl.le).mpr hlo)
  have hratio : c.A / margin c ≤ Amax / marginFloor c Amin := by
    calc
      _ ≤ Amax / margin c := div_le_div_of_nonneg_right hAhi hm.le
      _ ≤ _ := div_le_div_of_nonneg_left hAmax.le ht0 ht
  have hstep : OriginalBetaCurveBounds.stepModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G D ≤
      (c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu := by
    unfold OriginalBetaCurveBounds.stepModulus
    gcongr
  have hactualI0 : 0 ≤ OriginalBetaCurveBounds.inverseLambdaModulus c.A (lower c G) (margin c) := by
    unfold OriginalBetaCurveBounds.inverseLambdaModulus
    positivity
  have hactualStep0 : 0 ≤ OriginalBetaCurveBounds.stepModulus c.mu c.Lg c.M c.A (lower c G) (margin c) G D := by
    unfold OriginalBetaCurveBounds.stepModulus
    positivity
  refine ⟨?_, ?_⟩
  · change 0 ≤ T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
      ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)
    positivity
  · unfold OriginalBetaCurveBounds.sizeModulus
    change _ ≤ T * (Gmax / c.mu) + (Amax / marginFloor c Amin) *
      ((c.Lg * Dmax + (c.M * Dmax + I) * (Gmax / c.mu)) / c.mu)
    gcongr

theorem fuel_uniform_log_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (c : Settings) (hc : Legal c) (Amin Amax Gmax G Dmax : ℝ)
    (hAmin : 0 < Amin) (hAlo : Amin ≤ c.A) (hAhi : c.A ≤ Amax)
    (hG : 0 ≤ G) (hGhi : G ≤ Gmax) (x y : E) (hDhi : ‖x - y‖ ≤ Dmax) :
    let B := Real.logb 2 (max 1 (2 * modulusCeiling c Amin Amax Gmax Dmax /
      (thresholdHigh c - thresholdLow c)))
    (fuel c G x y : ℝ) + 2 ≤ 3 + B ∧
      2 * (fuel c G x y : ℝ) + 5 ≤ 7 + 2 * B := by
  dsimp only
  have hsize := size_modulus_uniform_bound c hc Amin Amax Gmax G ‖x - y‖ Dmax
    hAmin hAlo hAhi hG hGhi (norm_nonneg _) hDhi
  have hA := hc.A_pos
  have hmu := hc.mu_pos
  have hM := hc.M_pos
  have hLg := hc.Lg_nonneg
  have hp := compact_properties c hc G hG
  have hm := hp.2.2.1
  have hK0 : 0 ≤ modulus c G x y := by
    unfold modulus OriginalBetaCurveBounds.sizeModulus OriginalBetaCurveBounds.stepModulus
      OriginalBetaCurveBounds.inverseLambdaModulus
    positivity
  have hK : modulus c G x y ≤ modulusCeiling c Amin Amax Gmax Dmax := hsize.2
  have hwidth : upper c - lower c G ≤ 1 := by linarith only [hp.1, hp.2.2.2.2.2.1]
  have hgap := threshold_gap c hc
  have hnum : modulus c G x y * (upper c - lower c G) ≤ modulusCeiling c Amin Amax Gmax Dmax := by
    have hh := mul_le_mul_of_nonneg_left hwidth hK0
    nlinarith only [hh, hK]
  have hr : (modulus c G x y * (upper c - lower c G)) / ((thresholdHigh c - thresholdLow c) / 2) ≤
      2 * modulusCeiling c Amin Amax Gmax Dmax / (thresholdHigh c - thresholdLow c) := by
    calc
      _ ≤ modulusCeiling c Amin Amax Gmax Dmax / ((thresholdHigh c - thresholdLow c) / 2) :=
        div_le_div_of_nonneg_right hnum (by linarith only [hgap])
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le_max le_rfl hr)
  have hf := positive_search_log_bound c G x y
  constructor <;> linarith only [hf, hlog]

end
end OriginalUniformBetaResources


namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def uniformPrecisionFloor (c : Settings) (sigma0 D : ℝ) (n : ℕ) : ℝ :=
  OriginalUniformBetaResources.queryPrecisionFloor c (effectiveWeightFloor c D)
    (weightCeiling c n) (observedCeiling c D) sigma0

noncomputable def uniformModulusCeiling (c : Settings) (D : ℝ) (n : ℕ) : ℝ :=
  OriginalUniformBetaResources.modulusCeiling c (effectiveWeightFloor c D)
    (weightCeiling c n) (observedCeiling c D) (D + stateRadius c D)

noncomputable def getterLogCeiling (c : Settings) (D : ℝ) (n : ℕ) : ℝ :=
  7 + 2 * Real.logb 2 (max 1 (2 * uniformModulusCeiling c D n / (thresholdHigh c - thresholdLow c)))

noncomputable def getterCountCeiling (c : Settings) (D : ℝ) (n : ℕ) : ℕ := ⌈getterLogCeiling c D n⌉₊

noncomputable def stepCostCeiling (c : Settings) (K sigma0 D : ℝ) (n : ℕ) : ℕ :=
  logarithmicAtomicBound K (uniformPrecisionFloor c sigma0 D n) * getterCountCeiling c D n

theorem uniform_query_floor_effective (c : Settings) (s : State E) (Amin Amax Gmax sigma0 : ℝ) :
    OriginalUniformBetaResources.queryPrecisionFloor (effective (settingsAt c s)) Amin Amax Gmax sigma0 =
      OriginalUniformBetaResources.queryPrecisionFloor c Amin Amax Gmax sigma0 := by
  simp only [OriginalUniformBetaResources.queryPrecisionFloor, OriginalUniformBetaResources.centerPrecisionFloor,
    OriginalUniformBetaResources.outputPrecisionFloor, OriginalUniformBetaResources.lambdaFloor,
    OriginalUniformBetaResources.lambdaCeiling, OriginalUniformBetaResources.betaFloor,
    OriginalUniformBetaResources.marginFloor, effective_mu, effective_Lg, effective_M, effective_sigma,
    effective_low, effective_up, effective_rho, settingsAt]

theorem uniform_modulus_effective (c : Settings) (s : State E) (Amin Amax Gmax Dmax : ℝ) :
    OriginalUniformBetaResources.modulusCeiling (effective (settingsAt c s)) Amin Amax Gmax Dmax =
      OriginalUniformBetaResources.modulusCeiling c Amin Amax Gmax Dmax := by
  simp only [OriginalUniformBetaResources.modulusCeiling, OriginalUniformBetaResources.lambdaFloor,
    OriginalUniformBetaResources.betaFloor, OriginalUniformBetaResources.marginFloor,
    effective_mu, effective_Lg, effective_M, effective_sigma, effective_low, effective_up, effective_rho, settingsAt]

theorem scene_center_distance_bound
    {g : E → ℝ} {getter : E × ℝ → Answer E} {c : Settings} {D : ℝ} {n : ℕ}
    (hc : OriginalFirstCoupledStep.CommonLegal c) (hD : 0 ≤ D) (s : State E)
    (hscene : ResourceScene g getter c D n s) :
    ‖s.x - effectiveY (settingsAt c s) s.x s.y‖ ≤ D + stateRadius c D := by
  have hR := stateRadius_ge_D c hc D hD
  have hw : ‖effectiveY (settingsAt c s) s.x s.y - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D := by
    unfold effectiveY
    split_ifs
    · exact hscene.2.2.2.2.2.1.trans hR
    · exact hscene.2.2.2.2.2.2
  exact (norm_sub_le_norm_sub_add_norm_sub s.x (RobustAHPE.globalMinimizer g)
    (effectiveY (settingsAt c s) s.x s.y)).trans
      (add_le_add hscene.2.2.2.2.2.1 (by simpa only [norm_sub_rev] using hw))

theorem actual_uniform_step_resource_parameters
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n k : ℕ) (hk : k ≤ n) :
    0 < uniformPrecisionFloor c sigma0 D n ∧
      uniformPrecisionFloor c sigma0 D n ≤ queryFloor getter
        (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k)) sigma0
        (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y ∧
      2 * trialFuel getter (settingsAt c (states getter c sigma0 ⟨0, start, start⟩ k))
        (states getter c sigma0 ⟨0, start, start⟩ k).x (states getter c sigma0 ⟨0, start, start⟩ k).y + 5 ≤
          getterCountCeiling c D n := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have he := effective_legal cs (settingsAt_common c H.common s) hA
  have hscene := actual_resources_on_stream H start hstart n k hk
  have hprecision := OriginalUniformBetaResources.all_query_precision_bounds (effective cs) he
    (effectiveWeightFloor c D) (weightCeiling c n) (observedCeiling c D)
    (getterBound getter cs s.x s.y) sigma0 hscene.1 hscene.2.1 hscene.2.2.1 hscene.2.2.2.1 hscene.2.2.2.2.1
    (by simpa only [effective_sigma, effective_up, cs, settingsAt] using H.margin)
  rw [uniform_query_floor_effective] at hprecision
  have hfuel := (OriginalUniformBetaResources.fuel_uniform_log_bound (effective cs) he
    (effectiveWeightFloor c D) (weightCeiling c n) (observedCeiling c D) (getterBound getter cs s.x s.y)
    (D + stateRadius c D) hscene.1 hscene.2.1 hscene.2.2.1 hscene.2.2.2.1 hscene.2.2.2.2.1
    s.x (effectiveY cs s.x s.y) (scene_center_distance_bound H.common H.D_pos.le s hscene)).2
  rw [uniform_modulus_effective] at hfuel
  simp only [thresholdHigh, thresholdLow, effective_M, effective_sigma, effective_low, effective_up, cs, settingsAt] at hfuel
  have hcount : ((2 * trialFuel getter cs s.x s.y + 5 : ℕ) : ℝ) ≤ getterLogCeiling c D n := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, trialFuel, getterBound, getterLogCeiling,
      uniformModulusCeiling, thresholdHigh, thresholdLow, cs, settingsAt] using hfuel
  have hnat : 2 * trialFuel getter cs s.x s.y + 5 ≤ getterCountCeiling c D n := by
    exact_mod_cast hcount.trans (Nat.le_ceil (getterLogCeiling c D n))
  exact ⟨hprecision.1, hprecision.2, hnat⟩

theorem actual_uniform_step_base_cost
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (n k : ℕ) (hk : k ≤ n) :
    baseCost getter cost (stepProgram c sigma0 (states getter c sigma0 ⟨0, start, start⟩ k)) ≤
      stepCostCeiling c K sigma0 D n := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  obtain ⟨value, hrun, hvalid, hfloor, htrace, hcount, hcost, hlog⟩ :=
    original_certified_coupled_ahpe_step g cs (settingsAt_common c H.common s) hA sigma0 D H.margin H.sigma_lt_one
      H.rho_eq H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct cost K hK hatomic s.x s.y
  have hu := actual_uniform_step_resource_parameters H start hstart n k hk
  have hmono := logarithmicAtomicBound_antitone K (uniformPrecisionFloor c sigma0 D n)
    (queryFloor getter cs sigma0 s.x s.y) hK hu.1 hu.2.1
  exact hcost.trans (Nat.mul_le_mul hmono hu.2.2)

theorem actual_contraction_base_count
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (H : Hypotheses g c sigma0 D (implementedGetter baseAnswer oracle))
    (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → (execute baseAnswer (oracle q)).2 ≤ logarithmicAtomicBound K q.2)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let n := contractionIterations c sigma0 D
    let p := primitiveLower oracle (loopProgram c sigma0 n ⟨0, start, start⟩)
    ‖resultPoint (execute baseAnswer p).1 - RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      0 < uniformPrecisionFloor c sigma0 D n ∧
      (execute baseAnswer p).2 ≤ stepCostCeiling c K sigma0 D n * n ∧
      (n : ℝ) ≤ 1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
        (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  have hcontract := actual_finite_second_order_contraction g c H.common sigma0 D H.D_pos H.margin H.sigma_lt_one H.rho_eq
    H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz (implementedGetter baseAnswer oracle) H.getter_correct start hstart
  have hcost := loop_actual_weighted_cost_bound (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
    c sigma0 (contractionIterations c sigma0 D) (stepCostCeiling c K sigma0 D (contractionIterations c sigma0 D)) ⟨0, start, start⟩
    (fun k hk => actual_uniform_step_base_cost H start hstart (implementedCost baseAnswer oracle) K hK hatomic _ k (by omega))
  have hfloor := (actual_uniform_step_resource_parameters H start hstart (contractionIterations c sigma0 D) 0 (by omega)).1
  rw [primitiveLower_execution]
  exact ⟨hcontract.1, hfloor, hcost, hcontract.2⟩

end OriginalRobustTrajectory


namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch
open OriginalCertifiedCoupledAHPE
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def uniformQueryRadius (c : Settings) (D : ℝ) : ℝ :=
  D + 2 * stateRadius c D + 2 * (observedCeiling c D + c.mu / 4) / c.mu

theorem actual_uniform_step_query_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n k : ℕ) (hk : k ≤ n) :
    ∀ q ∈ trace getter (stepProgram c sigma0 (states getter c sigma0 ⟨0, start, start⟩ k)),
      uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧
        ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c D := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  let w := effectiveY cs s.x s.y
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have he := effective_legal cs (settingsAt_common c H.common s) hA
  have hscene := actual_resources_on_stream H start hstart n k hk
  have hu := actual_uniform_step_resource_parameters H start hstart n k hk
  have hp := OriginalCoupledGetterProgram.positiveProgram_request_precision_floor getter (effective cs)
    (outputQueryPrecision (effective cs) sigma0) s.x w
  have hb := OriginalCoupledQueryGeometry.positiveProgram_actual_query_ball g (effective cs) he
    (outputQueryPrecision (effective cs) sigma0) H.C2
    (by simpa only [effective_mu, cs, settingsAt] using H.strongly_convex)
    (by simpa only [effective_Lg, cs, settingsAt] using H.gradient_lipschitz)
    getter H.getter_correct s.x w
  have hR := stateRadius_ge_D c H.common D H.D_pos.le
  have hw : ‖w - RobustAHPE.globalMinimizer g‖ ≤ stateRadius c D := by
    dsimp only [w, effectiveY]
    split_ifs
    · exact hscene.2.2.2.2.2.1.trans hR
    · exact hscene.2.2.2.2.2.2
  have hdist := scene_center_distance_bound H.common H.D_pos.le s hscene
  have hG := hscene.2.2.2.2.1
  have hfrac := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (add_le_add hG (le_refl (c.mu / 4))) (by norm_num : (0 : ℝ) ≤ 2)) H.common.mu_pos.le
  intro q hq
  have hq' : q ∈ trace getter (OriginalCoupledGetterProgram.positiveProgram (effective cs)
      (outputQueryPrecision (effective cs) sigma0) s.x w) := hq
  refine ⟨hu.2.1.trans (hp q hq'), ?_⟩
  have hbq := hb q hq'
  have htriangle := norm_sub_le_norm_sub_add_norm_sub q.1 w (RobustAHPE.globalMinimizer g)
  have hbd := add_le_add hbq hw
  have hbound := htriangle.trans hbd
  simp only [OriginalCoupledQueryGeometry.queryRadius, effective_mu, cs, settingsAt] at hbound
  simp only [getterBound, cs, settingsAt, w] at hfrac hdist hbound
  unfold uniformQueryRadius
  nlinarith only [hbound, hdist, hfrac]

theorem actual_uniform_step_getter_count
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n k : ℕ) (hk : k ≤ n) :
    (execute getter (stepProgram c sigma0 (states getter c sigma0 ⟨0, start, start⟩ k))).2 ≤ getterCountCeiling c D n := by
  let s := states getter c sigma0 ⟨0, start, start⟩ k
  let cs := settingsAt c s
  have hA := all_states_nonnegative g c sigma0 D getter H.step_valid ⟨0, start, start⟩ (by norm_num) k
  have he := effective_legal cs (settingsAt_common c H.common s) hA
  have hmarginE : (effective cs).sigma + (effective cs).sigmaUp < sigma0 := by
    simpa only [effective_sigma, effective_up, cs, settingsAt] using H.margin
  have hprecision := outputQueryPrecision_positive (effective cs) he sigma0 hmarginE
  obtain ⟨value, hrun, hvalid, hcount⟩ := OriginalCoupledGetterProgram.positiveProgram_success_and_getter_calls g
    (effective cs) he (outputQueryPrecision (effective cs) sigma0) hprecision (min_le_left _ _)
    H.C2 (by simpa only [effective_mu, cs, settingsAt] using H.strongly_convex)
    (by simpa only [effective_Lg, cs, settingsAt] using H.gradient_lipschitz)
    (by simpa only [effective_M, cs, settingsAt] using H.hessian_lipschitz)
    getter H.getter_correct s.x (effectiveY cs s.x s.y)
  exact hcount.trans (actual_uniform_step_resource_parameters H start hstart n k hk).2.2

theorem loop_trace_from_step_traces
    (getter : E × ℝ → Answer E) (c : Settings) (sigma0 : ℝ)
    (P : E × ℝ → Prop) (n : ℕ) (s : State E)
    (hsteps : ∀ k < n, ∀ q ∈ trace getter (stepProgram c sigma0 (states getter c sigma0 s k)), P q) :
    ∀ q ∈ trace getter (loopProgram c sigma0 n s), P q := by
  induction n generalizing s with
  | zero => simp only [loopProgram, trace, List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
    intro q hq
    rw [loopProgram, OriginalCoupledQueryGeometry.trace_bind_actual, List.mem_append] at hq
    rcases hq with hfirst | htail
    · exact hsteps 0 (by omega) q hfirst
    · cases hout : (execute getter (stepProgram c sigma0 s)).1 with
      | bracket l r => simpa only [hout, trace, List.not_mem_nil] using htail
      | found value =>
        cases value with
        | stop w => simpa only [hout, trace, List.not_mem_nil] using htail
        | window b d aY =>
          have hadv : advance getter c sigma0 s = nextWindow c s b d aY := by
            unfold advance choice
            rw [hout]
            rfl
          have hnext : ∀ k < n, ∀ r ∈ trace getter (stepProgram c sigma0
              (states getter c sigma0 (nextWindow c s b d aY) k)), P r := by
            intro k hk r hr
            have h := hsteps (k + 1) (by omega)
            rw [states_shift, hadv] at h
            exact h r hr
          exact ih (nextWindow c s b d aY) hnext q (by simpa only [hout] using htail)

theorem actual_contraction_getter_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    ∀ q ∈ trace getter (loopProgram c sigma0 n ⟨0, start, start⟩),
      uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧
        ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c D :=
  loop_trace_from_step_traces getter c sigma0 _ n ⟨0, start, start⟩
    (fun k hk => actual_uniform_step_query_trace H start hstart n k (by omega))

theorem actual_contraction_local_base_count
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (sigma0 D : ℝ)
    (H : Hypotheses g c sigma0 D (implementedGetter baseAnswer oracle))
    (C : ℕ)
    (hatomic : ∀ q : E × ℝ,
      uniformPrecisionFloor c sigma0 D (contractionIterations c sigma0 D) ≤ q.2 →
      ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c D →
      (execute baseAnswer (oracle q)).2 ≤ C)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let n := contractionIterations c sigma0 D
    let p := primitiveLower oracle (loopProgram c sigma0 n ⟨0, start, start⟩)
    ‖resultPoint (execute baseAnswer p).1 - RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      0 < uniformPrecisionFloor c sigma0 D n ∧
      (execute baseAnswer p).2 ≤ C * getterCountCeiling c D n * n ∧
      (n : ℝ) ≤ 1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
        (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  have hcontract := actual_finite_second_order_contraction g c H.common sigma0 D H.D_pos H.margin H.sigma_lt_one H.rho_eq
    H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz (implementedGetter baseAnswer oracle) H.getter_correct start hstart
  have hcost := loop_actual_weighted_cost_bound (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
    c sigma0 (contractionIterations c sigma0 D) (C * getterCountCeiling c D (contractionIterations c sigma0 D)) ⟨0, start, start⟩ (by
      intro k hk
      have htr := actual_uniform_step_query_trace H start hstart (contractionIterations c sigma0 D) k (by omega)
      have hb := baseCost_le_mul_count (implementedGetter baseAnswer oracle) (implementedCost baseAnswer oracle)
        (stepProgram c sigma0 (states (implementedGetter baseAnswer oracle) c sigma0 ⟨0, start, start⟩ k)) C
        (fun q hq => hatomic q (htr q hq).1 (htr q hq).2)
      exact hb.trans (Nat.mul_le_mul_left C (actual_uniform_step_getter_count H start hstart _ k (by omega))))
  have hfloor := (actual_uniform_step_resource_parameters H start hstart (contractionIterations c sigma0 D) 0 (by omega)).1
  rw [primitiveLower_execution]
  exact ⟨hcontract.1, hfloor, hcost, hcontract.2⟩

end OriginalRobustTrajectory

namespace FangqingGetterComposition
open _root_.FangqingGetterComposition
open OriginalBetaATSTrial

theorem baseCost_unit_eq_getter_count {Q A R : Type*} (getter : Q → A) (p : GetterProgram Q A R) :
    baseCost getter (fun _ => 1) p = (execute getter p).2 := by
  induction p with
  | pure r => rfl
  | ask q next ih => simp only [baseCost, execute, ih, Nat.add_comm]

end FangqingGetterComposition

namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings)
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

theorem actual_contraction_primitive_getter_count
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    (execute getter (loopProgram c sigma0 n ⟨0, start, start⟩)).2 ≤ getterCountCeiling c D n * n := by
  have h := loop_actual_weighted_cost_bound getter (fun _ => 1) c sigma0 n (getterCountCeiling c D n)
    ⟨0, start, start⟩ (fun k hk => by
      rw [baseCost_unit_eq_getter_count]
      exact actual_uniform_step_getter_count H start hstart n k (by omega))
  simpa only [baseCost_unit_eq_getter_count] using h

theorem actual_contraction_trace_at_start
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) (n : ℕ) :
    ∀ q ∈ trace getter (loopProgram c sigma0 n ⟨0, start, start⟩),
      uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧
        ‖q.1 - start‖ ≤ uniformQueryRadius c D + D := by
  intro q hq
  have h := actual_contraction_getter_trace H start hstart n q hq
  refine ⟨h.1, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub q.1 (RobustAHPE.globalMinimizer g) start).trans
    (add_le_add h.2 (by simpa only [norm_sub_rev] using hstart))

noncomputable def contractionProgram (c : Settings) (sigma0 D : ℝ) (start : E) :
    GetterProgram (E × ℝ) (Answer E) E :=
  FangqingGetterComposition.map resultPoint (loopProgram c sigma0 (contractionIterations c sigma0 D) ⟨0, start, start⟩)

theorem actual_positive_contraction_program
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let n := contractionIterations c sigma0 D
    ‖(execute getter (contractionProgram c sigma0 D start)).1 - RobustAHPE.globalMinimizer g‖ ≤ D / 2 ∧
      0 < uniformPrecisionFloor c sigma0 D n ∧
      (execute getter (contractionProgram c sigma0 D start)).2 ≤ getterCountCeiling c D n * n ∧
      (∀ q ∈ trace getter (contractionProgram c sigma0 D start),
        uniformPrecisionFloor c sigma0 D n ≤ q.2 ∧ ‖q.1 - start‖ ≤ uniformQueryRadius c D + D) ∧
      (n : ℝ) ≤ 1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) *
        (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  have h := actual_finite_second_order_contraction g c H.common sigma0 D H.D_pos H.margin H.sigma_lt_one H.rho_eq
    H.C2 H.strongly_convex H.gradient_lipschitz H.hessian_lipschitz getter H.getter_correct start hstart
  simp only [contractionProgram, execute_map, OriginalCoupledQueryGeometry.trace_map_actual]
  exact ⟨h.1, (actual_uniform_step_resource_parameters H start hstart _ 0 (by omega)).1,
    actual_contraction_primitive_getter_count H start hstart _, actual_contraction_trace_at_start H start hstart _, h.2⟩

end OriginalRobustTrajectory


namespace OriginalActualDualPositiveContraction
open _root_.OriginalActualDualPositiveContraction
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalDualCurvature OriginalDualMinimizer
open OriginalBetaATSTrial OriginalCoupledBetaSearch OriginalFirstCoupledStep
open OriginalDualGetterImplementation OriginalDualGetterResourceComposition
open OriginalRobustTrajectory FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def parameters (mu L rho D : ℝ) : Settings where
  mu := mu
  Lg := 2 * L
  M := (4 * Real.sqrt 2) * rho
  A := 0
  sigma := 1 / 8
  sigmaLow := 1 / 8
  sigmaUp := 1 / 4
  rho := mu * D / 2

theorem parameters_common (mu L rho D : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (hD : 0 < D) :
    CommonLegal (parameters mu L rho D) := by
  refine ⟨hmu, by dsimp [parameters]; positivity, ?_, by norm_num [parameters],
    by norm_num [parameters], by norm_num [parameters], by norm_num [parameters],
    by norm_num [parameters], by dsimp [parameters]; positivity⟩
  dsimp [parameters]
  positivity

noncomputable def originalProgram (mu L rho D : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F :=
  primitiveLower (oracleProgram L rho x uInit)
    (contractionProgram (parameters mu L rho D) (1 / 2) D yin)

noncomputable def originalQueryBudget (J : Joint E F → ℝ) (mu L rho D : ℝ) (x uInit : E) (yin : F) : ℕ :=
  let c := parameters mu L rho D
  let n := contractionIterations c (1 / 2) D
  queryBallBudget J L rho x uInit yin (uniformQueryRadius c D + D) (uniformPrecisionFloor c (1 / 2) D n) *
    (getterCountCeiling c D n * n)

theorem actual_dual_positive_contraction
    (J : Joint E F → ℝ) (mu L rho D : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (hD : 0 < D)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (originalProgram mu L rho D x uInit yin)
    ‖run.1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ D / 2 ∧
      run.2 ≤ originalQueryBudget J mu L rho D x uInit yin ∧
      (contractionIterations (parameters mu L rho D) (1 / 2) D : ℝ) ≤
        1 + (8 * LargeStepAHPE.rateConstant (1 / 2) (1 / 8)) ^ (2 / 7 : ℝ) *
          (((4 * Real.sqrt 2) * rho) * D / mu) ^ (2 / 7 : ℝ) := by
  let g := psi J L x
  let c := parameters mu L rho D
  let getter := actualGetter J L rho x uInit
  let n := contractionIterations c (1 / 2) D
  let p := contractionProgram c (1 / 2) D yin
  have hgC2 := psi_contDiff2 J L hL hC2 hLip x
  have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
  have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
  have hgHess := psi_hessian_lipschitz J L rho hL hrho.le hC2 hLip hHess x
  have hgetter := actual_getter_accuracy J L rho hL hrho.le hC2 hLip hHess x uInit
  have H : Hypotheses g c (1 / 2) D getter :=
    ⟨parameters_common mu L rho D hmu hL hrho hD, hD, by norm_num [c, parameters],
      by norm_num, rfl, hgC2, hgsc, hglip, hgHess, hgetter⟩
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
  have hvs : vStar (JointSliceRegularity.curry J) L x = RobustAHPE.globalMinimizer g :=
    RobustAHPE.globalMinimizer_unique g mu hmu (hgC2.differentiable (by norm_num)) hgsc _ hmin
  have hstart : ‖yin - RobustAHPE.globalMinimizer g‖ ≤ D := by rwa [← hvs]
  have h := actual_positive_contraction_program H yin hstart
  have hresource := actual_original_queries_from_checked_getter_budget J L rho hL hrho.le hLip x uInit yin
    (uniformQueryRadius c D + D) (uniformPrecisionFloor c (1 / 2) D n) h.2.1 p
    (getterCountCeiling c D n * n)
    (fun q hq => (h.2.2.2.1 q hq).2) (fun q hq => (h.2.2.2.1 q hq).1) h.2.2.1
  have hresult := actual_original_program_result J L rho x uInit p
  refine ⟨?_, hresource, h.2.2.2.2⟩
  change ‖(execute (OriginalDualOracleProgram.actualOracle J)
    (primitiveLower (oracleProgram L rho x uInit) p)).1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ _
  rw [hresult, hvs]
  exact h.1

end OriginalActualDualPositiveContraction


namespace OriginalDualPrimalRecovery
open _root_.OriginalDualPrimalRecovery
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalPrimalElimination OriginalDualCurvature OriginalDualMinimizer
open OriginalDualGetterImplementation OriginalDualResidualQueryBound
open OriginalBetaATSTrial FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def program (L tau : ℝ) (x uInit : E)
    (dualProgram : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  FangqingGetterComposition.bind dualProgram (fun v => FangqingGetterComposition.map
    (fun s : OriginalDualOracleProgram.QueryState E F => JointSliceRegularity.point s.u v)
    (liftQuery (OriginalDualOracleProgram.simulator L x v uInit (tau / 4))))

noncomputable def queryBudget (J : Joint E F → ℝ) (L D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x uInit yin + (D + tau / 4)) / (tau / 4)))

theorem actual_joint_recovery_from_actual_dual_program
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 < tau) (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D)
    (dualProgram : GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F)
    (hdual : ‖(execute (OriginalDualOracleProgram.actualOracle J) dualProgram).1 -
      vStar (JointSliceRegularity.curry J) L x‖ ≤ tau / 4) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program L tau x uInit dualProgram)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ (execute (OriginalDualOracleProgram.actualOracle J) dualProgram).2 + queryBudget J L D tau x uInit yin := by
  let first := execute (OriginalDualOracleProgram.actualOracle J) dualProgram
  let v := first.1
  let last := OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
    (OriginalDualOracleProgram.simulator L x v uInit (tau / 4))
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpu := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hlast := OriginalDualOracleProgram.reduced_dual_oracle_simulation J L rho hL hrho
    hC2 hLip hHess x uInit v (tau / 4) (by positivity)
  have hprimal := primal_lipschitz J L hL hJ hLip x v (vStar (JointSliceRegularity.curry J) L x)
  rw [hpu] at hprimal
  have hu : ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ≤ tau / 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub last.1.u (primal J L x v) (uStar (JointSliceRegularity.curry J) L x)
    have hd : ‖last.1.u - primal J L x v‖ ≤ tau / 4 := hlast.2.1
    linarith only [ht, hd, hprimal, hdual]
  have hball : ‖v - yin‖ ≤ D + tau / 4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub v (vStar (JointSliceRegularity.curry J) L x) yin
    rw [norm_sub_rev (vStar (JointSliceRegularity.curry J) L x) yin] at ht
    linarith only [ht, hwarm, hdual]
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x uInit v yin (D + tau / 4)
    (tau / 4) (by positivity) hball
  have hlastCost : last.2 ≤ queryBudget J L D tau x uInit yin := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact hc.trans (Nat.le_ceil _)
  have hexec : execute (OriginalDualOracleProgram.actualOracle J) (program L tau x uInit dualProgram) =
      (JointSliceRegularity.point last.1.u v, first.2 + last.2) := by
    simp only [program, execute_bind, execute_map, execute_liftQuery]
    rfl
  rw [hexec]
  constructor
  · have hn := WithLp.prod_norm_sq_eq_of_L2
      (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)
    have heq : ‖JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x‖ ^ 2 =
        ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ^ 2 +
          ‖v - vStar (JointSliceRegularity.curry J) L x‖ ^ 2 := by
      rw [JointSliceRegularity.point_eq_toLp] at hn ⊢
      exact hn
    have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 2)).mpr hu
    have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 4)).mpr hdual
    nlinarith only [heq, hu2, hv2, htau,
      norm_nonneg (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)]
  · exact add_le_add le_rfl hlastCost

end OriginalDualPrimalRecovery


namespace FangqingGetterComposition
open _root_.FangqingGetterComposition
open OriginalBetaATSTrial

theorem baseCost_map_eq {Q A R S : Type*} (getter : Q → A) (cost : Q → ℕ) (f : R → S)
    (p : GetterProgram Q A R) : baseCost getter cost (map f p) = baseCost getter cost p := by
  simp only [map, baseCost_bind, baseCost, Nat.add_zero]

end FangqingGetterComposition

namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings)
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def atRadius (c : Settings) (R : ℝ) : Settings := {c with rho := c.mu * R / 2}

noncomputable def oneRadiusProgram (c : Settings) (sigma0 R : ℝ) (start : E) : GetterProgram (E × ℝ) (Answer E) E :=
  contractionProgram (atRadius c R) sigma0 R start

noncomputable def radiusGetterFactor (c : Settings) (sigma0 R : ℝ) : ℕ :=
  getterCountCeiling (atRadius c R) R (contractionIterations c sigma0 R)

noncomputable def radiusBaseFactor (c : Settings) (K sigma0 R : ℝ) : ℕ :=
  stepCostCeiling (atRadius c R) K sigma0 R (contractionIterations c sigma0 R)

theorem contractionIterations_atRadius (c : Settings) (sigma0 R S : ℝ) :
    contractionIterations (atRadius c R) sigma0 S = contractionIterations c sigma0 S := rfl

theorem Hypotheses.atRadius {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R) : Hypotheses g (atRadius c R) sigma0 R getter := by
  refine ⟨⟨H.common.mu_pos, H.common.Lg_nonneg, H.common.M_pos, H.common.sigma_pos, H.common.sigma_lt_one,
      H.common.low_pos, H.common.low_lt_up, H.common.gap, ?_⟩,
    hR, H.margin, H.sigma_lt_one, rfl, H.C2, H.strongly_convex, H.gradient_lipschitz, H.hessian_lipschitz, H.getter_correct⟩
  change 0 < c.mu * R / 2
  exact div_pos (mul_pos H.common.mu_pos hR) (by norm_num)

theorem one_radius_program_spec
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2) :
    ‖(execute getter (oneRadiusProgram c sigma0 R start)).1 - RobustAHPE.globalMinimizer g‖ ≤ R / 2 ∧
      (execute getter (oneRadiusProgram c sigma0 R start)).2 ≤
        radiusGetterFactor c sigma0 R * contractionIterations c sigma0 R ∧
      baseCost getter cost (oneRadiusProgram c sigma0 R start) ≤
        radiusBaseFactor c K sigma0 R * contractionIterations c sigma0 R := by
  have HR := H.atRadius R hR
  have h := actual_positive_contraction_program HR start hstart
  dsimp only at h
  have hb := loop_actual_weighted_cost_bound getter cost (atRadius c R) sigma0 (contractionIterations c sigma0 R)
    (radiusBaseFactor c K sigma0 R) ⟨0, start, start⟩ (fun k hk =>
      actual_uniform_step_base_cost HR start hstart cost K hK hatomic _ k (by omega))
  exact ⟨h.1, h.2.2.1, by simpa only [oneRadiusProgram, contractionProgram, baseCost_map_eq, contractionIterations_atRadius] using hb⟩

noncomputable def restartProgram (c : Settings) (sigma0 : ℝ) : ℕ → ℝ → E → GetterProgram (E × ℝ) (Answer E) E
  | 0, _, start => .pure start
  | r + 1, R, start => bind (oneRadiusProgram c sigma0 R start)
      (fun point => restartProgram c sigma0 r (R / 2) point)

noncomputable def coefficientSum (coefficient : ℝ → ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | r + 1, R => coefficient R + coefficientSum coefficient r (R / 2)

noncomputable def coefficientMaximum (coefficient : ℝ → ℕ) : ℕ → ℝ → ℕ
  | 0, _ => 0
  | r + 1, R => max (coefficient R) (coefficientMaximum coefficient r (R / 2))

theorem coefficient_sum_le_maximum (coefficient : ℝ → ℕ) (r : ℕ) (R : ℝ) :
    coefficientSum coefficient r R ≤ coefficientMaximum coefficient r R * r := by
  induction r generalizing R with
  | zero => simp only [coefficientSum, coefficientMaximum, Nat.mul_zero, le_refl]
  | succ r ih =>
    have htail := ih (R / 2)
    have hhead : coefficient R ≤ max (coefficient R) (coefficientMaximum coefficient r (R / 2)) := le_max_left _ _
    have hmax : coefficientMaximum coefficient r (R / 2) ≤ max (coefficient R) (coefficientMaximum coefficient r (R / 2)) := le_max_right _ _
    have hmul := Nat.mul_le_mul_right r hmax
    simp only [coefficientSum, coefficientMaximum]
    nlinarith only [htail, hhead, hmul]

theorem actual_positive_restarts
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter)
    (cost : E × ℝ → ℕ) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → cost q ≤ logarithmicAtomicBound K q.2)
    (r : ℕ) (R : ℝ) (hR : 0 < R) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R) :
    ‖(execute getter (restartProgram c sigma0 r R start)).1 - RobustAHPE.globalMinimizer g‖ ≤ R / (2 : ℝ) ^ r ∧
      (execute getter (restartProgram c sigma0 r R start)).2 ≤
        coefficientSum (fun R => radiusGetterFactor c sigma0 R * contractionIterations c sigma0 R) r R ∧
      baseCost getter cost (restartProgram c sigma0 r R start) ≤
        coefficientSum (fun R => radiusBaseFactor c K sigma0 R * contractionIterations c sigma0 R) r R := by
  induction r generalizing R start with
  | zero => simpa only [restartProgram, execute, baseCost, coefficientSum, pow_zero, div_one, le_refl, and_self, and_true] using hstart
  | succ r ih =>
    let first := execute getter (oneRadiusProgram c sigma0 R start)
    have hfirst := one_radius_program_spec H R hR start hstart cost K hK hatomic
    have hsecond := ih (R / 2) (by positivity) first.1 hfirst.1
    simp only [restartProgram, execute_bind, baseCost_bind, coefficientSum]
    refine ⟨?_, Nat.add_le_add hfirst.2.1 hsecond.2.1, Nat.add_le_add hfirst.2.2 hsecond.2.2⟩
    convert! hsecond.1 using 1
    rw [pow_succ]
    ring

theorem contraction_iterations_monotone
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) :
    contractionIterations c sigma0 R ≤ contractionIterations c sigma0 S := by
  have hC := LargeStepAHPE.rateConstant_positive sigma0 c.sigmaLow H.sigma_positive H.sigma_lt_one H.common.low_pos
  have hscale : 8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * R / c.mu ≤
      8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * S / c.mu :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRS
      (mul_nonneg (mul_nonneg (by norm_num) hC.le) H.common.M_pos.le)) H.common.mu_pos.le
  have hbase : 0 ≤ 8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow * c.M * R / c.mu := by
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC.le) H.common.M_pos.le) hR) H.common.mu_pos.le
  unfold contractionIterations OriginalSecondOrderCount.iterations
  exact max_le_max le_rfl (Nat.ceil_mono (Real.rpow_le_rpow hbase hscale (by norm_num : (0 : ℝ) ≤ 2 / 7)))

theorem coefficient_sum_remove_iteration_factor
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (coefficient : ℝ → ℕ) (r : ℕ)
    (R : ℝ) (hR : 0 ≤ R) (hRD : R ≤ D) :
    coefficientSum (fun R => coefficient R * contractionIterations c sigma0 R) r R ≤
      contractionIterations c sigma0 D * coefficientSum coefficient r R := by
  induction r generalizing R with
  | zero => simp only [coefficientSum, Nat.mul_zero, le_refl]
  | succ r ih =>
    have hn := contraction_iterations_monotone H R D hR hRD
    have hhead := Nat.mul_le_mul_left (coefficient R) hn
    have hhalf : 0 ≤ R / 2 := by positivity
    have hhalfD : R / 2 ≤ D := by linarith only [hR, hRD]
    have htail := ih (R / 2) hhalf hhalfD
    simp only [coefficientSum]
    calc
      _ ≤ coefficient R * contractionIterations c sigma0 D +
          contractionIterations c sigma0 D * coefficientSum coefficient r (R / 2) := Nat.add_le_add hhead htail
      _ = _ := by ring

theorem actual_positive_restart_base_program
    {BQ BA : Type*} (baseAnswer : BQ → BA)
    (oracle : E × ℝ → GetterProgram BQ BA (Answer E))
    (g : E → ℝ) (c : Settings) (sigma0 D tau : ℝ)
    (H : Hypotheses g c sigma0 D (implementedGetter baseAnswer oracle))
    (htau : 0 < tau) (K : ℝ) (hK : 0 ≤ K)
    (hatomic : ∀ q : E × ℝ, 0 < q.2 → (execute baseAnswer (oracle q)).2 ≤ logarithmicAtomicBound K q.2)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let r := FangqingHysteresis.halvingCount D tau
    let p := primitiveLower oracle (restartProgram c sigma0 r D start)
    ‖(execute baseAnswer p).1 - RobustAHPE.globalMinimizer g‖ ≤ tau ∧
      (execute baseAnswer p).2 ≤ contractionIterations c sigma0 D * r *
        coefficientMaximum (radiusBaseFactor c K sigma0) r D ∧
      (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) ∧
      (contractionIterations c sigma0 D : ℝ) ≤
        1 + (8 * LargeStepAHPE.rateConstant sigma0 c.sigmaLow) ^ (2 / 7 : ℝ) * (c.M * D / c.mu) ^ (2 / 7 : ℝ) := by
  dsimp only
  let getter := implementedGetter baseAnswer oracle
  let r := FangqingHysteresis.halvingCount D tau
  have hs := actual_positive_restarts H (implementedCost baseAnswer oracle) K hK hatomic r D H.D_pos start hstart
  have hsum := coefficient_sum_remove_iteration_factor H (radiusBaseFactor c K sigma0) r D H.D_pos.le le_rfl
  have hmax := coefficient_sum_le_maximum (radiusBaseFactor c K sigma0) r D
  have hcost : baseCost getter (implementedCost baseAnswer oracle) (restartProgram c sigma0 r D start) ≤
      contractionIterations c sigma0 D * r * coefficientMaximum (radiusBaseFactor c K sigma0) r D := by
    calc
      _ ≤ contractionIterations c sigma0 D * coefficientSum (radiusBaseFactor c K sigma0) r D := hs.2.2.trans hsum
      _ ≤ contractionIterations c sigma0 D * (coefficientMaximum (radiusBaseFactor c K sigma0) r D * r) :=
        Nat.mul_le_mul_left _ hmax
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.logb 2 (max 1 (D / tau)) := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hr : (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) := by
    have h := (Nat.ceil_lt_add_one hlog0).le
    change (r : ℝ) ≤ _ at h
    linarith only [h]
  have hn := (OriginalSecondOrderCount.rounded_iteration_properties (LargeStepAHPE.rateConstant sigma0 c.sigmaLow)
    c.M D c.mu (LargeStepAHPE.rateConstant_positive sigma0 c.sigmaLow H.sigma_positive H.sigma_lt_one H.common.low_pos).le
    H.common.M_pos.le H.D_pos.le H.common.mu_pos).2.1
  rw [primitiveLower_execution]
  exact ⟨hs.1.trans (FangqingHysteresis.halving_precision D tau htau), hcost, hr, hn⟩

end OriginalRobustTrajectory


namespace OriginalRobustTrajectory
open _root_.OriginalRobustTrajectory
open OriginalBetaATSTrial
open OriginalCoupledBetaSearch (Settings)
open FangqingGetterComposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

noncomputable def radiusPrecision (c : Settings) (sigma0 R : ℝ) : ℝ :=
  uniformPrecisionFloor (atRadius c R) sigma0 R (contractionIterations c sigma0 R)

noncomputable def precisionMinimum (c : Settings) (sigma0 : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | r + 1, R => min (radiusPrecision c sigma0 R) (precisionMinimum c sigma0 r (R / 2))

theorem firstWeightFloor_antitone (c : Settings) (hc : OriginalFirstCoupledStep.CommonLegal c)
    (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : firstWeightFloor c S ≤ firstWeightFloor c R := by
  have hnum : 0 ≤ c.sigmaLow * c.mu * (1 - c.sigma) :=
    mul_nonneg (mul_nonneg hc.low_pos.le hc.mu_pos.le) (sub_nonneg.mpr hc.sigma_lt_one.le)
  have hMR : 0 < c.M * (1 + c.Lg * R) :=
    mul_pos hc.M_pos (by nlinarith only [mul_nonneg hc.Lg_nonneg hR])
  have hden : c.M * (1 + c.Lg * R) ≤ c.M * (1 + c.Lg * S) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hRS hc.Lg_nonneg)) hc.M_pos.le
  exact div_le_div_of_nonneg_left hnum hMR hden

theorem stateRadius_monotone (c : Settings) (hc : OriginalFirstCoupledStep.CommonLegal c)
    (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : stateRadius c R ≤ stateRadius c S := by
  have hS : 0 ≤ S := hR.trans hRS
  have hfloorR := firstWeightFloor_positive c hc R hR
  have hfloorS := firstWeightFloor_positive c hc S hS
  have hfloor := firstWeightFloor_antitone c hc R S hR hRS
  have hinv : (c.mu * firstWeightFloor c R)⁻¹ ≤ (c.mu * firstWeightFloor c S)⁻¹ :=
    inv_anti₀ (mul_pos hc.mu_pos hfloorS) (mul_le_mul_of_nonneg_left hfloor hc.mu_pos.le)
  unfold stateRadius geometryRadius
  exact mul_le_mul hRS (add_le_add le_rfl hinv)
    (by have h := inv_nonneg.mpr (mul_nonneg hc.mu_pos.le hfloorR.le); linarith only [h]) hS

theorem uniformQueryRadius_monotone (c : Settings) (hc : OriginalFirstCoupledStep.CommonLegal c)
    (R S : ℝ) (hR : 0 ≤ R) (hRS : R ≤ S) : uniformQueryRadius c R ≤ uniformQueryRadius c S := by
  have hradius := stateRadius_monotone c hc R S hR hRS
  have hobs : observedCeiling c R ≤ observedCeiling c S := by
    unfold observedCeiling
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith only [hRS, hradius]) hc.Lg_nonneg)
  have hfrac := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add hobs (le_refl (c.mu / 4))) (by norm_num : (0 : ℝ) ≤ 2)) hc.mu_pos.le
  unfold uniformQueryRadius
  linarith only [hRS, hradius, hfrac]

theorem radiusPrecision_positive
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R) : 0 < radiusPrecision c sigma0 R := by
  have HR := H.atRadius R hR
  have ht := (actual_uniform_step_resource_parameters HR (RobustAHPE.globalMinimizer g)
    (by simpa only [sub_self, norm_zero] using hR.le) (contractionIterations c sigma0 R) 0 (by omega)).1
  exact ht

theorem precisionMinimum_positive
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (r : ℕ) (R : ℝ) (hR : 0 < R) : 0 < precisionMinimum c sigma0 r R := by
  induction r generalizing R with
  | zero => norm_num [precisionMinimum]
  | succ r ih => exact lt_min (radiusPrecision_positive H R hR) (ih (R / 2) (by positivity))

theorem uniformQueryRadius_atRadius (c : Settings) (R S : ℝ) :
    uniformQueryRadius (atRadius c R) S = uniformQueryRadius c S := rfl

theorem one_radius_actual_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (R : ℝ) (hR : 0 < R)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R) :
    ∀ q ∈ trace getter (oneRadiusProgram c sigma0 R start),
      radiusPrecision c sigma0 R ≤ q.2 ∧ ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c R := by
  have ht := actual_contraction_getter_trace (H.atRadius R hR) start hstart (contractionIterations c sigma0 R)
  simpa only [oneRadiusProgram, contractionProgram, OriginalCoupledQueryGeometry.trace_map_actual,
    contractionIterations_atRadius, radiusPrecision, uniformQueryRadius_atRadius] using ht

theorem actual_positive_restart_trace
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (r : ℕ) (R : ℝ) (hR : 0 < R)
    (start : E) (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ R) :
    ∀ q ∈ trace getter (restartProgram c sigma0 r R start),
      precisionMinimum c sigma0 r R ≤ q.2 ∧ ‖q.1 - RobustAHPE.globalMinimizer g‖ ≤ uniformQueryRadius c R := by
  induction r generalizing R start with
  | zero => simp only [restartProgram, trace, List.not_mem_nil, false_implies, implies_true]
  | succ r ih =>
    have hfirst := actual_positive_contraction_program (H.atRadius R hR) start hstart
    have hfirstdist : ‖(execute getter (oneRadiusProgram c sigma0 R start)).1 - RobustAHPE.globalMinimizer g‖ ≤ R / 2 := hfirst.1
    have hRhalf : 0 < R / 2 := by positivity
    have hsecond := ih (R / 2) hRhalf (execute getter (oneRadiusProgram c sigma0 R start)).1 hfirstdist
    intro q hq
    rw [restartProgram, OriginalCoupledQueryGeometry.trace_bind_actual, List.mem_append] at hq
    rcases hq with hq | hq
    · have h := one_radius_actual_trace H R hR start hstart q hq
      exact ⟨(min_le_left _ _).trans h.1, h.2⟩
    · have h := hsecond q hq
      exact ⟨(min_le_right _ _).trans h.1, h.2.trans
        (uniformQueryRadius_monotone c H.common (R / 2) R hRhalf.le (by linarith only [hR]))⟩

theorem actual_positive_restart_getter_count
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (r : ℕ) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    (execute getter (restartProgram c sigma0 r D start)).2 ≤
      contractionIterations c sigma0 D * r * coefficientMaximum (radiusGetterFactor c sigma0) r D := by
  have hs := (actual_positive_restarts H (fun _ => 0) 0 (by norm_num) (fun _ _ => Nat.zero_le _)
    r D H.D_pos start hstart).2.1
  have hsum := coefficient_sum_remove_iteration_factor H (radiusGetterFactor c sigma0) r D H.D_pos.le le_rfl
  have hmax := coefficient_sum_le_maximum (radiusGetterFactor c sigma0) r D
  calc
    _ ≤ contractionIterations c sigma0 D * coefficientSum (radiusGetterFactor c sigma0) r D := hs.trans hsum
    _ ≤ contractionIterations c sigma0 D * (coefficientMaximum (radiusGetterFactor c sigma0) r D * r) := Nat.mul_le_mul_left _ hmax
    _ = _ := by ring

theorem actual_positive_restarts_to_accuracy
    {g : E → ℝ} {c : Settings} {sigma0 D : ℝ} {getter : E × ℝ → Answer E}
    (H : Hypotheses g c sigma0 D getter) (tau : ℝ) (htau : 0 < tau) (start : E)
    (hstart : ‖start - RobustAHPE.globalMinimizer g‖ ≤ D) :
    let r := FangqingHysteresis.halvingCount D tau
    let p := restartProgram c sigma0 r D start
    ‖(execute getter p).1 - RobustAHPE.globalMinimizer g‖ ≤ tau ∧
      0 < precisionMinimum c sigma0 r D ∧
      (execute getter p).2 ≤ contractionIterations c sigma0 D * r * coefficientMaximum (radiusGetterFactor c sigma0) r D ∧
      (∀ q ∈ trace getter p, precisionMinimum c sigma0 r D ≤ q.2 ∧ ‖q.1 - start‖ ≤ uniformQueryRadius c D + D) ∧
      (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) := by
  dsimp only
  let r := FangqingHysteresis.halvingCount D tau
  have hs := actual_positive_restarts H (fun _ => 0) 0 (by norm_num) (fun _ _ => Nat.zero_le _) r D H.D_pos start hstart
  have hlog0 : 0 ≤ Real.logb 2 (max 1 (D / tau)) := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hr : (r : ℝ) ≤ 1 + Real.logb 2 (max 1 (D / tau)) := by
    have h := (Nat.ceil_lt_add_one hlog0).le
    change (r : ℝ) ≤ _ at h
    linarith only [h]
  refine ⟨hs.1.trans (FangqingHysteresis.halving_precision D tau htau), precisionMinimum_positive H r D H.D_pos,
    actual_positive_restart_getter_count H r start hstart, ?_, hr⟩
  intro q hq
  have h := actual_positive_restart_trace H r D H.D_pos start hstart q hq
  exact ⟨h.1, (norm_sub_le_norm_sub_add_norm_sub q.1 (RobustAHPE.globalMinimizer g) start).trans
    (add_le_add h.2 (by simpa only [norm_sub_rev] using hstart))⟩

end OriginalRobustTrajectory


namespace OriginalActualDualSecondOrderWarm
open _root_.OriginalActualDualSecondOrderWarm
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalDualCurvature OriginalDualMinimizer
open OriginalBetaATSTrial OriginalRobustTrajectory
open OriginalDualGetterImplementation OriginalDualGetterResourceComposition
open OriginalActualDualPositiveContraction FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def dualProgram (mu L rho D tol : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F :=
  if 0 < D then primitiveLower (oracleProgram L rho x uInit)
    (restartProgram (parameters mu L rho D) (1 / 2) (FangqingHysteresis.halvingCount D tol) D yin)
  else .pure yin

noncomputable def dualQueryBudget (J : Joint E F → ℝ) (mu L rho D tol : ℝ) (x uInit : E) (yin : F) : ℕ :=
  if 0 < D then
    let c := parameters mu L rho D
    let r := FangqingHysteresis.halvingCount D tol
    queryBallBudget J L rho x uInit yin (uniformQueryRadius c D + D) (precisionMinimum c (1 / 2) r D) *
      (contractionIterations c (1 / 2) D * r * coefficientMaximum (radiusGetterFactor c (1 / 2)) r D)
  else 0

theorem actual_positive_dual_restarts
    (J : Joint E F → ℝ) (mu L rho D tol : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htol : 0 < tol)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (dualProgram mu L rho D tol x uInit yin)
    ‖run.1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ tol ∧
      run.2 ≤ dualQueryBudget J mu L rho D tol x uInit yin := by
  classical
  by_cases hD : 0 < D
  · let g := psi J L x
    let c := parameters mu L rho D
    let getter := actualGetter J L rho x uInit
    let r := FangqingHysteresis.halvingCount D tol
    let p := restartProgram c (1 / 2) r D yin
    have hgC2 := psi_contDiff2 J L hL hC2 hLip x
    have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
    have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
    have hgHess := psi_hessian_lipschitz J L rho hL hrho.le hC2 hLip hHess x
    have hgetter := actual_getter_accuracy J L rho hL hrho.le hC2 hLip hHess x uInit
    have H : Hypotheses g c (1 / 2) D getter :=
      ⟨parameters_common mu L rho D hmu hL hrho hD, hD, by norm_num [c, parameters],
        by norm_num, rfl, hgC2, hgsc, hglip, hgHess, hgetter⟩
    have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
    have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
    have hvs : vStar (JointSliceRegularity.curry J) L x = RobustAHPE.globalMinimizer g :=
      RobustAHPE.globalMinimizer_unique g mu hmu (hgC2.differentiable (by norm_num)) hgsc _ hmin
    have hstart : ‖yin - RobustAHPE.globalMinimizer g‖ ≤ D := by rwa [← hvs]
    have h := actual_positive_restarts_to_accuracy H tol htol yin hstart
    have hresource := actual_original_queries_from_checked_getter_budget J L rho hL hrho.le hLip x uInit yin
      (uniformQueryRadius c D + D) (precisionMinimum c (1 / 2) r D) h.2.1 p
      (contractionIterations c (1 / 2) D * r * coefficientMaximum (radiusGetterFactor c (1 / 2)) r D)
      (fun q hq => (h.2.2.2.1 q hq).2) (fun q hq => (h.2.2.2.1 q hq).1) h.2.2.1
    have hresult := actual_original_program_result J L rho x uInit p
    constructor
    · simp only [dualProgram, if_pos hD]
      change ‖(execute (OriginalDualOracleProgram.actualOracle J)
        (primitiveLower (oracleProgram L rho x uInit) p)).1 - vStar (JointSliceRegularity.curry J) L x‖ ≤ _
      rw [hresult, hvs]
      exact h.1
    · simpa only [dualProgram, dualQueryBudget, if_pos hD] using hresource
  · have hD0 : D = 0 := le_antisymm (le_of_not_gt hD) ((norm_nonneg _).trans hwarm)
    simp only [dualProgram, dualQueryBudget, if_neg hD, execute, Nat.le_refl, and_true]
    rw [hD0] at hwarm
    exact hwarm.trans htol.le

noncomputable def warmProgram (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  OriginalDualPrimalRecovery.program L tau x uInit (dualProgram mu L rho D (tau / 4) x uInit yin)

noncomputable def warmQueryBudget (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  dualQueryBudget J mu L rho D (tau / 4) x uInit yin + OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin

theorem actual_positive_second_order_joint_warm_solve
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (warmProgram mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ warmQueryBudget J mu L rho D tau x uInit yin := by
  have hdual := actual_positive_dual_restarts J mu L rho D (tau / 4) hmu hL hrho (by positivity)
    hC2 hLip hHess hsc x uInit yin hwarm
  have hrecover := OriginalDualPrimalRecovery.actual_joint_recovery_from_actual_dual_program
    J mu L rho D tau hmu hL hrho.le htau hC2 hLip hHess hsc x uInit yin hwarm
    (dualProgram mu L rho D (tau / 4) x uInit yin) hdual.1
  exact ⟨hrecover.1, hrecover.2.trans (add_le_add hdual.2 le_rfl)⟩

end OriginalActualDualSecondOrderWarm


namespace OriginalZeroCurvatureDualWarm
open _root_.OriginalZeroCurvatureDualWarm
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalPrimalElimination OriginalDualCurvature OriginalDualMinimizer
open OriginalDualGetterImplementation OriginalDualResidualQueryBound
open OriginalDualGetterResourceComposition
open OriginalBetaATSTrial OriginalZeroCurvatureSearch OriginalZeroQueryGeometry
open FangqingGetterComposition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def dualProgram (mu L tol : ℝ) (yin : F) : GetterProgram (F × ℝ) (Answer F) (TrialResult F) :=
  zeroProgram mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8) yin yin
noncomputable def dualFloor (getter : F × ℝ → Answer F) (mu L tol : ℝ) (yin : F) : ℝ :=
  zeroPrecisionFloor getter mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8) yin yin
noncomputable def dualBall (getter : F × ℝ → Answer F) (mu L : ℝ) (yin : F) : ℝ :=
  ‖yin - yin‖ + 2 * (observedBound getter (2 * L) yin yin + mu / 4) / mu
noncomputable def dualOriginalProgram (mu L tol : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (TrialResult F) :=
  primitiveLower (oracleProgram L 0 x uInit) (dualProgram mu L tol yin)
noncomputable def dualQueryBudget (J : Joint E F → ℝ) (mu L tol : ℝ) (x uInit : E) (yin : F) : ℕ :=
  let getter := actualGetter J L 0 x uInit
  queryBallBudget J L 0 x uInit yin (dualBall getter mu L yin) (dualFloor getter mu L tol yin)

theorem actual_zero_dual_accuracy
    (J : Joint E F → ℝ) (mu L tol : ℝ) (hmu : 0 < mu) (hL : 0 < L) (htol : 0 < tol)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hH0 : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) :
    ∃ v : F,
      (execute (OriginalDualOracleProgram.actualOracle J) (dualOriginalProgram mu L tol x uInit yin)).1 = .stop v ∧
      ‖v - vStar (JointSliceRegularity.curry J) L x‖ ≤ tol ∧
      (execute (OriginalDualOracleProgram.actualOracle J) (dualOriginalProgram mu L tol x uInit yin)).2 ≤
        3 * dualQueryBudget J mu L tol x uInit yin := by
  let getter := actualGetter J L 0 x uInit
  let g := psi J L x
  have hgC2 := psi_contDiff2 J L hL hC2 hLip x
  have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
  have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
  have hgH0 : ∀ z w : F, ‖fderiv ℝ (gradient g) z - fderiv ℝ (gradient g) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
    simpa only [mul_zero, zero_mul] using psi_hessian_lipschitz J L 0 hL (by norm_num) hC2 hLip hH0 x
  have hgetter := actual_getter_accuracy J L 0 hL (by norm_num) hC2 hLip hH0 x uInit
  obtain ⟨v, hrun, hgrad, hcount, hfloor, _⟩ := zeroProgram_small_gradient_and_logarithmic_cost g mu (2 * L) 1
    (1 / 4) (mu * tol) (mu * tol / 8) hmu (by positivity) (by norm_num) (by norm_num) (by norm_num)
    (by positivity) (by positivity) le_rfl hgC2 hgsc hglip hgH0 getter hgetter
    (fun _ => 0) 0 (by norm_num) (fun _ _ => Nat.zero_le _) yin yin
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
  have hdist := PacketCore.strongConvex_gradient_distance g mu hmu hgsc
    (hgC2.differentiable (by norm_num)) _ hmin v
  have hv : ‖v - vStar (JointSliceRegularity.curry J) L x‖ ≤ tol := by
    apply (mul_le_mul_iff_right₀ hmu).mp
    nlinarith only [hdist, hgrad]
  have hpoints := zeroProgram_actual_query_ball g mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8)
    hmu (by positivity) (by norm_num) (by norm_num) (by norm_num) (by positivity)
    hgC2 hgsc hglip getter hgetter yin yin
  have hprecisions := zeroProgram_trace_floor getter mu (2 * L) 1 (1 / 4) (mu * tol) (mu * tol / 8) yin yin
  have hcost := actual_original_queries_from_checked_getter_budget J L 0 hL (by norm_num) hLip x uInit yin
    (dualBall getter mu L yin) (dualFloor getter mu L tol yin) hfloor (dualProgram mu L tol yin) 3
    hpoints hprecisions hcount
  have hbase := primitiveLower_execution (OriginalDualOracleProgram.actualOracle J) (oracleProgram L 0 x uInit)
    (dualProgram mu L tol yin)
  refine ⟨v, ?_, hv, ?_⟩
  · change (execute (OriginalDualOracleProgram.actualOracle J)
      (primitiveLower (oracleProgram L 0 x uInit) (dualProgram mu L tol yin))).1 = _
    rw [hbase]
    exact hrun
  · simpa only [dualOriginalProgram, dualQueryBudget, Nat.mul_comm] using hcost

noncomputable def recoverProgram (L tau : ℝ) (x uInit : E) (yin : F) : TrialResult F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F)
  | .stop v => FangqingGetterComposition.map (fun s : OriginalDualOracleProgram.QueryState E F =>
      JointSliceRegularity.point s.u v) (liftQuery (OriginalDualOracleProgram.simulator L x v uInit (tau / 4)))
  | .step _ _ => .pure (JointSliceRegularity.point uInit yin)
noncomputable def warmProgram (mu L tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  FangqingGetterComposition.bind (dualOriginalProgram mu L (tau / 4) x uInit yin) (recoverProgram L tau x uInit yin)
noncomputable def recoveryQueryBudget (J : Joint E F → ℝ) (L D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  Nat.ceil (2 + 18 * Real.log (1 + 3 * (observedRadius J L x uInit yin + (D + tau / 4)) / (tau / 4)))
noncomputable def warmQueryBudget (J : Joint E F → ℝ) (mu L D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  3 * dualQueryBudget J mu L (tau / 4) x uInit yin + recoveryQueryBudget J L D tau x uInit yin

theorem actual_zero_curvature_joint_warm_solve
    (J : Joint E F → ℝ) (mu L D tau : ℝ) (hmu : 0 < mu) (hL : 0 < L) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hH0 : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ (0 : ℝ) * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (warmProgram mu L tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ warmQueryBudget J mu L D tau x uInit yin := by
  let first := execute (OriginalDualOracleProgram.actualOracle J) (dualOriginalProgram mu L (tau / 4) x uInit yin)
  obtain ⟨v, hfirst, hv, hfirstCost⟩ := actual_zero_dual_accuracy J mu L (tau / 4) hmu hL (by positivity)
    hC2 hLip hH0 hsc x uInit yin
  let last := OriginalDualOracleProgram.execute (OriginalDualOracleProgram.actualOracle J)
    (OriginalDualOracleProgram.simulator L x v uInit (tau / 4))
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpu := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hlast := OriginalDualOracleProgram.reduced_dual_oracle_simulation J L 0 hL (by norm_num)
    hC2 hLip hH0 x uInit v (tau / 4) (by positivity)
  have hprimal := primal_lipschitz J L hL hJ hLip x v (vStar (JointSliceRegularity.curry J) L x)
  rw [hpu] at hprimal
  have hu : ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ≤ tau / 2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub last.1.u (primal J L x v) (uStar (JointSliceRegularity.curry J) L x)
    have hd : ‖last.1.u - primal J L x v‖ ≤ tau / 4 := hlast.2.1
    linarith only [ht, hd, hprimal, hv]
  have hball : ‖v - yin‖ ≤ D + tau / 4 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub v (vStar (JointSliceRegularity.curry J) L x) yin
    rw [norm_sub_rev (vStar (JointSliceRegularity.curry J) L x) yin] at ht
    linarith only [ht, hwarm, hv]
  have hc := actual_simulator_cost_on_query_ball J L hL hLip x uInit v yin (D + tau / 4)
    (tau / 4) (by positivity) hball
  have hlastCost : last.2 ≤ recoveryQueryBudget J L D tau x uInit yin := by
    apply (Nat.cast_le (α := ℝ)).mp
    exact hc.trans (Nat.le_ceil _)
  have hexec : execute (OriginalDualOracleProgram.actualOracle J) (warmProgram mu L tau x uInit yin) =
      (JointSliceRegularity.point last.1.u v, first.2 + last.2) := by
    simp only [warmProgram, execute_bind, hfirst, recoverProgram, execute_map, execute_liftQuery]
    rfl
  rw [hexec]
  constructor
  · have hn := WithLp.prod_norm_sq_eq_of_L2
      (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)
    have heq : ‖JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x‖ ^ 2 =
        ‖last.1.u - uStar (JointSliceRegularity.curry J) L x‖ ^ 2 +
          ‖v - vStar (JointSliceRegularity.curry J) L x‖ ^ 2 := by
      rw [JointSliceRegularity.point_eq_toLp] at hn ⊢
      exact hn
    have hu2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 2)).mpr hu
    have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ tau / 4)).mpr hv
    nlinarith only [heq, hu2, hv2, htau,
      norm_nonneg (JointSliceRegularity.point last.1.u v - zStar (JointSliceRegularity.curry J) L x)]
  · exact add_le_add hfirstCost hlastCost

end OriginalZeroCurvatureDualWarm


namespace OriginalSecondOrderWarmAll
open _root_.OriginalSecondOrderWarmAll
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable def program (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  if 0 < rho then OriginalActualDualSecondOrderWarm.warmProgram mu L rho D tau x uInit yin
  else OriginalZeroCurvatureDualWarm.warmProgram mu L tau x uInit yin

noncomputable def queryBudget (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℕ :=
  if 0 < rho then OriginalActualDualSecondOrderWarm.warmQueryBudget J mu L rho D tau x uInit yin
  else OriginalZeroCurvatureDualWarm.warmQueryBudget J mu L D tau x uInit yin

theorem actual_second_order_joint_warm_solve
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      run.2 ≤ queryBudget J mu L rho D tau x uInit yin := by
  classical
  by_cases hpos : 0 < rho
  · simpa only [program, queryBudget, if_pos hpos] using
      OriginalActualDualSecondOrderWarm.actual_positive_second_order_joint_warm_solve J mu L rho D tau
        hmu hL hpos htau hC2 hLip hHess hsc x uInit yin hwarm
  · have hrho0 : rho = 0 := le_antisymm (le_of_not_gt hpos) hrho
    have hH0 : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ (0 : ℝ) * ‖z - w‖ := by
      simpa only [hrho0] using hHess
    simpa only [program, queryBudget, if_neg hpos] using
      OriginalZeroCurvatureDualWarm.actual_zero_curvature_joint_warm_solve J mu L D tau
        hmu hL htau hC2 hLip hH0 hsc x uInit yin hwarm

end OriginalSecondOrderWarmAll


namespace OriginalZeroUniformResources
open _root_.OriginalZeroUniformResources

open OriginalBetaSearchEndpoints OriginalCoupledBetaAlgebra OriginalZeroCurvatureSearch

noncomputable section

theorem high_endpoint_lambda_upper (A H : ℝ) (hA : 0 < A) (hH : 0 ≤ H) :
    lambda A (betaHigh A H) ≤ 4 * A + 8 * (1 + H) := by
  have hp := betaHigh_properties A H hA hH
  have hmargin := hp.1
  have hbeta0 : 0 ≤ betaHigh A H := by linarith only [hp.2.2.1]
  have hbeta1 : betaHigh A H ≤ 1 := hp.2.2.2.1.le
  have hsquare : betaHigh A H ^ 2 ≤ 1 := by nlinarith only [hbeta0, hbeta1]
  have heq : 1 - betaHigh A H = highMargin A H := by unfold betaHigh; ring
  have hfirst : lambda A (betaHigh A H) ≤ A / highMargin A H := by
    unfold lambda
    rw [heq]
    apply div_le_div_of_nonneg_right _ hmargin.le
    nlinarith only [mul_le_mul_of_nonneg_left hsquare hA.le]
  refine hfirst.trans ?_
  unfold highMargin
  rcases le_total (1 / 4 : ℝ) (A / (8 * (1 + H))) with hl | hr
  · rw [min_eq_left hl]
    norm_num
    nlinarith only [hH]
  · rw [min_eq_right hr]
    have hid : A / (A / (8 * (1 + H))) = 8 * (1 + H) := by field_simp [ne_of_gt hA]
    rw [hid]
    linarith only [hA]

theorem large_lambda_mono (mu sigma rho G Gmax : ℝ)
    (hmu : 0 < mu) (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (hG : G ≤ Gmax) : largeLambda mu sigma rho G ≤ largeLambda mu sigma rho Gmax := by
  unfold largeLambda
  gcongr

def lambdaCeiling (mu sigma rho Gmax : ℝ) : ℝ :=
  4 + 8 * (1 + largeLambda mu sigma rho Gmax)

theorem initial_lambda_uniform_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (mu Lg sigma rho Gmax : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (x y : E) (a : OriginalBetaATSTrial.Answer E)
    (hGmax : ‖a.grad‖ + 1 + Lg * ‖x - y‖ ≤ Gmax) :
    1 ≤ initialLambda mu Lg 1 sigma rho x y a ∧
      initialLambda mu Lg 1 sigma rho x y a ≤ lambdaCeiling mu sigma rho Gmax := by
  let G := ‖a.grad‖ + 1 + Lg * ‖x - y‖
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hlarge : 1 ≤ largeLambda mu sigma rho G := by
    unfold largeLambda
    have hh : 0 ≤ 2 * ((1 + sigma) * G) / (mu * (1 - sigma) * rho) := by positivity
    linarith only [hh]
  have hp := betaHigh_properties 1 (largeLambda mu sigma rho G) (by norm_num)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlarge)
  have hmono := large_lambda_mono mu sigma rho G Gmax hmu hsigma0 hsigma1 hrho hGmax
  have hu := high_endpoint_lambda_upper 1 (largeLambda mu sigma rho G) (by norm_num)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) hlarge)
  change 1 ≤ lambda 1 (betaHigh 1 (largeLambda mu sigma rho G)) ∧
    lambda 1 (betaHigh 1 (largeLambda mu sigma rho G)) ≤ 4 + 8 * (1 + largeLambda mu sigma rho Gmax)
  refine ⟨hlarge.trans hp.2.2.2.2, ?_⟩
  nlinarith only [hu, hmono]

def toleranceFloor (mu Lg sigma rho Gmax : ℝ) : ℝ :=
  OriginalBetaATSUniform.uniformTolerance mu Lg 0 1 (lambdaCeiling mu sigma rho Gmax) sigma rho

def precisionFloor (mu Lg sigma rho Gmax : ℝ) : ℝ :=
  min 1 (min (toleranceFloor mu Lg sigma rho Gmax) (rho / 8))

theorem initial_tolerance_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (mu Lg sigma rho Gmax : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (x y : E) (a : OriginalBetaATSTrial.Answer E)
    (hGmax : ‖a.grad‖ + 1 + Lg * ‖x - y‖ ≤ Gmax) :
    0 < toleranceFloor mu Lg sigma rho Gmax ∧
      toleranceFloor mu Lg sigma rho Gmax ≤ initialTolerance mu Lg 1 sigma rho x y a := by
  have hlambda := initial_lambda_uniform_bounds mu Lg sigma rho Gmax hmu hLg hsigma0.le hsigma1 hrho x y a hGmax
  have hlam : 0 < initialLambda mu Lg 1 sigma rho x y a := lt_of_lt_of_le zero_lt_one hlambda.1
  have hup : 0 < lambdaCeiling mu sigma rho Gmax := hlam.trans_le hlambda.2
  refine ⟨OriginalBetaATSUniform.uniformTolerance_positive mu Lg 0 1 _ sigma rho
    hmu hLg le_rfl zero_lt_one hup hsigma0 hrho, ?_⟩
  exact OriginalUniformBetaResources.uniform_tolerance_mono mu Lg 0 1 _ _ _ sigma rho
    hmu hLg le_rfl zero_lt_one hlambda.1 hlam hlambda.2 hsigma0 hrho

theorem zero_precision_uniform_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (getter : E × ℝ → OriginalBetaATSTrial.Answer E)
    (mu Lg sigma rho Gmax : ℝ) (hmu : 0 < mu) (hLg : 0 ≤ Lg)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1) (hrho : 0 < rho)
    (x y : E)
    (hGmax : ‖(getter (y, 1)).grad‖ + 1 + Lg * ‖x - y‖ ≤ Gmax) :
    0 < precisionFloor mu Lg sigma rho Gmax ∧ precisionFloor mu Lg sigma rho Gmax ≤
      zeroPrecisionFloor getter mu Lg 1 sigma rho (rho / 8) x y := by
  have ht := initial_tolerance_uniform_bound mu Lg sigma rho Gmax hmu hLg hsigma0 hsigma1 hrho
    x y (getter (y, 1)) hGmax
  exact ⟨lt_min zero_lt_one (lt_min ht.1 (by positivity)), min_le_min le_rfl (min_le_min ht.2 le_rfl)⟩

end
end OriginalZeroUniformResources


namespace CertifiedFirstOrder
open _root_.CertifiedFirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable section

structure State (E : Type*) where
  weight : ℝ
  x : E
  y : E

def increment (lam A : ℝ) : ℝ :=
  (lam + Real.sqrt (lam ^ 2 + 4 * lam * A)) / 2

def center (lam : ℝ) (s : State E) : E :=
  (s.weight / (s.weight + increment lam s.weight)) • s.y +
    (increment lam s.weight / (s.weight + increment lam s.weight)) • s.x

def next (lam : ℝ) (s : State E) (gz vy : E) : State E :=
  ⟨s.weight + increment lam s.weight,
    s.x - increment lam s.weight • vy, center lam s - lam • gz⟩

def centerTolerance (mu D : ℝ) : ℝ := mu * D / 64

inductive Program (E R : Type*) where
  | pure : R → Program E R
  | ask : E → ℝ → (E → Program E R) → Program E R

def execute {R : Type*} (oracle : E → ℝ → E) : Program E R → R × ℕ
  | .pure r => (r, 0)
  | .ask z delta cont =>
      let result := execute oracle (cont (oracle z delta))
      (result.1, result.2 + 1)

def contractionProgram (mu L D : ℝ) : ℕ → State E → Program E (Sum E (State E))
  | 0, s => .pure (.inr s)
  | n + 1, s =>
      let lam := (2 * L)⁻¹
      let z := center lam s
      .ask z (centerTolerance mu D) (fun gz =>
        if ‖gz‖ + centerTolerance mu D ≤ mu * D / 2 then .pure (.inl z)
        else
          let y := z - lam • gz
          let delta := RobustAHPE.outputGradientTolerance mu lam (3 / 64) ‖y - z‖
          .ask y delta (fun vy => contractionProgram mu L D n (next lam s gz vy)))

theorem weight_growth_step (lam A : ℝ) (k : ℕ) (hlam : 0 < lam)
    (hA : 0 ≤ A) (hbound : lam * (k : ℝ) ^ 2 / 4 ≤ A) :
    lam * ((k + 1 : ℕ) : ℝ) ^ 2 / 4 ≤ A + increment lam A := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hrad : 0 ≤ lam ^ 2 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (lam ^ 2 + 4 * lam * A)
  have hm := mul_le_mul_of_nonneg_left hbound hlam.le
  have hlow : lam * (k : ℝ) ≤ Real.sqrt (lam ^ 2 + 4 * lam * A) := by
    nlinarith only [hs, hn, hm, mul_nonneg hlam.le hk]
  simp only [Nat.cast_add, Nat.cast_one]
  unfold increment
  nlinarith only [hbound, hlow, hlam]

theorem center_scaled (lam : ℝ) (s : State E) (hA : 0 ≤ s.weight) (hlam : 0 < lam) :
    (s.weight + increment lam s.weight) • center lam s =
      s.weight • s.y + increment lam s.weight • s.x := by
  have hp := LargeStepAHPE.a_formula_properties s.weight lam hA hlam
  change 0 < increment lam s.weight ∧ 0 < s.weight + increment lam s.weight ∧
    _ at hp
  have h1 : (s.weight + increment lam s.weight) *
      (s.weight / (s.weight + increment lam s.weight)) = s.weight := by
    field_simp [ne_of_gt hp.2.1]
  have h2 : (s.weight + increment lam s.weight) *
      (increment lam s.weight / (s.weight + increment lam s.weight)) =
        increment lam s.weight := by field_simp [ne_of_gt hp.2.1]
  simp only [center, smul_add, smul_smul, h1, h2]

theorem center_query_outcomes
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hL : 0 < L) (hD : 0 < D)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (z gz : E) (herror : ‖gz - gradient g z‖ ≤ centerTolerance mu D)
    (haway : ¬ ‖gz‖ + centerTolerance mu D ≤ mu * D / 2) :
    let lam := (2 * L)⁻¹
    let d := -lam • gz
    0 < ‖d‖ ∧
      ‖lam • gradient g (z + d) + d‖ ≤ (9 / 16 : ℝ) * ‖d‖ := by
  dsimp only
  let lam := (2 * L)⁻¹
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hscale : lam * L = 1 / 2 := by dsimp only [lam]; field_simp <;> ring
  have htolpos : 0 < centerTolerance mu D := by unfold centerTolerance; positivity
  have hgz : 16 * centerTolerance mu D ≤ ‖gz‖ := by
    unfold centerTolerance at *
    linarith only [lt_of_not_ge haway, mul_pos hmu hD]
  have hgpos : 0 < ‖gz‖ := lt_of_lt_of_le (by positivity) hgz
  have hd : ‖-lam • gz‖ = lam * ‖gz‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hlam]
  refine ⟨by rw [hd]; positivity, ?_⟩
  have herror' : ‖gradient g z - gz‖ ≤ centerTolerance mu D := by
    simpa only [norm_sub_rev] using herror
  have hdiff := hgrad (z + -lam • gz) z
  simp only [add_sub_cancel_left] at hdiff
  have he : lam • gradient g (z + -lam • gz) + -lam • gz =
      lam • (gradient g (z + -lam • gz) - gradient g z) +
        lam • (gradient g z - gz) := by module
  have hn := norm_add_le (lam • (gradient g (z + -lam • gz) - gradient g z))
    (lam • (gradient g z - gz))
  rw [← he] at hn
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hlam] at hn
  have hm1 := mul_le_mul_of_nonneg_left hdiff hlam.le
  rw [← mul_assoc, hscale] at hm1
  have hm2 := mul_le_mul_of_nonneg_left herror' hlam.le
  have hm3 := mul_le_mul_of_nonneg_left hgz hlam.le
  change ‖lam • gradient g (z + -lam • gz) + -lam • gz‖ ≤ (9 / 16 : ℝ) * ‖-lam • gz‖
  nlinarith only [hn, hm1, hm2, hm3, hd]

theorem nonterminal_step
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hL : 0 < L) (hD : 0 < D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (s : State E) (hA : 0 ≤ s.weight) (gz vy : E)
    (hzerror : ‖gz - gradient g (center ((2 * L)⁻¹) s)‖ ≤ centerTolerance mu D)
    (haway : ¬ ‖gz‖ + centerTolerance mu D ≤ mu * D / 2)
    (hyerror : ‖vy - gradient g (center ((2 * L)⁻¹) s - (2 * L)⁻¹ • gz)‖ ≤
      RobustAHPE.outputGradientTolerance mu ((2 * L)⁻¹) (3 / 64)
        ‖(center ((2 * L)⁻¹) s - (2 * L)⁻¹ • gz) - center ((2 * L)⁻¹) s‖)
    (xstar : E) :
    0 < RobustAHPE.outputGradientTolerance mu ((2 * L)⁻¹) (3 / 64)
        ‖(next ((2 * L)⁻¹) s gz vy).y - center ((2 * L)⁻¹) s‖ ∧
    0 ≤ (next ((2 * L)⁻¹) s gz vy).weight ∧
    LargeStepAHPE.potential g (next ((2 * L)⁻¹) s gz vy).weight
        (next ((2 * L)⁻¹) s gz vy).x (next ((2 * L)⁻¹) s gz vy).y xstar ≤
      LargeStepAHPE.potential g s.weight s.x s.y xstar := by
  let lam := (2 * L)⁻¹
  let z := center lam s
  let y := z - lam • gz
  let d := y - z
  let delta := RobustAHPE.outputGradientTolerance mu lam (3 / 64) ‖d‖
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hdeq : d = -lam • gz := by dsimp only [d, y]; module
  have hyeq : z + d = y := by dsimp only [d]; abel
  have hout := center_query_outcomes g mu L D hmu hL hD hgrad z gz hzerror haway
  change 0 < ‖-lam • gz‖ ∧ _ at hout
  rw [← hdeq, hyeq] at hout
  have hdelta : 0 < delta := RobustAHPE.outputGradientTolerance_positive mu lam
    (3 / 64) ‖d‖ hmu hlam (by norm_num) hout.1
  have ht := RobustAHPE.outputGradientTolerance_suffices mu lam (3 / 64) ‖d‖ delta
    hmu hlam (by norm_num) (norm_nonneg _) hdelta.le le_rfl
  have hcert := RobustAHPE.enlarged_gradient_relative_certificate g mu lam (9 / 16)
    (3 / 64) (3 / 4) delta hmu hlam (by norm_num) (by norm_num) (by norm_num)
    hdiff hsc y d vy hyerror hout.2 ht.1 ht.2
  have hp := LargeStepAHPE.a_formula_properties s.weight lam hA hlam
  change 0 < increment lam s.weight ∧ 0 < s.weight + increment lam s.weight ∧ _ at hp
  have hsub : LargeStepAHPE.EpsilonSubgradient g y vy (delta ^ 2 / (2 * mu)) := hcert.1
  have hstep := LargeStepAHPE.one_step_potential g s.weight
    (s.weight + increment lam s.weight) (increment lam s.weight) lam (3 / 4)
    (delta ^ 2 / (2 * mu)) s.x s.y (s.x - increment lam s.weight • vy) y z vy xstar
    hA hp.2.1 hp.1.le hlam rfl hp.2.2 (center_scaled lam s hA hlam) rfl hsub hcert.2
  have hnonneg : 0 ≤ ((1 - (3 / 4 : ℝ) ^ 2) / 2) *
      ((s.weight + increment lam s.weight) / lam) * ‖y - z‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hp.2.1.le hlam.le)) (sq_nonneg _)
  refine ⟨hdelta, hp.2.1.le, ?_⟩
  change LargeStepAHPE.potential g (s.weight + increment lam s.weight)
    (s.x - increment lam s.weight • vy) y xstar ≤ _
  linarith only [hstep, hnonneg]

def OutcomeInvariant (g : E → ℝ) (lam D : ℝ) (xstar : E) (k : ℕ) :
    Sum E (State E) → Prop
  | .inl z => ‖z - xstar‖ ≤ D / 2
  | .inr s => 0 ≤ s.weight ∧ lam * (k : ℝ) ^ 2 / 4 ≤ s.weight ∧
      LargeStepAHPE.potential g s.weight s.x s.y xstar ≤ D ^ 2 / 2

theorem program_spec
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hL : 0 < L) (hD : 0 < D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (oracle : E → ℝ → E)
    (hvalid : ∀ z delta, 0 < delta → ‖oracle z delta - gradient g z‖ ≤ delta)
    (xstar : E) (hmin : ∀ z : E, g xstar ≤ g z)
    (n k : ℕ) (s : State E) (hA : 0 ≤ s.weight)
    (hbound : (2 * L)⁻¹ * (k : ℝ) ^ 2 / 4 ≤ s.weight)
    (hpot : LargeStepAHPE.potential g s.weight s.x s.y xstar ≤ D ^ 2 / 2) :
    (execute oracle (contractionProgram mu L D n s)).2 ≤ 2 * n ∧
      OutcomeInvariant g ((2 * L)⁻¹) D xstar (k + n)
        (execute oracle (contractionProgram mu L D n s)).1 := by
  induction n generalizing k s with
  | zero => simpa only [contractionProgram, execute, Nat.add_zero, OutcomeInvariant]
      using And.intro (show 0 ≤ 2 * 0 by omega) ⟨hA, hbound, hpot⟩
  | succ n ih =>
      let lam := (2 * L)⁻¹
      let z := center lam s
      let gz := oracle z (centerTolerance mu D)
      have hlam : 0 < lam := by dsimp only [lam]; positivity
      have htol : 0 < centerTolerance mu D := by unfold centerTolerance; positivity
      have hzerror := hvalid z (centerTolerance mu D) htol
      change ‖gz - gradient g z‖ ≤ centerTolerance mu D at hzerror
      by_cases hstop : ‖gz‖ + centerTolerance mu D ≤ mu * D / 2
      · have htrue : ‖gradient g z‖ ≤ mu * D / 2 := by
          have hh := norm_sub_le gz (gz - gradient g z)
          have he : gz - (gz - gradient g z) = gradient g z := by abel
          rw [he] at hh
          linarith only [hh, hzerror, hstop]
        have hd := RobustAHPE.small_gradient_contracts_distance g mu D hmu hdiff hsc
          xstar z hmin htrue
        have hstop' := hstop
        dsimp only [gz, z, lam] at hstop'
        simp only [contractionProgram, execute, if_pos hstop', OutcomeInvariant]
        exact ⟨by omega, hd⟩
      · have hout := center_query_outcomes g mu L D hmu hL hD hgrad z gz hzerror hstop
        let y := z - lam • gz
        let delta := RobustAHPE.outputGradientTolerance mu lam (3 / 64) ‖y - z‖
        have hdeq : y - z = -lam • gz := by dsimp only [y]; module
        have hr : 0 < ‖y - z‖ := by simpa only [hdeq] using hout.1
        have hdelta : 0 < delta := RobustAHPE.outputGradientTolerance_positive mu lam
          (3 / 64) ‖y - z‖ hmu hlam (by norm_num) hr
        let vy := oracle y delta
        have hyerror := hvalid y delta hdelta
        have hs := nonterminal_step g mu L D hmu hL hD hdiff hsc hgrad s hA gz vy
          hzerror hstop hyerror xstar
        have hgrowth := weight_growth_step lam s.weight k hlam hA hbound
        have hrec := ih (k + 1) (next lam s gz vy) hs.2.1 hgrowth (le_trans hs.2.2 hpot)
        have hindex : k + (n + 1) = (k + 1) + n := by omega
        rw [hindex]
        have hstop' := hstop
        dsimp only [gz, z, lam] at hstop'
        simp only [contractionProgram, execute, if_neg hstop']
        change (execute oracle (contractionProgram mu L D n (next lam s gz vy))).2 + 1 + 1 ≤
          2 * (n + 1) ∧ OutcomeInvariant g ((2 * L)⁻¹) D xstar ((k + 1) + n)
            (execute oracle (contractionProgram mu L D n (next lam s gz vy))).1
        exact ⟨by omega, hrec.2⟩

def iterationCount (mu L : ℝ) : ℕ := ⌈8 * Real.sqrt (L / mu)⌉₊

def resultPoint : Sum E (State E) → E
  | .inl z => z
  | .inr s => s.y

theorem iteration_count_bounds (mu L : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) :
    64 * (L / mu) ≤ (iterationCount mu L : ℝ) ^ 2 ∧
      (2 * iterationCount mu L : ℕ) ≤ 18 * Real.sqrt (L / mu) := by
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have hratio : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by linarith only [hLmu])
  have hsqrt := Real.sqrt_nonneg (L / mu)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ L / mu)
  have hsqrt1 : 1 ≤ Real.sqrt (L / mu) := by nlinarith only [hsqrt, hsq, hratio]
  have hlower : 8 * Real.sqrt (L / mu) ≤ (iterationCount mu L : ℝ) :=
    Nat.le_ceil _
  have hupper : (iterationCount mu L : ℝ) < 8 * Real.sqrt (L / mu) + 1 :=
    Nat.ceil_lt_add_one (show 0 ≤ 8 * Real.sqrt (L / mu) by positivity)
  constructor
  · nlinarith only [hlower, hsqrt, hsq,
      (show 0 ≤ (iterationCount mu L : ℝ) by positivity)]
  · push_cast
    nlinarith only [hupper, hsqrt1]

theorem first_order_contraction_program
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hD : 0 < D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (oracle : E → ℝ → E)
    (hvalid : ∀ z delta, 0 < delta → ‖oracle z delta - gradient g z‖ ≤ delta)
    (xstar start : E) (hmin : ∀ z : E, g xstar ≤ g z) (hstart : ‖start - xstar‖ ≤ D) :
    let initial : State E := ⟨0, start, start⟩
    let run := execute oracle (contractionProgram mu L D (iterationCount mu L) initial)
    ‖resultPoint run.1 - xstar‖ ≤ D / 2 ∧
      (run.2 : ℝ) ≤ 18 * Real.sqrt (L / mu) := by
  dsimp only
  let initial : State E := ⟨0, start, start⟩
  let n := iterationCount mu L
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have hpot : LargeStepAHPE.potential g initial.weight initial.x initial.y xstar ≤ D ^ 2 / 2 := by
    simp only [initial, LargeStepAHPE.potential, zero_mul, zero_add]
    nlinarith only [hstart, norm_nonneg (start - xstar)]
  have hrun := program_spec g mu L D hmu hL hD hdiff hsc hgrad oracle hvalid xstar hmin
    n 0 initial (by norm_num [initial]) (by norm_num [initial]) hpot
  simp only [Nat.zero_add] at hrun
  have hn := iteration_count_bounds mu L hmu hLmu
  refine ⟨?_, le_trans (by exact_mod_cast hrun.1) hn.2⟩
  generalize he : (execute oracle (contractionProgram mu L D n initial)).1 = out at hrun ⊢
  cases out with
  | inl z => exact hrun.2
  | inr s =>
      have hg0 := PacketCore.gradient_eq_zero_at_global_min g xstar hmin
      have hlower := PacketCore.strongConvex_support g mu hsc hdiff xstar s.y
      rw [hg0, inner_zero_left, add_zero] at hlower
      have hpotential := hrun.2.2.2
      dsimp only [LargeStepAHPE.potential] at hpotential
      have hm := mul_le_mul_of_nonneg_left hlower hrun.2.1
      have hweight : 8 ≤ s.weight * mu := by
        have hw := mul_le_mul_of_nonneg_right hrun.2.2.1 hmu.le
        have hnorm : ((2 * L)⁻¹ * (n : ℝ) ^ 2 / 4) * mu =
            (n : ℝ) ^ 2 / (8 * (L / mu)) := by field_simp <;> ring
        rw [hnorm] at hw
        have hratio : 0 < L / mu := div_pos hL hmu
        have hn8 : 8 ≤ (n : ℝ) ^ 2 / (8 * (L / mu)) :=
          (le_div_iff₀ (by positivity)).mpr (by nlinarith only [hn.1])
        exact le_trans hn8 hw
      have hdist := sq_nonneg ‖s.x - xstar‖
      have hmul := mul_le_mul_of_nonneg_right hweight (sq_nonneg ‖s.y - xstar‖)
      change ‖s.y - xstar‖ ≤ D / 2
      nlinarith only [hm, hpotential, hdist, hmul, norm_nonneg (s.y - xstar), hD]

end
end CertifiedFirstOrder


namespace CertifiedFirstOrder
open _root_.CertifiedFirstOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable section

def queryRadius (mu L D : ℝ) : ℝ := 2 * Real.sqrt (L / mu) * D

def precisionFloor (mu L D : ℝ) : ℝ :=
  (3 / 64) * (2 * L)⁻¹ * centerTolerance mu D *
    min ((2 * L)⁻¹)⁻¹ (min 1 (mu / ((2 * L)⁻¹)))

def QueriesSatisfy {R : Type*} (oracle : E → ℝ → E) (P : E → ℝ → Prop) :
    Program E R → Prop
  | .pure _ => True
  | .ask z delta cont => P z delta ∧ QueriesSatisfy oracle P (cont (oracle z delta))

theorem precision_floor_bounds (mu L D : ℝ) (hmu : 0 < mu) (hL : 0 < L) (hD : 0 < D) :
    0 < precisionFloor mu L D ∧ precisionFloor mu L D ≤ centerTolerance mu D := by
  let lam := (2 * L)⁻¹
  let c := min lam⁻¹ (min 1 (mu / lam))
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have htol : 0 < centerTolerance mu D := by unfold centerTolerance; positivity
  have hcl : lam * c ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_left lam⁻¹ (min 1 (mu / lam))) hlam.le
    rw [mul_inv_cancel₀ (ne_of_gt hlam)] at hh
    exact hh
  change 0 < (3 / 64 : ℝ) * lam * centerTolerance mu D * c ∧ _
  refine ⟨by positivity, ?_⟩
  have hh := mul_le_mul_of_nonneg_right hcl htol.le
  change (3 / 64 : ℝ) * lam * centerTolerance mu D * c ≤ _
  nlinarith only [hh, htol]

theorem increment_ge_lambda (lam A : ℝ) (hlam : 0 < lam) (hA : 0 ≤ A) :
    lam ≤ increment lam A := by
  have hrad : 0 ≤ lam ^ 2 + 4 * lam * A := by positivity
  have hs := Real.sq_sqrt hrad
  have hn := Real.sqrt_nonneg (lam ^ 2 + 4 * lam * A)
  have hroot : lam ≤ Real.sqrt (lam ^ 2 + 4 * lam * A) := by
    nlinarith only [hs, hn, hlam, mul_nonneg hlam.le hA]
  unfold increment
  linarith only [hroot]

theorem center_distance_bound (lam B : ℝ) (s : State E) (xstar : E)
    (hlam : 0 < lam) (hA : 0 ≤ s.weight)
    (hx : ‖s.x - xstar‖ ≤ B) (hy : ‖s.y - xstar‖ ≤ B) :
    ‖center lam s - xstar‖ ≤ B := by
  let a := increment lam s.weight
  have hp := LargeStepAHPE.a_formula_properties s.weight lam hA hlam
  change 0 < a ∧ 0 < s.weight + a ∧ _ at hp
  let cy := s.weight / (s.weight + a)
  let cx := a / (s.weight + a)
  have hcy : 0 ≤ cy := div_nonneg hA hp.2.1.le
  have hcx : 0 ≤ cx := div_nonneg hp.1.le hp.2.1.le
  have hsum : cy + cx = 1 := by dsimp only [cy, cx]; field_simp [ne_of_gt hp.2.1]
  have he : cy • (s.y - xstar) + cx • (s.x - xstar) = center lam s - xstar := by
    calc
      _ = (cy • s.y + cx • s.x) - (cy + cx) • xstar := by module
      _ = _ := by rw [hsum, one_smul]; rfl
  have hn := norm_add_le (cy • (s.y - xstar)) (cx • (s.x - xstar))
  rw [he, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hcy, abs_of_nonneg hcx] at hn
  have hy' := mul_le_mul_of_nonneg_left hy hcy
  have hx' := mul_le_mul_of_nonneg_left hx hcx
  have hsumB := congrArg (fun r : ℝ => r * B) hsum
  nlinarith only [hn, hy', hx', hsumB]

theorem potential_point_bounds
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hD : 0 < D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (xstar : E) (hmin : ∀ z : E, g xstar ≤ g z)
    (s : State E) (hA : 0 ≤ s.weight)
    (hpot : LargeStepAHPE.potential g s.weight s.x s.y xstar ≤ D ^ 2 / 2) :
    ‖s.x - xstar‖ ≤ D ∧
      ((2 * L)⁻¹ ≤ s.weight → ‖s.y - xstar‖ ≤ queryRadius mu L D) := by
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have hgap : 0 ≤ g s.y - g xstar := sub_nonneg.mpr (hmin _)
  have hgapA := mul_nonneg hA hgap
  dsimp only [LargeStepAHPE.potential] at hpot
  refine ⟨by nlinarith only [hpot, hgapA, norm_nonneg (s.x - xstar), hD], ?_⟩
  intro hlambda
  have hg0 := PacketCore.gradient_eq_zero_at_global_min g xstar hmin
  have hs := PacketCore.strongConvex_support g mu hsc hdiff xstar s.y
  rw [hg0, inner_zero_left, add_zero] at hs
  have hm := mul_le_mul_of_nonneg_left hs hA
  have hr := mul_le_mul_of_nonneg_right hlambda (mul_nonneg hmu.le (sq_nonneg ‖s.y - xstar‖))
  have hnonneg := sq_nonneg ‖s.x - xstar‖
  have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ L / mu)
  have hradius : 0 < queryRadius mu L D := by unfold queryRadius; positivity
  have hradid : (2 * L)⁻¹ * mu * (queryRadius mu L D) ^ 2 = 2 * D ^ 2 := by
    unfold queryRadius
    calc
      _ = (2 * L)⁻¹ * mu * (4 * (Real.sqrt (L / mu)) ^ 2 * D ^ 2) := by ring
      _ = _ := by rw [hsqrt]; field_simp <;> ring
  have hcoef : 0 < (2 * L)⁻¹ * mu := by positivity
  have hsq : ‖s.y - xstar‖ ^ 2 ≤ (queryRadius mu L D) ^ 2 := by
    apply (mul_le_mul_iff_right₀ hcoef).mp
    nlinarith only [hm, hr, hpot, hnonneg, hradid, sq_nonneg D]
  exact (sq_le_sq₀ (norm_nonneg _) hradius.le).mp hsq

theorem nonterminal_query_bounds
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hD : 0 < D)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (xstar : E) (hzero : gradient g xstar = 0) (z gz : E)
    (hz : ‖z - xstar‖ ≤ queryRadius mu L D)
    (herror : ‖gz - gradient g z‖ ≤ centerTolerance mu D)
    (haway : ¬ ‖gz‖ + centerTolerance mu D ≤ mu * D / 2) :
    let y := z - (2 * L)⁻¹ • gz
    ‖y - xstar‖ ≤ 2 * queryRadius mu L D ∧
      precisionFloor mu L D ≤
        RobustAHPE.outputGradientTolerance mu ((2 * L)⁻¹) (3 / 64) ‖y - z‖ := by
  dsimp only
  let lam := (2 * L)⁻¹
  let B := queryRadius mu L D
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hscale : lam * L = 1 / 2 := by dsimp only [lam]; field_simp <;> ring
  have hratio : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa only [one_mul] using hLmu)
  have hsqrt := Real.sqrt_nonneg (L / mu)
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ L / mu)
  have hsqrt1 : 1 ≤ Real.sqrt (L / mu) := by nlinarith only [hsqrt, hsq, hratio]
  have hBD : D ≤ B := by dsimp only [B, queryRadius]; nlinarith only [hD, hsqrt1]
  have hzB : ‖z - xstar‖ ≤ B := hz
  have htolpos : 0 < centerTolerance mu D := by unfold centerTolerance; positivity
  have hgz : centerTolerance mu D ≤ ‖gz‖ := by
    unfold centerTolerance at *
    linarith only [lt_of_not_ge haway, mul_pos hmu hD]
  have hstep : ‖(z - lam • gz) - z‖ = lam * ‖gz‖ := by
    have he : z - lam • gz - z = -lam • gz := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hlam]
  constructor
  · have hgradz := hgrad z xstar
    rw [hzero, sub_zero] at hgradz
    have hgnorm := norm_sub_le (gz - gradient g z) (-gradient g z)
    have he : (gz - gradient g z) - -gradient g z = gz := by abel
    rw [he, norm_neg] at hgnorm
    have hgupper : ‖gz‖ ≤ L * B + centerTolerance mu D := by
      have hh := mul_le_mul_of_nonneg_left hzB hL.le
      nlinarith only [hgnorm, herror, hgradz, hh]
    have htri := norm_sub_le_norm_sub_add_norm_sub (z - lam • gz) z xstar
    rw [hstep] at htri
    have hmul := mul_le_mul_of_nonneg_left hgupper hlam.le
    rw [mul_add, ← mul_assoc, hscale] at hmul
    have htolsmall : lam * centerTolerance mu D ≤ D / 128 := by
      have hh : lam * mu ≤ 1 / 2 := by
        have hh := mul_le_mul_of_nonneg_left hLmu hlam.le
        rw [hscale] at hh
        exact hh
      unfold centerTolerance
      nlinarith only [mul_le_mul_of_nonneg_right hh hD.le]
    change ‖z - lam • gz - xstar‖ ≤ 2 * B
    nlinarith only [htri, hmul, htolsmall, hzB, hBD, hD]
  · have hc : 0 ≤ min lam⁻¹ (min 1 (mu / lam)) := by positivity
    have hh := mul_le_mul_of_nonneg_left hgz hlam.le
    have hm := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 64) hc)
    change precisionFloor mu L D ≤ RobustAHPE.outputGradientTolerance mu lam (3 / 64)
      ‖(z - lam • gz) - z‖
    rw [hstep]
    dsimp only [precisionFloor, RobustAHPE.outputGradientTolerance]
    convert! hm using 1 <;> ring

theorem query_radius_ge_initial (mu L D : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L)
    (hD : 0 ≤ D) : D ≤ queryRadius mu L D := by
  have hr : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa only [one_mul] using hLmu)
  have hs := Real.sqrt_nonneg (L / mu)
  have hsq := Real.sq_sqrt (le_trans (by norm_num : (0 : ℝ) ≤ 1) hr)
  have hs1 : 1 ≤ Real.sqrt (L / mu) := by nlinarith only [hr, hs, hsq]
  unfold queryRadius
  nlinarith only [mul_le_mul_of_nonneg_right hs1 hD, hD]

theorem program_queries_bounded
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hD : 0 < D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (oracle : E → ℝ → E)
    (hvalid : ∀ z delta, 0 < delta → ‖oracle z delta - gradient g z‖ ≤ delta)
    (xstar : E) (hmin : ∀ z : E, g xstar ≤ g z)
    (n : ℕ) (s : State E) (hA : 0 ≤ s.weight)
    (hpot : LargeStepAHPE.potential g s.weight s.x s.y xstar ≤ D ^ 2 / 2)
    (hy : ‖s.y - xstar‖ ≤ queryRadius mu L D) :
    QueriesSatisfy oracle (fun z delta =>
      ‖z - xstar‖ ≤ 2 * queryRadius mu L D ∧ precisionFloor mu L D ≤ delta)
      (contractionProgram mu L D n s) := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
      let lam := (2 * L)⁻¹
      let z := center lam s
      let gz := oracle z (centerTolerance mu D)
      have hL : 0 < L := lt_of_lt_of_le hmu hLmu
      have hlam : 0 < lam := by dsimp only [lam]; positivity
      have hfloor := precision_floor_bounds mu L D hmu hL hD
      have hDB := query_radius_ge_initial mu L D hmu hLmu hD.le
      have hB : 0 < queryRadius mu L D := lt_of_lt_of_le hD hDB
      have hpoints := potential_point_bounds g mu L D hmu hLmu hD hdiff hsc xstar hmin s hA hpot
      have hz := center_distance_bound lam (queryRadius mu L D) s xstar hlam hA
        (le_trans hpoints.1 hDB) hy
      have hzerror := hvalid z (centerTolerance mu D) (lt_of_lt_of_le hfloor.1 hfloor.2)
      change ‖gz - gradient g z‖ ≤ centerTolerance mu D at hzerror
      change (‖z - xstar‖ ≤ 2 * queryRadius mu L D ∧
          precisionFloor mu L D ≤ centerTolerance mu D) ∧
        QueriesSatisfy oracle (fun z delta =>
          ‖z - xstar‖ ≤ 2 * queryRadius mu L D ∧ precisionFloor mu L D ≤ delta)
          (if ‖gz‖ + centerTolerance mu D ≤ mu * D / 2 then .pure (.inl z)
           else .ask (z - lam • gz)
             (RobustAHPE.outputGradientTolerance mu lam (3 / 64) ‖(z - lam • gz) - z‖)
             (fun vy => contractionProgram mu L D n (next lam s gz vy)))
      refine ⟨⟨by change ‖z - xstar‖ ≤ _; linarith only [hz, hB], hfloor.2⟩, ?_⟩
      split_ifs with hstop
      · trivial
      · let y := z - lam • gz
        let delta := RobustAHPE.outputGradientTolerance mu lam (3 / 64) ‖y - z‖
        let vy := oracle y delta
        have hzero := PacketCore.gradient_eq_zero_at_global_min g xstar hmin
        have hquery := nonterminal_query_bounds g mu L D hmu hLmu hD hgrad xstar hzero z gz
          hz hzerror hstop
        have hdelta : 0 < delta := lt_of_lt_of_le hfloor.1 hquery.2
        have hyerror := hvalid y delta hdelta
        have hs := nonterminal_step g mu L D hmu hL hD hdiff hsc hgrad s hA gz vy hzerror
          hstop hyerror xstar
        have hpot' := le_trans hs.2.2 hpot
        have hnextweight : lam ≤ (next lam s gz vy).weight := by
          have hh := increment_ge_lambda lam s.weight hlam hA
          change lam ≤ s.weight + increment lam s.weight
          linarith only [hh, hA]
        have hnexty := (potential_point_bounds g mu L D hmu hLmu hD hdiff hsc xstar hmin
          (next lam s gz vy) hs.2.1 hpot').2 hnextweight
        change (‖y - xstar‖ ≤ 2 * queryRadius mu L D ∧ precisionFloor mu L D ≤ delta) ∧ _
        exact ⟨hquery, ih (next lam s gz vy) hs.2.1 hpot' hnexty⟩

theorem initial_program_queries_bounded
    (g : E → ℝ) (mu L D : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hD : 0 < D)
    (hdiff : Differentiable ℝ g) (hsc : StrongConvexOn (Set.univ : Set E) mu g)
    (hgrad : ∀ x y : E, ‖gradient g x - gradient g y‖ ≤ L * ‖x - y‖)
    (oracle : E → ℝ → E)
    (hvalid : ∀ z delta, 0 < delta → ‖oracle z delta - gradient g z‖ ≤ delta)
    (xstar start : E) (hmin : ∀ z : E, g xstar ≤ g z) (hstart : ‖start - xstar‖ ≤ D)
    (n : ℕ) :
    QueriesSatisfy oracle (fun z delta =>
      ‖z - xstar‖ ≤ 2 * queryRadius mu L D ∧ precisionFloor mu L D ≤ delta)
      (contractionProgram mu L D n ⟨0, start, start⟩) := by
  apply program_queries_bounded g mu L D hmu hLmu hD hdiff hsc hgrad oracle hvalid xstar hmin n
    ⟨0, start, start⟩ (by norm_num)
  · simp only [LargeStepAHPE.potential, zero_mul, zero_add]
    nlinarith only [hstart, norm_nonneg (start - xstar)]
  · exact le_trans hstart (query_radius_ge_initial mu L D hmu hLmu hD.le)

end
end CertifiedFirstOrder


namespace CertifiedFirstOrderLowering
open _root_.CertifiedFirstOrderLowering

open OriginalDualOracleProgram

noncomputable section

def qbind {Z A R S : Type*} : QueryProgram Z A R → (R → QueryProgram Z A S) → QueryProgram Z A S
  | .pure r, cont => cont r
  | .ask z next, cont => .ask z (fun answer => qbind (next answer) cont)

theorem execute_qbind {Z A R S : Type*} (oracle : Z → A)
    (p : QueryProgram Z A R) (cont : R → QueryProgram Z A S) :
    execute oracle (qbind p cont) =
      let first := execute oracle p
      let second := execute oracle (cont first.1)
      (second.1, first.2 + second.2) := by
  induction p with
  | pure r => simp only [qbind, execute, zero_add]
  | ask z next ih =>
      simp only [qbind, execute, ih]
      congr 1 <;> omega

def lower {F Z A R : Type*} (getter : F → ℝ → QueryProgram Z A F) :
    CertifiedFirstOrder.Program F R → QueryProgram Z A R
  | .pure r => .pure r
  | .ask z delta cont => qbind (getter z delta) (fun value => lower getter (cont value))

def getterResponse {F Z A : Type*} (oracle : Z → A)
    (getter : F → ℝ → QueryProgram Z A F) (z : F) (delta : ℝ) : F :=
  (execute oracle (getter z delta)).1

theorem lower_result {F Z A R : Type*} (oracle : Z → A)
    (getter : F → ℝ → QueryProgram Z A F) (p : CertifiedFirstOrder.Program F R) :
    (execute oracle (lower getter p)).1 =
      (CertifiedFirstOrder.execute (getterResponse oracle getter) p).1 := by
  induction p with
  | pure r => rfl
  | ask z delta cont ih =>
      simp only [lower, execute_qbind, CertifiedFirstOrder.execute]
      exact ih _

theorem lower_count {F Z A R : Type*} (oracle : Z → A)
    (getter : F → ℝ → QueryProgram Z A F) (p : CertifiedFirstOrder.Program F R)
    (P : F → ℝ → Prop) (C : ℝ)
    (hcost : ∀ z delta, P z delta → ((execute oracle (getter z delta)).2 : ℝ) ≤ C)
    (hqueries : CertifiedFirstOrder.QueriesSatisfy (getterResponse oracle getter) P p) :
    ((execute oracle (lower getter p)).2 : ℝ) ≤
      C * (CertifiedFirstOrder.execute (getterResponse oracle getter) p).2 := by
  induction p with
  | pure r => simp only [lower, execute, CertifiedFirstOrder.execute, Nat.cast_zero, mul_zero, le_refl]
  | ask z delta cont ih =>
      have hfirst := hcost z delta hqueries.1
      have htail := ih (getterResponse oracle getter z delta) hqueries.2
      simp only [lower, execute_qbind, CertifiedFirstOrder.execute, Nat.cast_add, Nat.cast_one]
      change ((execute oracle (getter z delta)).2 : ℝ) +
        ((execute oracle (lower getter (cont (getterResponse oracle getter z delta)))).2 : ℝ) ≤ _
      nlinarith only [hfirst, htail]

end
end CertifiedFirstOrderLowering


namespace OriginalDualFirstOrder
open _root_.OriginalDualFirstOrder

open OriginalSaddleImplicit OriginalPrimalElimination OriginalDualCurvature
open OriginalDualOracleEstimates OriginalDualOracleProgram
open CertifiedFirstOrderLowering

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section

def gradientGetter (L rho : ℝ) (x u0 : E) (v : F) (delta : ℝ) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) F :=
  qbind (simulator L x v u0 (min 1 (delta / (1 + 3 * L + 4 * rho))))
    (fun s => .pure (gradientOutput s))

theorem gradient_getter_execution
    (oracle : Joint E F → OracleAnswer (Joint E F)) (L rho : ℝ) (x u0 : E) (v : F) (delta : ℝ) :
    execute oracle (gradientGetter L rho x u0 v delta) =
      let run := execute oracle (simulator L x v u0 (min 1 (delta / (1 + 3 * L + 4 * rho))))
      (gradientOutput run.1, run.2) := by
  simp only [gradientGetter, execute_qbind, execute, Nat.add_zero]

theorem simulated_gradient_valid
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (x u0 : E) (v : F) (delta : ℝ) (hdelta : 0 < delta) :
    ‖getterResponse (actualOracle J) (gradientGetter L rho x u0) v delta - gradient (psi J L x) v‖ ≤ delta := by
  have hs := arbitrary_accuracy_simulation J L rho hL hrho hC2 hLip hHess x u0 v delta hdelta
  simpa only [getterResponse, gradient_getter_execution] using hs.2.2.1

def primalAccuracyFloor (L rho deltaFloor : ℝ) : ℝ :=
  min 1 (deltaFloor / (1 + 3 * L + 4 * rho))

def perGradientCost (L rho Du Dv B deltaFloor : ℝ) : ℝ :=
  2 + 18 * Real.log (1 + 9 * (Du + Dv + B) / primalAccuracyFloor L rho deltaFloor)

theorem actual_gradient_getter_cost
    (J : Joint E F → ℝ) (L rho : ℝ) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (x u0 : E) (v0 vstar v : F) (Du Dv B deltaFloor delta : ℝ)
    (hDu : ‖u0 - primal J L x v0‖ ≤ Du) (hDv : ‖v0 - vstar‖ ≤ Dv)
    (hB : 0 ≤ B) (hv : ‖v - vstar‖ ≤ B) (hFloor : 0 < deltaFloor) (hdelta : deltaFloor ≤ delta) :
    0 < primalAccuracyFloor L rho deltaFloor ∧
    0 ≤ perGradientCost L rho Du Dv B deltaFloor ∧
    ((execute (actualOracle J) (gradientGetter L rho x u0 v delta)).2 : ℝ) ≤
      perGradientCost L rho Du Dv B deltaFloor := by
  let c := 1 + 3 * L + 4 * rho
  let e := min 1 (delta / c)
  let emin := primalAccuracyFloor L rho deltaFloor
  let U := Du + Dv + B
  let Dobs := ‖OriginalPrimalElimination.residual J L x (v, u0)‖ / L
  have hc : 0 < c := by dsimp only [c]; positivity
  have hemin : 0 < emin := by unfold emin primalAccuracyFloor; positivity
  have hemin_e : emin ≤ e :=
    min_le_min_left 1 ((div_le_div_iff_of_pos_right hc).mpr hdelta)
  have he : 0 < e := lt_of_lt_of_le hemin hemin_e
  have hDu0 : 0 ≤ Du := le_trans (norm_nonneg _) hDu
  have hDv0 : 0 ≤ Dv := le_trans (norm_nonneg _) hDv
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hprimal := primal_lipschitz J L hL hJ hLip x v0 v
  have hdist := norm_sub_le_norm_sub_add_norm_sub v0 vstar v
  rw [norm_sub_rev vstar v] at hdist
  have hu := norm_sub_le_norm_sub_add_norm_sub u0 (primal J L x v0) (primal J L x v)
  have huU : ‖u0 - primal J L x v‖ ≤ U := by
    dsimp only [U]
    linarith only [hu, hDu, hprimal, hdist, hDv, hv]
  have hres := residual_norm_upper J L hL hC2 hLip x u0 v
  have hDobs : Dobs ≤ 3 * U := by
    apply (div_le_iff₀ hL).mpr
    have hh := mul_le_mul_of_nonneg_left huU (by positivity : 0 ≤ 3 * L)
    nlinarith only [hh, hres]
  have hDobs0 : 0 ≤ Dobs := by dsimp only [Dobs]; positivity
  have hratio : 3 * Dobs / e ≤ 9 * U / emin := by
    calc
      _ ≤ 3 * (3 * U) / e := by gcongr
      _ ≤ 3 * (3 * U) / emin :=
        div_le_div_of_nonneg_left (by positivity) hemin hemin_e
      _ = _ := by ring
  have hlog := Real.log_le_log (by positivity : 0 < 1 + 3 * Dobs / e)
    (add_le_add le_rfl hratio)
  have hlog0 : 0 ≤ Real.log (1 + 9 * U / emin) := Real.log_nonneg (by
    have hh : 0 ≤ 9 * U / emin := by positivity
    linarith only [hh])
  have hs := arbitrary_accuracy_simulation J L rho hL hrho hC2 hLip hHess x u0 v delta
    (lt_of_lt_of_le hFloor hdelta)
  rw [gradient_getter_execution]
  refine ⟨hemin, ?_, ?_⟩
  · change 0 ≤ 2 + 18 * Real.log (1 + 9 * U / emin)
    positivity
  · change _ ≤ 2 + 18 * Real.log (1 + 9 * U / emin)
    have hcost : ((execute (actualOracle J) (simulator L x v u0 e)).2 : ℝ) ≤
        2 + 18 * Real.log (1 + 3 * Dobs / e) := hs.2.2.2.2
    linarith only [hcost, hlog]

def contractionProgram (mu L rho D : ℝ) (x u0 : E) (start : F) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) F :=
  qbind (lower (gradientGetter L rho x u0)
    (CertifiedFirstOrder.contractionProgram mu (2 * L) D
      (CertifiedFirstOrder.iterationCount mu (2 * L)) ⟨0, start, start⟩))
    (fun out => .pure (CertifiedFirstOrder.resultPoint out))

theorem contraction_program_execution (J : Joint E F → ℝ) (mu L rho D : ℝ)
    (x u0 : E) (start : F) :
    let p := CertifiedFirstOrder.contractionProgram mu (2 * L) D
      (CertifiedFirstOrder.iterationCount mu (2 * L)) ⟨0, start, start⟩
    let getter := gradientGetter L rho x u0
    execute (actualOracle J) (contractionProgram mu L rho D x u0 start) =
      (CertifiedFirstOrder.resultPoint (CertifiedFirstOrder.execute
        (getterResponse (actualOracle J) getter) p).1,
       (execute (actualOracle J) (lower getter p)).2) := by
  simp only [contractionProgram, execute_qbind, execute, Nat.add_zero, lower_result]

def contractionCost (mu L rho D Du : ℝ) : ℝ :=
  18 * Real.sqrt (2 * L / mu) *
    perGradientCost L rho Du D (2 * CertifiedFirstOrder.queryRadius mu (2 * L) D)
      (CertifiedFirstOrder.precisionFloor mu (2 * L) D)

theorem actual_first_order_contraction
    (J : Joint E F → ℝ) (mu L rho D Du : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hD : 0 < D)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x u0 : E) (vstar start : F) (hmin : ∀ y : F, psi J L x vstar ≤ psi J L x y)
    (hstart : ‖start - vstar‖ ≤ D) (hDu : ‖u0 - primal J L x start‖ ≤ Du) :
    let run := execute (actualOracle J) (contractionProgram mu L rho D x u0 start)
    ‖run.1 - vstar‖ ≤ D / 2 ∧ (run.2 : ℝ) ≤ contractionCost mu L rho D Du := by
  dsimp only
  let getter : F → ℝ → QueryProgram (Joint E F) (OracleAnswer (Joint E F)) F :=
    gradientGetter L rho x u0
  let oracle := getterResponse (actualOracle J) getter
  let p := CertifiedFirstOrder.contractionProgram mu (2 * L) D
    (CertifiedFirstOrder.iterationCount mu (2 * L)) ⟨0, start, start⟩
  let B := 2 * CertifiedFirstOrder.queryRadius mu (2 * L) D
  let floor := CertifiedFirstOrder.precisionFloor mu (2 * L) D
  let C := perGradientCost L rho Du D B floor
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have htwoL : 0 < 2 * L := by positivity
  have hmutwo : mu ≤ 2 * L := by linarith only [hmu, hLmu]
  have hB : 0 ≤ B := by dsimp only [B, CertifiedFirstOrder.queryRadius]; positivity
  have hfloor : 0 < floor :=
    (CertifiedFirstOrder.precision_floor_bounds mu (2 * L) D hmu htwoL hD).1
  have hvalid : ∀ y delta, 0 < delta → ‖oracle y delta - gradient (psi J L x) y‖ ≤ delta :=
    fun y delta hdelta => simulated_gradient_valid J L rho hL hrho hC2 hLip hHess x u0 y delta hdelta
  have hdiff : Differentiable ℝ (psi J L x) :=
    (psi_contDiff2 J L hL hC2 hLip x).differentiable (by norm_num)
  have hscpsi := psi_strongConvex J L mu hL hC2 hLip hsc x
  have hgrad := psi_gradient_lipschitz J L hL hC2 hLip x
  have hfo := CertifiedFirstOrder.first_order_contraction_program (psi J L x) mu (2 * L) D
    hmu hmutwo hD hdiff hscpsi hgrad oracle hvalid vstar start hmin hstart
  have hqueries := CertifiedFirstOrder.initial_program_queries_bounded (psi J L x) mu (2 * L) D
    hmu hmutwo hD hdiff hscpsi hgrad oracle hvalid vstar start hmin hstart
    (CertifiedFirstOrder.iterationCount mu (2 * L))
  have hC : 0 ≤ C :=
    (actual_gradient_getter_cost J L rho hL hrho hC2 hLip hHess x u0 start vstar vstar
      Du D B floor floor hDu hstart hB (by simpa only [sub_self, norm_zero] using hB)
      hfloor le_rfl).2.1
  have hcost : ∀ y delta, (‖y - vstar‖ ≤ B ∧ floor ≤ delta) →
      ((execute (actualOracle J) (getter y delta)).2 : ℝ) ≤ C := by
    intro y delta hy
    exact (actual_gradient_getter_cost J L rho hL hrho hC2 hLip hHess x u0 start vstar y
      Du D B floor delta hDu hstart hB hy.1 hfloor hy.2).2.2
  have hlower := lower_count (actualOracle J) getter p
    (fun y delta => ‖y - vstar‖ ≤ B ∧ floor ≤ delta) C hcost hqueries
  rw [contraction_program_execution]
  refine ⟨hfo.1, ?_⟩
  change ((execute (actualOracle J) (lower getter p)).2 : ℝ) ≤
    18 * Real.sqrt (2 * L / mu) * C
  have hh := mul_le_mul_of_nonneg_left hfo.2 hC
  nlinarith only [hlower, hh]

end
end OriginalDualFirstOrder


namespace OriginalSaddleFirstOrder
open _root_.OriginalSaddleFirstOrder

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalPrimalElimination OriginalDualCurvature OriginalDualMinimizer
open OriginalDualOracleEstimates OriginalDualOracleProgram CertifiedFirstOrderLowering

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section

def program (mu L rho D : ℝ) (x u0 : E) (v0 : F) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (Joint E F) :=
  qbind (OriginalDualFirstOrder.contractionProgram mu L rho D x u0 v0) (fun v1 =>
    qbind (OriginalDualFirstOrder.contractionProgram mu L rho (D / 2) x u0 v1) (fun v2 =>
      qbind (simulator L x v2 u0 (D / 8)) (fun s =>
        .pure (JointSliceRegularity.point s.u v2))))

def queryCost (mu L rho D : ℝ) : ℝ :=
  OriginalDualFirstOrder.contractionCost mu L rho D (2 * D) +
    OriginalDualFirstOrder.contractionCost mu L rho (D / 2) (2 * D) +
      (2 + 18 * Real.log 145)

theorem actual_saddle_contraction
    (J : Joint E F → ℝ) (mu L rho D : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hD : 0 < D)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x u0 : E) (v0 : F)
    (hstart : ‖JointSliceRegularity.point u0 v0 - zStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (actualOracle J) (program mu L rho D x u0 v0)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ D / 2 ∧
      (run.2 : ℝ) ≤ queryCost mu L rho D := by
  dsimp only
  let f := JointSliceRegularity.curry J
  let us := uStar f L x
  let vs := vStar f L x
  let first := execute (actualOracle J) (OriginalDualFirstOrder.contractionProgram mu L rho D x u0 v0)
  let second := execute (actualOracle J)
    (OriginalDualFirstOrder.contractionProgram mu L rho (D / 2) x u0 first.1)
  let third := execute (actualOracle J) (simulator L x second.1 u0 (D / 8))
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpu := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
  have hstart' : ‖WithLp.toLp 2 (u0, v0) - zStar f L x‖ ≤ D := by
    simpa only [JointSliceRegularity.point_eq_toLp] using hstart
  have hu0 : ‖u0 - us‖ ≤ D := by
    have hh := WithLp.norm_fst_le E (JointSliceRegularity.point u0 v0 - zStar f L x)
    rw [JointSliceRegularity.point_eq_toLp] at hh
    exact hh.trans hstart'
  have hv0 : ‖v0 - vs‖ ≤ D := by
    have hh := WithLp.norm_snd_le E (JointSliceRegularity.point u0 v0 - zStar f L x)
    rw [JointSliceRegularity.point_eq_toLp] at hh
    exact hh.trans hstart'
  have hu_warm : ∀ v : F, ‖u0 - primal J L x v‖ ≤ D + ‖v - vs‖ := by
    intro v
    have hh := primal_lipschitz J L hL hJ hLip x vs v
    rw [hpu, norm_sub_rev vs v] at hh
    have ht := norm_sub_le_norm_sub_add_norm_sub u0 us (primal J L x v)
    linarith only [ht, hu0, hh]
  have hfirst := OriginalDualFirstOrder.actual_first_order_contraction J mu L rho D (2 * D)
    hmu hLmu hrho hD hC2 hLip hHess hsc x u0 vs v0 hmin hv0
    (by have hh := hu_warm v0; linarith only [hh, hv0])
  change ‖first.1 - vs‖ ≤ D / 2 ∧ (first.2 : ℝ) ≤ _ at hfirst
  have hsecond := OriginalDualFirstOrder.actual_first_order_contraction J mu L rho (D / 2) (2 * D)
    hmu hLmu hrho (by positivity) hC2 hLip hHess hsc x u0 vs first.1 hmin hfirst.1
    (by have hh := hu_warm first.1; linarith only [hh, hfirst.1, hD])
  change ‖second.1 - vs‖ ≤ (D / 2) / 2 ∧ (second.2 : ℝ) ≤ _ at hsecond
  have hthird := reduced_dual_oracle_simulation J L rho hL hrho hC2 hLip hHess x u0 second.1
    (D / 8) (by positivity)
  have hdist : ‖third.1.u - primal J L x second.1‖ ≤ D / 8 := hthird.2.1
  have hprimal := primal_lipschitz J L hL hJ hLip x second.1 vs
  rw [hpu] at hprimal
  have htri := norm_sub_le_norm_sub_add_norm_sub third.1.u (primal J L x second.1) us
  have hu : ‖third.1.u - us‖ ≤ 3 * D / 8 := by
    linarith only [htri, hdist, hprimal, hsecond.1]
  have hv : ‖second.1 - vs‖ ≤ D / 4 := by linarith only [hsecond.1]
  have hdu2 : ‖u0 - primal J L x second.1‖ ≤ 2 * D := by
    have hh := hu_warm second.1
    linarith only [hh, hv, hD]
  have hres := residual_norm_upper J L hL hC2 hLip x u0 second.1
  have hDobs : ‖OriginalPrimalElimination.residual J L x (second.1, u0)‖ / L ≤ 6 * D := by
    apply (div_le_iff₀ hL).mpr
    have hh := mul_le_mul_of_nonneg_left hdu2 (by positivity : 0 ≤ 3 * L)
    nlinarith only [hh, hres]
  have hlog : Real.log (1 + 3 * (‖OriginalPrimalElimination.residual J L x (second.1, u0)‖ / L) / (D / 8)) ≤
      Real.log 145 := by
    apply Real.log_le_log (by positivity)
    calc
      _ ≤ 1 + 3 * (6 * D) / (D / 8) := by gcongr
      _ = 145 := by field_simp <;> ring
  have hthirdcost : (third.2 : ℝ) ≤ 2 + 18 * Real.log 145 := by
    have hh := hthird.2.2.2.2.2
    linarith only [hh, hlog]
  simp only [program, execute_qbind, execute, Nat.add_zero]
  change ‖JointSliceRegularity.point third.1.u second.1 - zStar f L x‖ ≤ D / 2 ∧
    ((first.2 + (second.2 + third.2) : ℕ) : ℝ) ≤ _
  constructor
  · have hn := WithLp.prod_norm_sq_eq_of_L2 (JointSliceRegularity.point third.1.u second.1 - zStar f L x)
    rw [JointSliceRegularity.point_eq_toLp] at hn
    have hn' : ‖JointSliceRegularity.point third.1.u second.1 - zStar f L x‖ ^ 2 =
        ‖third.1.u - us‖ ^ 2 + ‖second.1 - vs‖ ^ 2 := by
      rw [JointSliceRegularity.point_eq_toLp]
      exact hn
    have husq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 3 * D / 8)).mpr hu
    have hvsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ D / 4)).mpr hv
    nlinarith only [hn', husq, hvsq, hD,
      norm_nonneg (JointSliceRegularity.point third.1.u second.1 - zStar f L x)]
  · push_cast
    dsimp only [queryCost]
    linarith only [hfirst.2, hsecond.2, hthirdcost]

end
end OriginalSaddleFirstOrder


namespace OriginalSaddleFirstOrder
open _root_.OriginalSaddleFirstOrder

noncomputable section

def primitiveUniformCost (mu L rho Dmax dmin : ℝ) : ℝ :=
  OriginalDualFirstOrder.perGradientCost L rho (2 * Dmax) Dmax
    (2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax)
    (CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2))

def uniformCost (mu L rho Dmax dmin : ℝ) : ℝ :=
  36 * Real.sqrt (2 * L / mu) * primitiveUniformCost mu L rho Dmax dmin +
    (2 + 18 * Real.log 145)

theorem precision_floor_mono (mu L : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (a b : ℝ) (hab : a ≤ b) :
    CertifiedFirstOrder.precisionFloor mu L a ≤ CertifiedFirstOrder.precisionFloor mu L b := by
  unfold CertifiedFirstOrder.precisionFloor CertifiedFirstOrder.centerTolerance
  have hc : 0 ≤ (3 / 64 : ℝ) * (2 * L)⁻¹ * (mu / 64) *
      min ((2 * L)⁻¹)⁻¹ (min 1 (mu / ((2 * L)⁻¹))) := by positivity
  convert! mul_le_mul_of_nonneg_left hab hc using 1 <;> ring

theorem per_gradient_cost_mono (L rho Du Dv B delta Du' Dv' B' delta' : ℝ)
    (hL : 0 < L) (hrho : 0 ≤ rho) (hdelta' : 0 < delta')
    (hdelta : delta' ≤ delta)
    (hU : 0 ≤ Du + Dv + B) (hU' : Du + Dv + B ≤ Du' + Dv' + B') :
    OriginalDualFirstOrder.perGradientCost L rho Du Dv B delta ≤
      OriginalDualFirstOrder.perGradientCost L rho Du' Dv' B' delta' := by
  let c := 1 + 3 * L + 4 * rho
  let e := OriginalDualFirstOrder.primalAccuracyFloor L rho delta
  let e' := OriginalDualFirstOrder.primalAccuracyFloor L rho delta'
  have hc : 0 < c := by dsimp only [c]; positivity
  have he' : 0 < e' := by dsimp only [e', OriginalDualFirstOrder.primalAccuracyFloor]; positivity
  have he'e : e' ≤ e := min_le_min_left 1 ((div_le_div_iff_of_pos_right hc).mpr hdelta)
  have he : 0 < e := lt_of_lt_of_le he' he'e
  have hU'0 : 0 ≤ Du' + Dv' + B' := hU.trans hU'
  have hratio : 9 * (Du + Dv + B) / e ≤ 9 * (Du' + Dv' + B') / e' := by
    calc
      _ ≤ 9 * (Du' + Dv' + B') / e := by gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) he' he'e
  have hlog := Real.log_le_log (by positivity : 0 < 1 + 9 * (Du + Dv + B) / e)
    (add_le_add le_rfl hratio)
  unfold OriginalDualFirstOrder.perGradientCost
  change 2 + 18 * Real.log (1 + 9 * (Du + Dv + B) / e) ≤
    2 + 18 * Real.log (1 + 9 * (Du' + Dv' + B') / e')
  linarith only [hlog]

theorem query_cost_uniform_bound (mu L rho Dmax dmin d : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho)
    (hdmin : 0 < dmin) (hlo : dmin ≤ d) (hhi : d ≤ Dmax) :
    0 ≤ uniformCost mu L rho Dmax dmin ∧
      queryCost mu L rho d ≤ uniformCost mu L rho Dmax dmin := by
  have hd : 0 < d := lt_of_lt_of_le hdmin hlo
  have hmax : 0 < Dmax := lt_of_lt_of_le hd hhi
  have hsqrt : 0 ≤ Real.sqrt (2 * L / mu) := Real.sqrt_nonneg _
  have hrad : CertifiedFirstOrder.queryRadius mu (2 * L) d ≤
      CertifiedFirstOrder.queryRadius mu (2 * L) Dmax := by
    unfold CertifiedFirstOrder.queryRadius
    gcongr
  have hradhalf : CertifiedFirstOrder.queryRadius mu (2 * L) (d / 2) ≤
      CertifiedFirstOrder.queryRadius mu (2 * L) Dmax := by
    unfold CertifiedFirstOrder.queryRadius
    gcongr
    linarith only [hhi, hd]
  have hfloor : 0 < CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2) :=
    (CertifiedFirstOrder.precision_floor_bounds mu (2 * L) (dmin / 2) hmu (by positivity) (by positivity)).1
  have hfloor1 := precision_floor_mono mu (2 * L) hmu (by positivity) (dmin / 2) d
    (by linarith only [hlo, hdmin])
  have hfloor2 := precision_floor_mono mu (2 * L) hmu (by positivity) (dmin / 2) (d / 2)
    (by linarith only [hlo])
  have hU1 : 2 * d + d + 2 * CertifiedFirstOrder.queryRadius mu (2 * L) d ≤
      2 * Dmax + Dmax + 2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax := by
    linarith only [hhi, hrad]
  have hU2 : 2 * d + d / 2 + 2 * CertifiedFirstOrder.queryRadius mu (2 * L) (d / 2) ≤
      2 * Dmax + Dmax + 2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax := by
    linarith only [hhi, hradhalf, hd]
  have hcost1 := per_gradient_cost_mono L rho (2 * d) d
    (2 * CertifiedFirstOrder.queryRadius mu (2 * L) d) (CertifiedFirstOrder.precisionFloor mu (2 * L) d)
    (2 * Dmax) Dmax (2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax)
    (CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2)) hL hrho hfloor hfloor1
    (by unfold CertifiedFirstOrder.queryRadius; positivity) hU1
  have hcost2 := per_gradient_cost_mono L rho (2 * d) (d / 2)
    (2 * CertifiedFirstOrder.queryRadius mu (2 * L) (d / 2))
    (CertifiedFirstOrder.precisionFloor mu (2 * L) (d / 2))
    (2 * Dmax) Dmax (2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax)
    (CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2)) hL hrho hfloor hfloor2
    (by unfold CertifiedFirstOrder.queryRadius; positivity) hU2
  have hprimitive : 0 ≤ primitiveUniformCost mu L rho Dmax dmin := by
    unfold primitiveUniformCost OriginalDualFirstOrder.perGradientCost
    have he : 0 < OriginalDualFirstOrder.primalAccuracyFloor L rho
        (CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2)) := by
      unfold OriginalDualFirstOrder.primalAccuracyFloor
      positivity
    have hlog : 0 ≤ Real.log (1 + 9 * (2 * Dmax + Dmax +
        2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax) /
        OriginalDualFirstOrder.primalAccuracyFloor L rho
          (CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2))) := by
      apply Real.log_nonneg
      have hh : 0 ≤ 9 * (2 * Dmax + Dmax +
          2 * CertifiedFirstOrder.queryRadius mu (2 * L) Dmax) /
          OriginalDualFirstOrder.primalAccuracyFloor L rho
            (CertifiedFirstOrder.precisionFloor mu (2 * L) (dmin / 2)) := by
        unfold CertifiedFirstOrder.queryRadius
        positivity
      linarith only [hh]
    positivity
  have hlog145 : 0 ≤ Real.log (145 : ℝ) := Real.log_nonneg (by norm_num)
  refine ⟨by unfold uniformCost; positivity, ?_⟩
  have hm1 := mul_le_mul_of_nonneg_left hcost1 (by positivity : 0 ≤ 18 * Real.sqrt (2 * L / mu))
  have hm2 := mul_le_mul_of_nonneg_left hcost2 (by positivity : 0 ≤ 18 * Real.sqrt (2 * L / mu))
  unfold queryCost OriginalDualFirstOrder.contractionCost uniformCost primitiveUniformCost
  nlinarith only [hm1, hm2]

theorem halving_remaining_lower_bound (D tau : ℝ) (hD : 0 < D) (htau : 0 < tau) :
    min D tau / 2 ≤ D / (2 : ℝ) ^ FangqingHysteresis.halvingCount D tau := by
  let m := max 1 (D / tau)
  have hm : 0 < m := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog0 : 0 ≤ Real.logb 2 m := Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hn := (Nat.ceil_lt_add_one hlog0).le
  have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hn
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hm] at hpow
  have hnpos : 0 < (2 : ℝ) ^ FangqingHysteresis.halvingCount D tau := by positivity
  have heq : min D tau / 2 = D / (m * 2) := by
    by_cases hDt : D ≤ tau
    · have hr : D / tau ≤ 1 := (div_le_one₀ htau).mpr hDt
      simp only [m, max_eq_left hr, min_eq_left hDt]
      ring
    · have htD : tau ≤ D := le_of_not_ge hDt
      have hr : 1 ≤ D / tau := (one_le_div₀ htau).mpr htD
      simp only [m, max_eq_right hr, min_eq_right htD]
      field_simp
      <;> ring
  rw [heq]
  apply div_le_div_of_nonneg_left hD.le hnpos
  exact hpow

end
end OriginalSaddleFirstOrder


namespace OriginalSaddleFirstOrder
open _root_.OriginalSaddleFirstOrder

open OriginalSaddleImplicit OriginalSaddleStability OriginalDualOracleProgram CertifiedFirstOrderLowering

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section

def restartProgram (mu L rho : ℝ) (x : E) : ℕ → ℝ → Joint E F →
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (Joint E F)
  | 0, _, w => .pure w
  | n + 1, D, w => qbind (program mu L rho D x w.fst w.snd)
      (fun next => restartProgram mu L rho x n (D / 2) next)

theorem point_eta (w : Joint E F) : JointSliceRegularity.point w.fst w.snd = w := by
  rw [JointSliceRegularity.point_eq_toLp]
  rfl

theorem restart_uniform_spec
    (J : Joint E F → ℝ) (mu L rho Dmax dmin : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hdmin : 0 < dmin)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (n : ℕ) (D : ℝ) (hD : 0 < D) (hhi : D ≤ Dmax)
    (hlo : dmin ≤ D / (2 : ℝ) ^ n) (start : Joint E F)
    (hstart : ‖start - zStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (actualOracle J) (restartProgram mu L rho x n D start)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ D / (2 : ℝ) ^ n ∧
      (run.2 : ℝ) ≤ uniformCost mu L rho Dmax dmin * n := by
  dsimp only
  induction n generalizing D start with
  | zero =>
      simp only [restartProgram, execute, pow_zero, div_one, Nat.cast_zero, mul_zero, le_refl, and_true]
      exact hstart
  | succ n ih =>
      have hL : 0 < L := lt_of_lt_of_le hmu hLmu
      have hpow : (1 : ℝ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      have hDpow : D / (2 : ℝ) ^ (n + 1) ≤ D := by
        apply (div_le_iff₀ (by positivity)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hpow hD.le]
      have hcost := query_cost_uniform_bound mu L rho Dmax dmin D hmu hL hrho hdmin
        (le_trans hlo hDpow) hhi
      have hone := actual_saddle_contraction J mu L rho D hmu hLmu hrho hD hC2 hLip hHess hsc
        x start.fst start.snd (by simpa only [point_eta] using hstart)
      let first := execute (actualOracle J) (program mu L rho D x start.fst start.snd)
      change ‖first.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ D / 2 ∧
        (first.2 : ℝ) ≤ queryCost mu L rho D at hone
      have hnextlo : dmin ≤ (D / 2) / (2 : ℝ) ^ n := by
        convert! hlo using 1
        rw [pow_succ]
        ring
      have hnext := ih (D / 2) (by positivity) (by linarith only [hhi, hD]) hnextlo first.1 hone.1
      simp only [restartProgram, execute_qbind]
      change ‖(execute (actualOracle J) (restartProgram mu L rho x n (D / 2) first.1)).1 -
          zStar (JointSliceRegularity.curry J) L x‖ ≤ _ ∧
        ((first.2 + (execute (actualOracle J) (restartProgram mu L rho x n (D / 2) first.1)).2 : ℕ) : ℝ) ≤ _
      constructor
      · convert! hnext.1 using 1
        rw [pow_succ]
        ring
      · push_cast
        nlinarith only [hone.2, hnext.2, hcost.2]

def solveProgram (mu L rho D tau : ℝ) (x : E) (start : Joint E F) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (Joint E F) :=
  restartProgram mu L rho x (FangqingHysteresis.halvingCount D tau) D start

theorem actual_first_order_saddle_solver
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hD : 0 < D) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (start : Joint E F)
    (hstart : ‖start - zStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (actualOracle J) (solveProgram mu L rho D tau x start)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ uniformCost mu L rho D (min D tau / 2) *
        (1 + Real.logb 2 (max 1 (D / tau))) := by
  dsimp only
  have hminrad : 0 < min D tau / 2 := by positivity
  have hs := restart_uniform_spec J mu L rho D (min D tau / 2) hmu hLmu hrho hminrad
    hC2 hLip hHess hsc x (FangqingHysteresis.halvingCount D tau) D hD le_rfl
    (halving_remaining_lower_bound D tau hD htau) start hstart
  refine ⟨le_trans hs.1 (FangqingHysteresis.halving_precision D tau htau), ?_⟩
  have hC := (query_cost_uniform_bound mu L rho D (min D tau / 2) D hmu
    (lt_of_lt_of_le hmu hLmu) hrho hminrad (by
      have hh := min_le_left D tau
      linarith only [hh, hD]) le_rfl).1
  have hlog0 : 0 ≤ Real.logb 2 (max 1 (D / tau)) :=
    Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have hn := (Nat.ceil_lt_add_one hlog0).le
  change (FangqingHysteresis.halvingCount D tau : ℝ) ≤ _ at hn
  exact le_trans hs.2 (mul_le_mul_of_nonneg_left (by linarith only [hn]) hC)

end
end OriginalSaddleFirstOrder


namespace OriginalDualWarmFirstOrder
open _root_.OriginalDualWarmFirstOrder

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalPrimalElimination OriginalDualMinimizer
open OriginalDualOracleProgram CertifiedFirstOrderLowering

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section

def workingRadius (D tau : ℝ) : ℝ := max D (tau / 2)

def program (mu L rho D tau : ℝ) (x uinit : E) (yin : F) :
    QueryProgram (Joint E F) (OracleAnswer (Joint E F)) (Joint E F) :=
  let R := workingRadius D tau
  qbind (simulator L x yin uinit (R / 4)) (fun s =>
    OriginalSaddleFirstOrder.solveProgram mu L rho (2 * R) tau x
      (JointSliceRegularity.point s.u yin))

def queryBound (mu L rho D tau Dobs : ℝ) : ℝ :=
  let R := workingRadius D tau
  (2 + 18 * Real.log (1 + 12 * Dobs / R)) +
    OriginalSaddleFirstOrder.uniformCost mu L rho (2 * R) (min (2 * R) tau / 2) *
      (1 + Real.logb 2 (max 1 ((2 * R) / tau)))

theorem solve_from_dual_warm_start
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x uinit : E) (yin : F)
    (hin : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (actualOracle J) (program mu L rho D tau x uinit yin)
    let Dobs := ‖OriginalPrimalElimination.residual J L x (yin, uinit)‖ / L
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ queryBound mu L rho D tau Dobs := by
  dsimp only
  let f := JointSliceRegularity.curry J
  let us := uStar f L x
  let vs := vStar f L x
  let R := workingRadius D tau
  let prep := execute (actualOracle J) (simulator L x yin uinit (R / 4))
  have hL : 0 < L := lt_of_lt_of_le hmu hLmu
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < tau / 2) (le_max_right _ _)
  have hinR : ‖yin - vs‖ ≤ R := le_trans hin (le_max_left _ _)
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hpu := primal_at_actual_dual_saddle J L mu hL hmu hJ hLip hsc x
  have hprep := reduced_dual_oracle_simulation J L rho hL hrho hC2 hLip hHess x uinit yin
    (R / 4) (by positivity)
  have huprep : ‖prep.1.u - primal J L x yin‖ ≤ R / 4 := hprep.2.1
  have hprimal := primal_lipschitz J L hL hJ hLip x yin vs
  rw [hpu] at hprimal
  have htri := norm_sub_le_norm_sub_add_norm_sub prep.1.u (primal J L x yin) us
  have hu : ‖prep.1.u - us‖ ≤ 5 * R / 4 := by
    linarith only [huprep, hprimal, hinR, htri]
  have hjoint : ‖JointSliceRegularity.point prep.1.u yin - zStar f L x‖ ≤ 2 * R := by
    have hn := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (prep.1.u, yin) - zStar f L x)
    have hn' : ‖JointSliceRegularity.point prep.1.u yin - zStar f L x‖ ^ 2 =
        ‖prep.1.u - us‖ ^ 2 + ‖yin - vs‖ ^ 2 := by
      rw [JointSliceRegularity.point_eq_toLp]
      exact hn
    have husq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 5 * R / 4)).mpr hu
    have hvsq := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hinR
    nlinarith only [hn', husq, hvsq, hR,
      norm_nonneg (JointSliceRegularity.point prep.1.u yin - zStar f L x)]
  have hs := OriginalSaddleFirstOrder.actual_first_order_saddle_solver J mu L rho (2 * R) tau
    hmu hLmu hrho (by positivity) htau hC2 hLip hHess hsc x
    (JointSliceRegularity.point prep.1.u yin) hjoint
  have hcost := hprep.2.2.2.2.2
  have hratio : 3 * (‖OriginalPrimalElimination.residual J L x (yin, uinit)‖ / L) / (R / 4) =
      12 * (‖OriginalPrimalElimination.residual J L x (yin, uinit)‖ / L) / R := by ring
  rw [hratio] at hcost
  simp only [program, execute_qbind]
  change ‖(execute (actualOracle J)
    (OriginalSaddleFirstOrder.solveProgram mu L rho (2 * R) tau x
      (JointSliceRegularity.point prep.1.u yin))).1 - zStar f L x‖ ≤ tau ∧ _
  refine ⟨hs.1, ?_⟩
  change ((prep.2 + (execute (actualOracle J)
    (OriginalSaddleFirstOrder.solveProgram mu L rho (2 * R) tau x
      (JointSliceRegularity.point prep.1.u yin))).2 : ℕ) : ℝ) ≤ _
  push_cast
  dsimp only [queryBound]
  linarith only [hcost, hs.2]

theorem first_order_branch_from_standing_joint
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F,
      ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u, y))))
    (x uinit : E) (yin : F)
    (hin : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (actualOracle J) (program mu L rho D tau x uinit yin)
    let Dobs := ‖OriginalPrimalElimination.residual J L x (yin, uinit)‖ / L
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ queryBound mu L rho D tau Dobs := by
  have hconcave' : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu (JointSliceRegularity.curry J u) := by
    intro u
    have heq : JointSliceRegularity.curry J u = (fun y : F => J (WithLp.toLp 2 (u, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp u y)
    rw [heq]
    exact hconcave u
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J mu hconcave'
  exact solve_from_dual_warm_start J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess hsc x uinit yin hin

end
end OriginalDualWarmFirstOrder


namespace OriginalMinimumWarmSolver
open _root_.OriginalMinimumWarmSolver

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section

def firstScale (mu L : ℝ) : ℝ := Real.sqrt (L / mu)
def secondScale (mu rho D : ℝ) : ℝ := (rho * D / mu) ^ (2 / 7 : ℝ)

def secondConstant : ℝ := 1 +
  (8 * LargeStepAHPE.rateConstant (1 / 2) (1 / 8)) ^ (2 / 7 : ℝ) *
    (4 * Real.sqrt 2) ^ (2 / 7 : ℝ)

def program (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Joint E F) :=
  if firstScale mu L ≤ secondScale mu rho D then
    OriginalDualGetterImplementation.liftQuery (OriginalDualWarmFirstOrder.program mu L rho D tau x uInit yin)
  else OriginalSecondOrderWarmAll.program mu L rho D tau x uInit yin

def firstLogFactor (mu L rho D tau Dobs : ℝ) : ℝ :=
  let R := OriginalDualWarmFirstOrder.workingRadius D tau
  let C := OriginalSaddleFirstOrder.primitiveUniformCost mu L rho (2 * R) (min (2 * R) tau / 2)
  (2 + 18 * Real.log (1 + 12 * Dobs / R)) +
    (36 * Real.sqrt 2 * C + (2 + 18 * Real.log 145)) *
      (1 + Real.logb 2 (max 1 ((2 * R) / tau)))

theorem first_order_factorization (mu L rho D tau Dobs : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (hobs : 0 ≤ Dobs) :
    0 ≤ firstLogFactor mu L rho D tau Dobs ∧
      OriginalDualWarmFirstOrder.queryBound mu L rho D tau Dobs ≤
        (1 + firstScale mu L) * firstLogFactor mu L rho D tau Dobs := by
  let R := OriginalDualWarmFirstOrder.workingRadius D tau
  let C := OriginalSaddleFirstOrder.primitiveUniformCost mu L rho (2 * R) (min (2 * R) tau / 2)
  let A := 2 + 18 * Real.log (1 + 12 * Dobs / R)
  let T := 1 + Real.logb 2 (max 1 ((2 * R) / tau))
  let B := 2 + 18 * Real.log (145 : ℝ)
  let p := Real.sqrt (L / mu)
  have hL : 0 < L := hmu.trans_le hLmu
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < tau / 2) (le_max_right _ _)
  have hfloor : 0 < CertifiedFirstOrder.precisionFloor mu (2 * L) ((min (2 * R) tau / 2) / 2) :=
    (CertifiedFirstOrder.precision_floor_bounds mu (2 * L) _ hmu (by positivity) (by positivity)).1
  have haccuracy : 0 < OriginalDualFirstOrder.primalAccuracyFloor L rho
      (CertifiedFirstOrder.precisionFloor mu (2 * L) ((min (2 * R) tau / 2) / 2)) := by
    unfold OriginalDualFirstOrder.primalAccuracyFloor
    positivity
  have hC : 0 ≤ C := by
    unfold C OriginalSaddleFirstOrder.primitiveUniformCost OriginalDualFirstOrder.perGradientCost
    have hquot : 0 ≤ 9 * (2 * (2 * R) + (2 * R) +
        2 * CertifiedFirstOrder.queryRadius mu (2 * L) (2 * R)) /
        OriginalDualFirstOrder.primalAccuracyFloor L rho
          (CertifiedFirstOrder.precisionFloor mu (2 * L) ((min (2 * R) tau / 2) / 2)) := by
      unfold CertifiedFirstOrder.queryRadius
      positivity
    have hlog := Real.log_nonneg (show 1 ≤ 1 + 9 * (2 * (2 * R) + (2 * R) +
        2 * CertifiedFirstOrder.queryRadius mu (2 * L) (2 * R)) /
        OriginalDualFirstOrder.primalAccuracyFloor L rho
          (CertifiedFirstOrder.precisionFloor mu (2 * L) ((min (2 * R) tau / 2) / 2)) by linarith only [hquot])
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hlog := Real.log_nonneg (show 1 ≤ 1 + 12 * Dobs / R by
      have hh : 0 ≤ 12 * Dobs / R := by positivity
      linarith only [hh])
    positivity
  have hB : 0 ≤ B := by
    dsimp only [B]
    have hh : 0 ≤ Real.log (145 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  have hT : 0 ≤ T := by
    dsimp only [T]
    have hh : 0 ≤ Real.logb 2 (max 1 ((2 * R) / tau)) :=
      Real.logb_nonneg (by norm_num) (le_max_left _ _)
    positivity
  have hratio : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa only [one_mul] using hLmu)
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hpsq := Real.sq_sqrt (show 0 ≤ L / mu by positivity)
  have hp : 1 ≤ p := by dsimp only [p]; nlinarith only [hpsq, hratio, Real.sqrt_nonneg (L / mu)]
  have hscale : Real.sqrt (2 * L / mu) = Real.sqrt 2 * p := by
    rw [show 2 * L / mu = 2 * (L / mu) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hLF : 0 ≤ A + (36 * Real.sqrt 2 * C + B) * T := by positivity
  have hAineq := mul_nonneg (sub_nonneg.mpr hp) hA
  have hBineq := mul_nonneg (sub_nonneg.mpr hp) (mul_nonneg hB hT)
  change 0 ≤ A + (36 * Real.sqrt 2 * C + B) * T ∧
    A + (36 * Real.sqrt (2 * L / mu) * C + B) * T ≤
      (1 + p) * (A + (36 * Real.sqrt 2 * C + B) * T)
  rw [hscale]
  exact ⟨hLF, by nlinarith only [hAineq, hBineq, hLF]⟩

theorem second_constant_positive : 0 < secondConstant := by
  have hC := LargeStepAHPE.rateConstant_positive (1 / 2) (1 / 8) (by norm_num) (by norm_num) (by norm_num)
  unfold secondConstant
  positivity

theorem second_order_iteration_factor (mu L rho D : ℝ) (hmu : 0 < mu) (hrho : 0 ≤ rho) (hD : 0 ≤ D) :
    (OriginalRobustTrajectory.contractionIterations
      (OriginalActualDualPositiveContraction.parameters mu L rho D) (1 / 2) D : ℝ) ≤
      secondConstant * (1 + secondScale mu rho D) := by
  let C := LargeStepAHPE.rateConstant (1 / 2) (1 / 8)
  have hC : 0 < C := LargeStepAHPE.rateConstant_positive _ _ (by norm_num) (by norm_num) (by norm_num)
  have hn := OriginalSecondOrderCount.rounded_iteration_properties C ((4 * Real.sqrt 2) * rho) D mu
    hC.le (by positivity) hD hmu
  have hfactor : (((4 * Real.sqrt 2) * rho) * D / mu) ^ (2 / 7 : ℝ) =
      (4 * Real.sqrt 2) ^ (2 / 7 : ℝ) * secondScale mu rho D := by
    rw [show ((4 * Real.sqrt 2) * rho) * D / mu = (4 * Real.sqrt 2) * (rho * D / mu) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
    rfl
  rw [hfactor] at hn
  change (OriginalSecondOrderCount.iterations C ((4 * Real.sqrt 2) * rho) D mu : ℝ) ≤ _
  have hX : 0 ≤ secondScale mu rho D := by unfold secondScale; positivity
  have hCpow : 0 ≤ (8 * C) ^ (2 / 7 : ℝ) * (4 * Real.sqrt 2) ^ (2 / 7 : ℝ) := by positivity
  change _ ≤ (1 + (8 * C) ^ (2 / 7 : ℝ) * (4 * Real.sqrt 2) ^ (2 / 7 : ℝ)) * (1 + secondScale mu rho D)
  nlinarith only [hn.2.1, hX, hCpow]

def positiveLogFactor (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℝ :=
  if 0 < D then
    let c := OriginalActualDualPositiveContraction.parameters mu L rho D
    let r := FangqingHysteresis.halvingCount D (tau / 4)
    let K := OriginalDualGetterImplementation.queryBallBudget J L rho x uInit yin
      (OriginalRobustTrajectory.uniformQueryRadius c D + D)
      (OriginalRobustTrajectory.precisionMinimum c (1 / 2) r D)
    let G := OriginalRobustTrajectory.coefficientMaximum (OriginalRobustTrajectory.radiusGetterFactor c (1 / 2)) r D
    secondConstant * (K * r * G : ℕ) + (OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin : ℕ)
  else (OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin : ℕ)

def secondLogFactor (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℝ :=
  if 0 < rho then positiveLogFactor J mu L rho D tau x uInit yin
  else (OriginalZeroCurvatureDualWarm.warmQueryBudget J mu L D tau x uInit yin : ℕ)

theorem second_order_factorization
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (hmu : 0 < mu) (hrho : 0 ≤ rho) (hD : 0 ≤ D)
    (x uInit : E) (yin : F) :
    0 ≤ secondLogFactor J mu L rho D tau x uInit yin ∧
      (OriginalSecondOrderWarmAll.queryBudget J mu L rho D tau x uInit yin : ℝ) ≤
        (1 + secondScale mu rho D) * secondLogFactor J mu L rho D tau x uInit yin := by
  have hq : 0 ≤ secondScale mu rho D := by unfold secondScale; positivity
  have hconst := second_constant_positive.le
  by_cases hr : 0 < rho
  · by_cases hd : 0 < D
    · let c := OriginalActualDualPositiveContraction.parameters mu L rho D
      let r := FangqingHysteresis.halvingCount D (tau / 4)
      let K := OriginalDualGetterImplementation.queryBallBudget J L rho x uInit yin
        (OriginalRobustTrajectory.uniformQueryRadius c D + D)
        (OriginalRobustTrajectory.precisionMinimum c (1 / 2) r D)
      let G := OriginalRobustTrajectory.coefficientMaximum (OriginalRobustTrajectory.radiusGetterFactor c (1 / 2)) r D
      let N := OriginalRobustTrajectory.contractionIterations c (1 / 2) D
      let P := OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin
      have hN := second_order_iteration_factor mu L rho D hmu hrho hD
      change (N : ℝ) ≤ secondConstant * (1 + secondScale mu rho D) at hN
      have hmul := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ (K : ℝ) * (r : ℝ) * (G : ℝ))
      have hPextra := mul_nonneg (show 0 ≤ (P : ℝ) by positivity) hq
      simp only [secondLogFactor, OriginalSecondOrderWarmAll.queryBudget, if_pos hr,
        positiveLogFactor, OriginalActualDualSecondOrderWarm.warmQueryBudget,
        OriginalActualDualSecondOrderWarm.dualQueryBudget, if_pos hd]
      change 0 ≤ secondConstant * (K * r * G : ℕ) + (P : ℕ) ∧
        ((K * (N * r * G) + P : ℕ) : ℝ) ≤ (1 + secondScale mu rho D) *
          (secondConstant * (K * r * G : ℕ) + (P : ℕ))
      push_cast
      exact ⟨by positivity, by nlinarith only [hmul, hPextra]⟩
    · let P := OriginalDualPrimalRecovery.queryBudget J L D tau x uInit yin
      simp only [secondLogFactor, OriginalSecondOrderWarmAll.queryBudget, if_pos hr,
        positiveLogFactor, OriginalActualDualSecondOrderWarm.warmQueryBudget,
        OriginalActualDualSecondOrderWarm.dualQueryBudget, if_neg hd, zero_add]
      change 0 ≤ (P : ℝ) ∧ (P : ℝ) ≤ (1 + secondScale mu rho D) * (P : ℝ)
      exact ⟨by positivity, by nlinarith only [mul_nonneg hq (show 0 ≤ (P : ℝ) by positivity)]⟩
  · let P := OriginalZeroCurvatureDualWarm.warmQueryBudget J mu L D tau x uInit yin
    simp only [secondLogFactor, OriginalSecondOrderWarmAll.queryBudget, if_neg hr]
    change 0 ≤ (P : ℝ) ∧ (P : ℝ) ≤ (1 + secondScale mu rho D) * (P : ℝ)
    exact ⟨by positivity, by nlinarith only [mul_nonneg hq (show 0 ≤ (P : ℝ) by positivity)]⟩

def logFactor (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) : ℝ :=
  max (firstLogFactor mu L rho D tau (‖OriginalPrimalElimination.residual J L x (yin, uInit)‖ / L))
    (secondLogFactor J mu L rho D tau x uInit yin)

theorem actual_minimum_warm_solver
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ (1 + min (firstScale mu L) (secondScale mu rho D)) * logFactor J mu L rho D tau x uInit yin := by
  dsimp only
  have hL := hmu.trans_le hLmu
  have hD : 0 ≤ D := (norm_nonneg _).trans hwarm
  have hfo := OriginalDualWarmFirstOrder.solve_from_dual_warm_start J mu L rho D tau hmu hLmu hrho htau
    hC2 hLip hHess hsc x uInit yin hwarm
  have hso := OriginalSecondOrderWarmAll.actual_second_order_joint_warm_solve J mu L rho D tau hmu hL hrho htau
    hC2 hLip hHess hsc x uInit yin hwarm
  have hf := first_order_factorization mu L rho D tau
    (‖OriginalPrimalElimination.residual J L x (yin, uInit)‖ / L) hmu hLmu hrho htau (by positivity)
  have hs := second_order_factorization J mu L rho D tau hmu hrho hD x uInit yin
  by_cases hchoose : firstScale mu L ≤ secondScale mu rho D
  · simp only [program, if_pos hchoose, OriginalDualGetterImplementation.execute_liftQuery, min_eq_left hchoose]
    refine ⟨hfo.1, ?_⟩
    have hm := mul_le_mul_of_nonneg_left
      (le_max_left (firstLogFactor mu L rho D tau (‖OriginalPrimalElimination.residual J L x (yin, uInit)‖ / L))
        (secondLogFactor J mu L rho D tau x uInit yin))
      (show 0 ≤ 1 + firstScale mu L by unfold firstScale; positivity)
    exact hfo.2.trans (hf.2.trans hm)
  · have hmin : secondScale mu rho D ≤ firstScale mu L := le_of_not_ge hchoose
    simp only [program, if_neg hchoose, min_eq_right hmin]
    refine ⟨hso.1, ?_⟩
    have hm := mul_le_mul_of_nonneg_left
      (le_max_right (firstLogFactor mu L rho D tau (‖OriginalPrimalElimination.residual J L x (yin, uInit)‖ / L))
        (secondLogFactor J mu L rho D tau x uInit yin))
      (show 0 ≤ 1 + secondScale mu rho D by unfold secondScale; positivity)
    exact (show ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalSecondOrderWarmAll.program mu L rho D tau x uInit yin)).2 : ℝ) ≤
      (OriginalSecondOrderWarmAll.queryBudget J mu L rho D tau x uInit yin : ℝ) by exact_mod_cast hso.2).trans
      (hs.2.trans hm)

theorem warm_solve_from_standing_joint
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u, y))))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ (1 + min (Real.sqrt (L / mu)) ((rho * D / mu) ^ (2 / 7 : ℝ))) *
        logFactor J mu L rho D tau x uInit yin := by
  have hconcave' : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu (JointSliceRegularity.curry J u) := by
    intro u
    have heq : JointSliceRegularity.curry J u = (fun y : F => J (WithLp.toLp 2 (u, y))) := by
      funext y
      exact congrArg J (JointSliceRegularity.point_eq_toLp u y)
    rw [heq]
    exact hconcave u
  exact actual_minimum_warm_solver J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess
    (JointSliceRegularity.strongConvex_negative_y_slice J mu hconcave') x uInit yin hwarm

end
end OriginalMinimumWarmSolver
end OriginalBorelWarmReplay
end
