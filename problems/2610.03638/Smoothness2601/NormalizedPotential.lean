import Smoothness2601.NormalizedExecution
import Smoothness2601.OuterMoments

/-! Expected descent potential for the executed normalized path, using only
first moments of the actual direction error on the reachable travel ball. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Smoothness2601.NormalizedExecution
open Bilevel.Stateful

variable {X Y History : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [MeasurableSpace History]

def gradientSum (g : X → X) (n : ℕ) (v : Path X n) : ℝ := ∑ i : Fin n, ‖g (v i.castSucc)‖
def energy (f : X → ℝ) (g : X → X) (floor η : ℝ) (n : ℕ) (v : Path X n) : ℝ :=
  f (v (Fin.last n))-floor+η*gradientSum g n v

omit [InnerProductSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] in
theorem gradientSum_append (g : X → X) (n : ℕ) (v : Path X n) (x : X) :
    gradientSum g (n+1) (Fin.snoc v x) = gradientSum g n v+‖g (v (Fin.last n))‖ := by
  rw [gradientSum,Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc,gradientSum]

omit [InnerProductSpace ℝ X] [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] in
theorem energy_nonnegative (f : X → ℝ) (g : X → X) {η : ℝ} (hη : 0 ≤ η)
    (floor : ℝ) (hfloor : ∀ x, floor ≤ f x) (n : ℕ) (v : Path X n) :
    0 ≤ energy f g floor η n v :=
  add_nonneg (sub_nonneg.mpr (hfloor _))
    (mul_nonneg hη (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

omit [InnerProductSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X] in
theorem energy_measurable (f : X → ℝ) (g : X → X) (hf : Continuous f) (hg : Continuous g)
    (floor η : ℝ) (n : ℕ) : Measurable (energy f g floor η n) := by
  have hm : Measurable (gradientSum g n) := Finset.measurable_sum _ (fun i _ =>
    (hg.measurable.comp (measurable_pi_apply i.castSucc)).norm)
  exact ((hf.measurable.comp (measurable_pi_apply (Fin.last n))).sub_const floor).add (hm.const_mul η)

omit [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] in
theorem energy_append_le (f : X → ℝ) (g : X → X) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (floor : ℝ) (n : ℕ) (v : Path X n) (q : X) :
    energy f g floor η (n+1) (Fin.snoc v (NormalizedOuter.step (v (Fin.last n)) q η)) ≤
      energy f g floor η n v+2*η*‖q-g (v (Fin.last n))‖+L*η ^ 2/2 := by
  have hd := NormalizedOuter.smooth_descent f g hL hη hf hg (v (Fin.last n)) q
  unfold energy
  rw [gradientSum_append,Fin.snoc_last]
  linarith

theorem one_step_energy (A : Procedure (X × Y) History X) (f : X → ℝ) (g : X → X)
    {L η δ : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (floor : ℝ) (hfloor : ∀ x, floor ≤ f x) (n : ℕ) (p : X × Y) (v : Path X n) (history : History)
    (hA : Integrable (fun z => ‖z.1-g (v (Fin.last n))‖) (A.law ((v (Fin.last n),p.2),history)) ∧
      (∫ z, ‖z.1-g (v (Fin.last n))‖ ∂A.law ((v (Fin.last n),p.2),history)) ≤ δ) :
    Integrable (fun z => energy f g floor η (n+1) z.1) ((step A η n).law ((p,v),history)) ∧
    (∫ z, energy f g floor η (n+1) z.1 ∂(step A η n).law ((p,v),history)) ≤
      energy f g floor η n v+2*η*δ+L*η ^ 2/2 := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).hasFDerivAt.continuousAt)
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := ⟨L,hL⟩)
    (fun x z => by simpa only [dist_eq_norm,NNReal.coe_mk] using hg x z)).continuous
  have he := energy_measurable f g hfc hgc floor η (n+1)
  have hm : Measurable (fun z : Outcome X History => energy f g floor η (n+1)
      (append η n ((p,v),z.1))) := he.comp
        ((append_measurable η n).comp (measurable_const.prodMk measurable_fst))
  have hd := ((integrable_const (energy f g floor η n v)).add (hA.1.const_mul (2*η))).add
    (integrable_const (L*η ^ 2/2))
  have hi : Integrable (fun z => energy f g floor η (n+1) (append η n ((p,v),z.1)))
      (A.law ((v (Fin.last n),p.2),history)) := by
    apply hd.mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (energy_nonnegative f g hη floor hfloor _ _)]
    exact energy_append_le f g hL hη hf hg floor n v z.1
  have hb := integral_mono hi hd (fun z => energy_append_le f g hL hη hf hg floor n v z.1)
  have he₁ := integral_add (integrable_const (energy f g floor η n v)) (hA.1.const_mul (2*η))
  have he₂ := integral_add ((integrable_const (energy f g floor η n v)).add (hA.1.const_mul (2*η)))
    (integrable_const (L*η ^ 2/2))
  simp only [Pi.add_apply] at he₁ he₂ hb
  rw [he₂,he₁,integral_const_mul] at hb
  simp only [integral_const,measureReal_univ_eq_one,one_smul] at hb
  constructor
  · rw [step,Procedure.map_output_integrable_iff _ _ _ _ _ _ he.stronglyMeasurable]
    exact hi
  · rw [step,Procedure.map_output_integral _ _ _ _ _ _ he.stronglyMeasurable]
    exact hb.trans (add_le_add_right (add_le_add_left
      (mul_le_mul_of_nonneg_left hA.2 (by positivity)) _) _)

theorem expected_energy (A : Procedure (X × Y) History X) (f : X → ℝ) (g : X → X)
    {L η δ R : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (floor : ℝ) (hfloor : ∀ x, floor ≤ f x) (K : ℕ) (hR : (K:ℝ)*η ≤ R)
    (p : X × Y) (history : History)
    (hA : ∀ x h, ‖x-p.1‖ ≤ R →
      Integrable (fun z => ‖z.1-g x‖) (A.law ((x,p.2),h)) ∧
      (∫ z, ‖z.1-g x‖ ∂A.law ((x,p.2),h)) ≤ δ)
    (n : ℕ) (hn : n ≤ K) :
    Integrable (fun z => energy f g floor η n z.1) ((run A η n).law (p,history)) ∧
    (∫ z, energy f g floor η n z.1 ∂(run A η n).law (p,history)) ≤
      f p.1-floor+(n:ℝ)*(2*η*δ+L*η ^ 2/2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).hasFDerivAt.continuousAt)
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := ⟨L,hL⟩)
    (fun x z => by simpa only [dist_eq_norm,NNReal.coe_mk] using hg x z)).continuous
  revert hn
  induction n with
  | zero =>
    intro _
    rw [run,Procedure.pure_law]
    have hm : StronglyMeasurable (fun z : Outcome (Path X 0) History => energy f g floor η 0 z.1) :=
      ((energy_measurable f g hfc hgc floor η 0).comp measurable_fst).stronglyMeasurable
    refine ⟨integrable_dirac' hm,?_⟩
    rw [integral_dirac' _ _ hm]
    simp [energy,gradientSum]
  | succ n ih =>
    intro hn
    have ih := ih (Nat.le_of_succ_le hn)
    have hcond : ∀ᵐ z ∂(run A η n).law (p,history),
        Integrable (fun w => energy f g floor η (n+1) w.1) ((step A η n).law ((p,z.1),z.2.1)) ∧
        (∫ w, energy f g floor η (n+1) w.1 ∂(step A η n).law ((p,z.1),z.2.1)) ≤
          energy f g floor η n z.1+2*η*δ+L*η ^ 2/2 := by
      filter_upwards [run_travel A hη n p history] with z hz
      have hdist : ‖z.1 (Fin.last n)-p.1‖ ≤ R := hz.trans
        ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.le_of_succ_le hn)) hη).trans hR)
      exact one_step_energy A f g hL hη hf hg floor hfloor n p z.1 z.2.1 (hA _ _ hdist)
    have hb := OuterMoments.bind_output_bound_ae (run A η n) (step A η n) p history
      (energy f g floor η (n+1)) (energy_measurable f g hfc hgc floor η (n+1))
      (energy_nonnegative f g hη floor hfloor (n+1))
      (fun v => energy f g floor η n v+2*η*δ+L*η ^ 2/2)
      ((ih.1.add (integrable_const _)).add (integrable_const _))
      (hcond.mono (fun _ hz => hz.1)) (hcond.mono (fun _ hz => hz.2))
    refine ⟨hb.1,hb.2.trans ?_⟩
    have he₁ := integral_add ih.1 (integrable_const (2*η*δ))
    have he₂ := integral_add (ih.1.add (integrable_const (2*η*δ))) (integrable_const (L*η ^ 2/2))
    simp only [Pi.add_apply] at he₁ he₂
    rw [he₂,he₁]
    simp only [integral_const,measureReal_univ_eq_one,one_smul]
    push_cast
    linarith [ih.2]

end Smoothness2601.NormalizedExecution
