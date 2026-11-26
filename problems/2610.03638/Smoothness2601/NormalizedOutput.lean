import Smoothness2601.NormalizedPotential

/-! Integrable expected stationarity of the actual independently uniform
iterate sampled from the executed normalized path. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace Smoothness2601.NormalizedExecution
open Bilevel.Stateful

variable {X Y History : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [MeasurableSpace History]

theorem expected_gradient_sum (A : Procedure (X × Y) History X) (f : X → ℝ) (g : X → X)
    {L η δ R : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (floor : ℝ) (hfloor : ∀ x, floor ≤ f x) (n : ℕ) (hR : (n:ℝ)*η ≤ R)
    (p : X × Y) (history : History)
    (hA : ∀ x h, ‖x-p.1‖ ≤ R →
      Integrable (fun z => ‖z.1-g x‖) (A.law ((x,p.2),h)) ∧
      (∫ z, ‖z.1-g x‖ ∂A.law ((x,p.2),h)) ≤ δ) :
    Integrable (fun z => gradientSum g n z.1) ((run A η n).law (p,history)) ∧
    (∫ z, gradientSum g n z.1 ∂(run A η n).law (p,history)) ≤
      (f p.1-floor+(n:ℝ)*(2*η*δ+L*η ^ 2/2))/η := by
  have he := expected_energy A f g hL hη.le hf hg floor hfloor n hR p history hA n le_rfl
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := ⟨L,hL⟩)
    (fun x z => by simpa only [dist_eq_norm,NNReal.coe_mk] using hg x z)).continuous
  have hm : Measurable (fun z : Outcome (Path X n) History => gradientSum g n z.1) :=
    Finset.measurable_sum _ (fun i _ => (hgc.measurable.comp
      ((measurable_pi_apply i.castSucc).comp measurable_fst)).norm)
  have hp (v : Path X n) : gradientSum g n v ≤ energy f g floor η n v/η := by
    apply (le_div_iff₀ hη).mpr
    have := hfloor (v (Fin.last n))
    unfold energy
    nlinarith
  have hi : Integrable (fun z => gradientSum g n z.1) ((run A η n).law (p,history)) := by
    apply (he.1.div_const η).mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (show 0 ≤ gradientSum g n z.1 from
      Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact hp z.1
  refine ⟨hi,?_⟩
  have hb := integral_mono hi (he.1.div_const η) (fun z => hp z.1)
  rw [integral_div] at hb
  exact hb.trans (div_le_div_of_nonneg_right he.2 hη.le)

theorem expected_selected_norm (A : Procedure (X × Y) History X) (f : X → ℝ) (g : X → X)
    {L η δ R Δ : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : ∀ x z, ‖g x-g z‖ ≤ L*‖x-z‖)
    (floor : ℝ) (hfloor : ∀ x, floor ≤ f x) (n : ℕ) [NeZero n] (hR : (n:ℝ)*η ≤ R)
    (p : X × Y) (history : History) (hgap : f p.1-floor ≤ Δ)
    (hA : ∀ x h, ‖x-p.1‖ ≤ R →
      Integrable (fun z => ‖z.1-g x‖) (A.law ((x,p.2),h)) ∧
      (∫ z, ‖z.1-g x‖ ∂A.law ((x,p.2),h)) ≤ δ) :
    Integrable (fun z => ‖g (selected z)‖) (outputLaw A η n p history) ∧
    (∫ z, ‖g (selected z)‖ ∂outputLaw A η n p history) ≤ Δ/((n:ℝ)*η)+2*δ+L*η/2 := by
  classical
  have hs := expected_gradient_sum A f g hL hη hf hg floor hfloor n hR p history hA
  let π := (run A η n).law (p,history)
  let F : Fin n → Outcome (Path X n) History → ℝ := fun i z => ‖g (z.1 i.castSucc)‖
  have hgc : Continuous g := (LipschitzWith.of_dist_le_mul (K := ⟨L,hL⟩)
    (fun x z => by simpa only [dist_eq_norm,NNReal.coe_mk] using hg x z)).continuous
  have hi (i : Fin n) : Integrable (F i) π := by
    have hm : Measurable (F i) := (hgc.measurable.comp
      ((measurable_pi_apply i.castSucc).comp measurable_fst)).norm
    apply hs.1.mono' hm.aestronglyMeasurable
    filter_upwards with z
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact Finset.single_le_sum (fun j _ => norm_nonneg (g (z.1 j.castSucc))) (Finset.mem_univ i)
  have hind (i : Fin n) : Integrable (fun z : Fin n × Outcome (Path X n) History =>
      (if z.1=i then (1:ℝ) else 0)*F i z.2) ((Bilevel.StochasticOuter.uniformLaw n).prod π) := by
    have hc : Integrable (fun j : Fin n => if j=i then (1:ℝ) else 0) (Bilevel.StochasticOuter.uniformLaw n) := by
      simpa only [integrableOn_univ] using
        (IntegrableOn.of_finite Set.finite_univ : IntegrableOn
          (fun j : Fin n => if j=i then (1:ℝ) else 0) Set.univ (Bilevel.StochasticOuter.uniformLaw n))
    exact hc.mul_prod (hi i)
  have hp : Integrable (fun z : Fin n × Outcome (Path X n) History => F z.1 z.2)
      ((Bilevel.StochasticOuter.uniformLaw n).prod π) := by
    convert integrable_finset_sum Finset.univ (fun i _ => hind i) using 1
    funext z
    simp
  refine ⟨hp,?_⟩
  change (∫ z : Fin n × Outcome (Path X n) History, F z.1 z.2
    ∂(Bilevel.StochasticOuter.uniformLaw n).prod π) ≤ _
  rw [integral_prod _ hp,Bilevel.StochasticOuter.uniform_integral]
  have hsum : (∑ i : Fin n, ∫ z, F i z ∂π) = ∫ z, gradientSum g n z.1 ∂π := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hi i)]
    rfl
  rw [hsum]
  have hn : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero n)
  calc
    _ ≤ ((f p.1-floor+(n:ℝ)*(2*η*δ+L*η ^ 2/2))/η)/(n:ℝ) :=
      div_le_div_of_nonneg_right hs.2 hn.le
    _ = (f p.1-floor)/((n:ℝ)*η)+2*δ+L*η/2 := by field_simp; ring
    _ ≤ _ := add_le_add_right (add_le_add_right
      (div_le_div_of_nonneg_right hgap (mul_nonneg hn.le hη.le)) _) _

end Smoothness2601.NormalizedExecution
