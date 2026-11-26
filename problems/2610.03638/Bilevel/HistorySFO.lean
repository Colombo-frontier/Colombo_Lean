import Bilevel.FirstOrderSFO
import Bilevel.HistoryOracle
import Mathlib.MeasureTheory.Integral.Prod

/-! The manuscript's full SFO scope with conditional, history-dependent laws.

`FirstOrderSFO.Oracle` is a convenient stationary fresh-seed realization.  The
structure below records the more general source interface directly: at a
history `h`, the fresh sample law may be `law h`.  The x/y errors in one call
share the same seed, so no within-call independence is imposed. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace Bilevel.Stateful

/-- One original full-gradient observation: the upper and lower blocks are
recorded together.  The pair is retained by the history kernel so that the
two block errors may be correlated. -/
abbrev FullResponse (X Y : Type*) := (X × Y) × (X × Y)

/-- Conditional moment interface for a joint full-gradient response kernel.
The kernel itself is a parameter, rather than an extra field, so upper and
lower projections share exactly the same conditional observation law. -/
structure FullGradientLaw {Query History Obs X Y : Type*}
    [MeasurableSpace Query] [MeasurableSpace History] [MeasurableSpace Obs]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (K : Kernel (Query × History) Obs) (rx : Obs → X) (ry : Obs → Y)
    (σ : ℝ) where
  truth_x : Query → X
  truth_y : Query → Y
  truth_x_measurable : Measurable truth_x
  truth_y_measurable : Measurable truth_y
  rx_measurable : Measurable rx
  ry_measurable : Measurable ry
  square_integrable : ∀ q h, Integrable
    (fun o => ‖rx o - truth_x q‖ ^ 2 + ‖ry o - truth_y q‖ ^ 2) (K (q,h))
  mean_x : ∀ q h, (∫ o, rx o - truth_x q ∂K (q,h)) = 0
  mean_y : ∀ q h, (∫ o, ry o - truth_y q ∂K (q,h)) = 0
  variance : ∀ q h, (∫ o,
    ‖rx o - truth_x q‖ ^ 2 + ‖ry o - truth_y q‖ ^ 2 ∂K (q,h)) ≤ σ ^ 2

/-- The full history-dependent SFO source.  `upper` and `lower` are the two
projections of the same `law`; `update` is applied after every response and
can therefore make future conditional laws depend on the complete history. -/
structure HistorySFO {Query History X Y : Type*}
    [MeasurableSpace Query] [MeasurableSpace History]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (σf σg : ℝ) where
  law : Kernel (Query × History) (FullResponse X Y)
  markov : IsMarkovKernel law
  update : (Query × History) × FullResponse X Y → History
  update_measurable : Measurable update
  upper : FullGradientLaw law (fun o => o.1.1) (fun o => o.1.2) σf
  lower : FullGradientLaw law (fun o => o.2.1) (fun o => o.2.2) σg

attribute [instance] HistorySFO.markov

namespace FullGradientLaw

variable {Query History Obs X Y : Type*}
  [MeasurableSpace Query] [MeasurableSpace History] [MeasurableSpace Obs]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {K : Kernel (Query × History) Obs} {rx : Obs → X} {ry : Obs → Y}
  {σ : ℝ} (G : FullGradientLaw K rx ry σ)

theorem x_square_integrable (q : Query) (h : History) :
    Integrable (fun o => ‖rx o - G.truth_x q‖ ^ 2) (K (q,h)) := by
  apply (G.square_integrable q h).mono'
    ((((G.rx_measurable.comp measurable_id).sub
      (G.truth_x_measurable.comp measurable_const)).norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [] with o
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem y_square_integrable (q : Query) (h : History) :
    Integrable (fun o => ‖ry o - G.truth_y q‖ ^ 2) (K (q,h)) := by
  apply (G.square_integrable q h).mono'
    ((((G.ry_measurable.comp measurable_id).sub
      (G.truth_y_measurable.comp measurable_const)).norm.pow_const 2).aestronglyMeasurable)
  filter_upwards [] with o
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem x_variance (q : Query) (h : History) :
    (∫ o, ‖rx o - G.truth_x q‖ ^ 2 ∂K (q,h)) ≤ σ ^ 2 := by
  exact (integral_mono (x_square_integrable G q h) (G.square_integrable q h)
    (fun _ => le_add_of_nonneg_right (sq_nonneg _))).trans (G.variance q h)

theorem y_variance (q : Query) (h : History) :
    (∫ o, ‖ry o - G.truth_y q‖ ^ 2 ∂K (q,h)) ≤ σ ^ 2 := by
  exact (integral_mono (y_square_integrable G q h) (G.square_integrable q h)
    (fun _ => le_add_of_nonneg_left (sq_nonneg _))).trans (G.variance q h)

def xOracle [IsMarkovKernel K] (hx : Measurable rx)
    (update : (Query × History) × Obs → History) (hu : Measurable update) :
    HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := X) σ where
  law := K
  markov := inferInstance
  read := rx
  read_measurable := hx
  truth := G.truth_x
  truth_measurable := G.truth_x_measurable
  update := update
  update_measurable := hu
  square_integrable := x_square_integrable G
  mean := G.mean_x
  variance := x_variance G

def yOracle [IsMarkovKernel K] (hy : Measurable ry)
    (update : (Query × History) × Obs → History) (hu : Measurable update) :
    HistoryOracle (Query := Query) (History := History) (Obs := Obs) (E := Y) σ where
  law := K
  markov := inferInstance
  read := ry
  read_measurable := hy
  truth := G.truth_y
  truth_measurable := G.truth_y_measurable
  update := update
  update_measurable := hu
  square_integrable := y_square_integrable G
  mean := G.mean_y
  variance := y_variance G

end FullGradientLaw

namespace HistorySFO

variable {Query History X Y : Type*}
  [MeasurableSpace Query] [MeasurableSpace History]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  {σf σg : ℝ}
  (O : HistorySFO (Query := Query) (History := History) (X := X) (Y := Y) σf σg)

def fx : HistoryOracle (Query := Query) (History := History)
    (Obs := FullResponse X Y) (E := X) σf :=
  { law := O.law
    markov := O.markov
    read := fun o => o.1.1
    read_measurable := by fun_prop
    truth := O.upper.truth_x
    truth_measurable := O.upper.truth_x_measurable
    update := O.update
    update_measurable := O.update_measurable
    square_integrable := FullGradientLaw.x_square_integrable O.upper
    mean := O.upper.mean_x
    variance := FullGradientLaw.x_variance O.upper }

def fy : HistoryOracle (Query := Query) (History := History)
    (Obs := FullResponse X Y) (E := Y) σf :=
  { law := O.law
    markov := O.markov
    read := fun o => o.1.2
    read_measurable := by fun_prop
    truth := O.upper.truth_y
    truth_measurable := O.upper.truth_y_measurable
    update := O.update
    update_measurable := O.update_measurable
    square_integrable := FullGradientLaw.y_square_integrable O.upper
    mean := O.upper.mean_y
    variance := FullGradientLaw.y_variance O.upper }

def gx : HistoryOracle (Query := Query) (History := History)
    (Obs := FullResponse X Y) (E := X) σg :=
  { law := O.law
    markov := O.markov
    read := fun o => o.2.1
    read_measurable := by fun_prop
    truth := O.lower.truth_x
    truth_measurable := O.lower.truth_x_measurable
    update := O.update
    update_measurable := O.update_measurable
    square_integrable := FullGradientLaw.x_square_integrable O.lower
    mean := O.lower.mean_x
    variance := FullGradientLaw.x_variance O.lower }

def gy : HistoryOracle (Query := Query) (History := History)
    (Obs := FullResponse X Y) (E := Y) σg :=
  { law := O.law
    markov := O.markov
    read := fun o => o.2.2
    read_measurable := by fun_prop
    truth := O.lower.truth_y
    truth_measurable := O.lower.truth_y_measurable
    update := O.update
    update_measurable := O.update_measurable
    square_integrable := FullGradientLaw.y_square_integrable O.lower
    mean := O.lower.mean_y
    variance := FullGradientLaw.y_variance O.lower }

end HistorySFO

end Bilevel.Stateful

namespace Bilevel.HistorySFO

variable {History Query Seed X Y : Type*}
  [MeasurableSpace History] [MeasurableSpace Query] [MeasurableSpace Seed]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

structure Oracle (σ : ℝ) where
  law : History → Measure Seed
  law_probability : ∀ h, IsProbabilityMeasure (law h)
  truth_x : Query → X
  truth_y : Query → Y
  sample_x : History → Query → Seed → X
  sample_y : History → Query → Seed → Y
  truth_x_measurable : Measurable truth_x
  truth_y_measurable : Measurable truth_y
  sample_x_measurable : Measurable (fun p : History × Query × Seed =>
    sample_x p.1 p.2.1 p.2.2)
  sample_y_measurable : Measurable (fun p : History × Query × Seed =>
    sample_y p.1 p.2.1 p.2.2)
  x_square_integrable : ∀ h q, Integrable
    (fun s => ‖sample_x h q s - truth_x q‖ ^ 2) (law h)
  y_square_integrable : ∀ h q, Integrable
    (fun s => ‖sample_y h q s - truth_y q‖ ^ 2) (law h)
  mean_x : ∀ h q, (∫ s, sample_x h q s - truth_x q ∂law h) = 0
  mean_y : ∀ h q, (∫ s, sample_y h q s - truth_y q ∂law h) = 0
  variance : ∀ h q, (∫ s,
    ‖sample_x h q s - truth_x q‖ ^ 2 +
      ‖sample_y h q s - truth_y q‖ ^ 2 ∂law h) ≤ σ ^ 2

variable {σ : ℝ} (O : Oracle (History := History) (Query := Query)
  (Seed := Seed) (X := X) (Y := Y) σ)

def xError (O : Oracle (History := History) (Query := Query)
    (Seed := Seed) (X := X) (Y := Y) σ) (h : History) (q : Query) (s : Seed) : X :=
  O.sample_x h q s - O.truth_x q

def yError (O : Oracle (History := History) (Query := Query)
    (Seed := Seed) (X := X) (Y := Y) σ) (h : History) (q : Query) (s : Seed) : Y :=
  O.sample_y h q s - O.truth_y q

omit [CompleteSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem xError_centered (h : History) (q : Query) :
    (∫ s, xError O h q s ∂O.law h) = 0 := O.mean_x h q

omit [CompleteSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem yError_centered (h : History) (q : Query) :
    (∫ s, yError O h q s ∂O.law h) = 0 := O.mean_y h q

omit [CompleteSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem xError_variance (h : History) (q : Query) :
    (∫ s, ‖xError O h q s‖ ^ 2 ∂O.law h) ≤ σ ^ 2 := by
  have hsum := (O.x_square_integrable h q).add (O.y_square_integrable h q)
  have hle : (∫ s, ‖xError O h q s‖ ^ 2 ∂O.law h) ≤
      ∫ s, (‖xError O h q s‖ ^ 2 + ‖yError O h q s‖ ^ 2) ∂O.law h := by
    apply integral_mono (O.x_square_integrable h q) hsum
    intro s
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact hle.trans (O.variance h q)

omit [CompleteSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
theorem yError_variance (h : History) (q : Query) :
    (∫ s, ‖yError O h q s‖ ^ 2 ∂O.law h) ≤ σ ^ 2 := by
  have hsum := (O.x_square_integrable h q).add (O.y_square_integrable h q)
  have hle : (∫ s, ‖yError O h q s‖ ^ 2 ∂O.law h) ≤
      ∫ s, (‖xError O h q s‖ ^ 2 + ‖yError O h q s‖ ^ 2) ∂O.law h := by
    apply integral_mono (O.y_square_integrable h q) hsum
    intro s
    exact le_add_of_nonneg_left (sq_nonneg _)
  exact hle.trans (O.variance h q)

omit [CompleteSpace X] [BorelSpace X] [SecondCountableTopology X]
  [CompleteSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- The conditional statement used by the source: after fixing the full history,
query randomness is centered and has the advertised second-moment bound. -/
theorem conditional_call_spec (h : History) (q : Query) :
    (∫ s, xError O h q s ∂O.law h) = 0 ∧
    (∫ s, yError O h q s ∂O.law h) = 0 ∧
    (∫ s, ‖xError O h q s‖ ^ 2 + ‖yError O h q s‖ ^ 2 ∂O.law h) ≤ σ ^ 2 := by
  exact ⟨O.mean_x h q, O.mean_y h q, O.variance h q⟩

def ofStationary {ν : Measure Seed} [IsProbabilityMeasure ν]
    (O : Bilevel.FirstOrderSFO.Oracle (Query := Query) (X := X) (Y := Y) ν σ) :
    Oracle (History := History) (Query := Query) (Seed := Seed)
      (X := X) (Y := Y) σ where
  law := fun _ => ν
  law_probability := fun _ => inferInstance
  truth_x := O.truth_x
  truth_y := O.truth_y
  sample_x := fun _ => O.sample_x
  sample_y := fun _ => O.sample_y
  truth_x_measurable := O.truth_x_measurable
  truth_y_measurable := O.truth_y_measurable
  sample_x_measurable := by
    simpa only using O.sample_x_measurable.comp measurable_snd
  sample_y_measurable := by
    simpa only using O.sample_y_measurable.comp measurable_snd
  x_square_integrable := fun h q => O.x_square_integrable q
  y_square_integrable := fun h q => O.y_square_integrable q
  mean_x := fun h q => O.mean_x q
  mean_y := fun h q => O.mean_y q
  variance := fun h q => O.variance q

end Bilevel.HistorySFO
