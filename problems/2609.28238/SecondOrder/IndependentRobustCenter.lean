import SecondOrder.IndependentMajority
import SecondOrder.RobustBatch

open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

/-- Measurability needs only the observations and the finitely many distance
comparisons; no separability assumption is hidden in this lemma. -/
theorem robustCenter_measurable_of_dist {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] {R : ℕ} (hR : 0<R) (r : ℝ)
    (X : Fin R → Ω → E) (hX : ∀ i, Measurable (X i))
    (hd : ∀ i j, Measurable (fun w => dist (X j w) (X i w))) :
    Measurable (fun w => robustCenter hR (fun i => X i w) r) := by
  have hc : Measurable (fun w => neighborCode (fun i => X i w) r) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact Measurable.ite (measurableSet_le (hd i j) measurable_const) measurable_const measurable_const
  have hi : Measurable (fun w => codedCenterIndex hR (neighborCode (fun i => X i w) r)) :=
    (measurable_of_finite (codedCenterIndex hR)).comp hc
  have he : Measurable (fun p : Ω × Fin R => X p.2 p.1) := measurable_from_prod_countable hX
  simpa only [Function.comp_def,id_eq,robustCenter_eq_coded] using he.comp (measurable_id.prodMk hi)

/-- Borel measurability of the concrete selector on the topological finite
product, even when the metric space itself is not second countable. -/
theorem robustCenter_borel {E : Type*} [PseudoMetricSpace E] {R : ℕ} (hR : 0<R) (r : ℝ) :
    @Measurable (Fin R → E) E (borel (Fin R → E)) (borel E) (fun z => robustCenter hR z r) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  letI : MeasurableSpace (Fin R → E) := borel (Fin R → E)
  letI : BorelSpace (Fin R → E) := ⟨rfl⟩
  exact robustCenter_measurable_of_dist (Ω := Fin R → E) (E := E) (R := R) hR r (fun i z => z i)
    (fun i => (continuous_apply i).measurable)
    (fun i j => ((continuous_apply j).dist (continuous_apply i)).measurable)

theorem robustCenter_measurable_strong {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {R : ℕ}
    (hR : 0<R) (r : ℝ) (X : Fin R → Ω → E) (hX : ∀ i, StronglyMeasurable (X i)) :
    Measurable (fun w => robustCenter hR (fun i => X i w) r) := by
  apply robustCenter_measurable_of_dist hR r X (fun i => (hX i).measurable)
  intro i j
  simpa only [dist_eq_norm] using ((hX j).sub (hX i)).norm.measurable

theorem goodObservations_add_bad {Ω E : Type*} [PseudoMetricSpace E] {R : ℕ}
    (X : Fin R → Ω → E) (a : E) (r : ℝ) (w : Ω) :
    (goodObservations (fun i => X i w) a r).card+
      eventCount (fun i => {z | r<dist (X i z) a}) w=R := by
  simpa only [goodObservations,eventCount,Set.mem_setOf_eq,not_le,Finset.card_univ,Fintype.card_fin]
    using Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.univ) (fun i : Fin R => dist (X i w) a≤r)

variable {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E] [MeasurableSpace E]
  [BorelSpace E] {μ : Measure Ω} [IsProbabilityMeasure μ] {R : ℕ}
  {X : Fin R → Ω → E}

theorem independent_robustCenter_majority_failure (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (a : E) (r : ℝ)
    (hp : ∀ i, μ {w | r<dist (X i w) a}≤ENNReal.ofReal (1/4:ℝ)) :
    μ {w | R≤2*eventCount (fun i => {z | r<dist (X i z) a}) w}≤
      ENNReal.ofReal ((7/8:ℝ)^R) := by
  have hd : Measurable (fun x : E => dist x a) := (continuous_id.dist continuous_const).measurable
  have hB : MeasurableSet {x : E | r<dist x a} := measurableSet_lt measurable_const hd
  have hw : Measurable (trialWeight {x : E | r<dist x a}) :=
    Measurable.ite hB measurable_const measurable_const
  have hind := hi.comp (fun _ => trialWeight {x : E | r<dist x a}) (fun _ => hw)
  simpa only [Fintype.card_fin] using independent_eventCount_majority
    (fun i => hB.preimage (hX i)) hind hp

/-- The non-identically-distributed form: each marginal failure is at most
one quarter, and independence gives exponential confidence amplification. -/
theorem independent_robustCenter_failure (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (a : E) (r : ℝ) (hR : 0<R)
    (hp : ∀ i, μ {w | r<dist (X i w) a}≤ENNReal.ofReal (1/4:ℝ)) :
    μ {w | 3*r<dist (robustCenter hR (fun i => X i w) r) a}≤
      ENNReal.ofReal ((7/8:ℝ)^R) := by
  apply (measure_mono (t := {w | R≤2*eventCount (fun i => {z | r<dist (X i z) a}) w}) ?_).trans
    (independent_robustCenter_majority_failure hX hi a r hp)
  intro w hw
  by_contra hn
  change ¬R≤2*eventCount (fun i => {z | r<dist (X i z) a}) w at hn
  have hh := goodObservations_add_bad X a r w
  exact (not_lt_of_ge (robustCenter_close hR (fun i => X i w) a r (by omega))) hw

theorem confidencePower_sufficient {δ : ℝ} (hδ : 0<δ) (R : ℕ)
    (hR : 8*Real.log (1/δ)≤(R:ℝ)) : (7/8:ℝ)^R≤δ := by
  have hlog : Real.log (1/δ)=-Real.log δ := by
    rw [Real.log_div (by norm_num) hδ.ne',Real.log_one]; ring
  rw [hlog] at hR
  have he : (7/8:ℝ)≤Real.exp (-(1/8:ℝ)) := by
    linarith [Real.add_one_le_exp (-(1/8:ℝ))]
  calc
    _ ≤ Real.exp (-(1/8:ℝ))^R := pow_le_pow_left₀ (by norm_num) he R
    _ = Real.exp ((R:ℝ)*(-(1/8:ℝ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.mpr (by linarith)
    _ = δ := Real.exp_log hδ

/-- Manuscript robust-center confidence with explicit constant C=8.
The selector itself is independent of the unknown center and of all laws. -/
theorem independent_robustCenter_confidence (hX : ∀ i, Measurable (X i))
    (hi : iIndepFun X μ) (a : E) (r : ℝ) (hR : 0<R)
    (hp : ∀ i, ENNReal.ofReal (3/4:ℝ)≤μ {w | dist (X i w) a≤r})
    {δ : ℝ} (hδ : 0<δ) (hsize : 8*Real.log (1/δ)≤(R:ℝ)) :
    ENNReal.ofReal (1-δ)≤μ {w | dist (robustCenter hR (fun i => X i w) r) a≤3*r} := by
  let B : Fin R → Set Ω := fun i => {w | r<dist (X i w) a}
  have hd : Measurable (fun x : E => dist x a) := (continuous_id.dist continuous_const).measurable
  have hB : ∀ i, MeasurableSet (B i) := fun i => measurableSet_lt measurable_const (hd.comp (hX i))
  have hpB : ∀ i, μ (B i)≤ENNReal.ofReal (1/4:ℝ) := by
    intro i
    have hc : B i={w | dist (X i w) a≤r}ᶜ := by ext w; simp [B]
    have hg : MeasurableSet {w | dist (X i w) a≤r} :=
      measurableSet_le (hd.comp (hX i)) measurable_const
    rw [hc,measure_compl hg (measure_ne_top _ _),measure_univ]
    apply (tsub_le_tsub_left (hp i) (1:ℝ≥0∞)).trans_eq
    rw [←ENNReal.ofReal_one,←ENNReal.ofReal_sub 1 (by norm_num : (0:ℝ)≤3/4)]
    norm_num
  let bad := {w | R≤2*eventCount B w}
  have hbad : MeasurableSet bad := measurableSet_le measurable_const
    (measurable_const.mul (eventCount_measurable hB))
  have htail : μ bad≤ENNReal.ofReal δ :=
    (independent_robustCenter_majority_failure hX hi a r hpB).trans
      (ENNReal.ofReal_le_ofReal (confidencePower_sufficient hδ R hsize))
  have hc : ENNReal.ofReal (1-δ)≤μ badᶜ := by
    rw [ENNReal.ofReal_sub 1 hδ.le,ENNReal.ofReal_one,measure_compl hbad (measure_ne_top _ _),measure_univ]
    exact tsub_le_tsub_left htail 1
  apply hc.trans (measure_mono ?_)
  intro w hw
  have hh := goodObservations_add_bad X a r w
  have hn : ¬R≤2*eventCount B w := hw
  exact robustCenter_close hR (fun i => X i w) a r (by dsimp only [B] at hn; omega)

/-- The usual real-valued probability statement for strongly measurable
Hilbert-valued observations; it already holds in a normed abelian group.
This also verifies measurability of the composed output without assuming
that the whole value space has a countable base. -/
theorem independent_robustCenter_norm_confidence {H : Type*} [NormedAddCommGroup H]
    [MeasurableSpace H] [BorelSpace H] {Z : Fin R → Ω → H}
    (hZ : ∀ i, StronglyMeasurable (Z i)) (hi : iIndepFun Z μ)
    (a : H) (r : ℝ) (hR : 0<R)
    (hp : ∀ i, ENNReal.ofReal (3/4:ℝ)≤μ {w | ‖Z i w-a‖≤r})
    {δ : ℝ} (hδ : 0<δ) (hδ1 : δ≤1) (hsize : 8*Real.log (1/δ)≤(R:ℝ)) :
    Measurable (fun w => robustCenter hR (fun i => Z i w) r) ∧
      1-δ≤μ.real {w | ‖robustCenter hR (fun i => Z i w) r-a‖≤3*r} := by
  refine ⟨robustCenter_measurable_strong hR r Z hZ,?_⟩
  have hpm : ∀ i, ENNReal.ofReal (3/4:ℝ)≤μ {w | dist (Z i w) a≤r} := by
    simpa only [dist_eq_norm] using hp
  have hh := independent_robustCenter_confidence (fun i => (hZ i).measurable) hi a r hR hpm hδ hsize
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1),dist_eq_norm] using ht

end
end SecondOrder
