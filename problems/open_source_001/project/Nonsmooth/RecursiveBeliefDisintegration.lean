import Nonsmooth.RecursiveSupportBelief
import Nonsmooth.RecursiveSupportResponse
import Nonsmooth.ConditionalReencoding

open MeasureTheory ProbabilityTheory Set Filter
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

theorem conditionalKernel_reencoding {α β γ Ω : Type}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace Ω]
    [StandardBorelSpace β] [Nonempty β]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → α) (hX : Measurable X) (Y : Ω → β) (hY : Measurable Y)
    (Z : Ω → γ) (hZ : Measurable Z)
    (f : α → γ) (hf : Measurable f) (g : γ → α) (hg : Measurable g)
    (hZX : ∀ a, Z a = f (X a)) (hXZ : ∀ a, g (Z a) = X a)
    (κ : Kernel α β) (hκ : ∀ᵐ x ∂μ.map X, κ x = condDistrib Y X μ x) :
    ∀ᵐ z ∂μ.map Z, κ (g z) = condDistrib Y Z μ z := by
  have hm : (μ.map Z).map g = μ.map X := by
    rw [Measure.map_map hg hZ]
    congr 1
    funext a
    exact hXZ a
  rw [← hm] at hκ
  filter_upwards [ae_of_ae_map hg.aemeasurable hκ,
    condDistrib_reencoding μ X hX Y hY Z hZ f hf g hg hZX hXZ] with z hk he
  exact hk.trans he

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {k : ℕ} [Nonempty (Fin k)]

theorem recursiveSupportBelief_disintegrates (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    (Q.map (recursiveSupportResponse u n)) ⊗ₘ recursiveSupportBelief Q u hu n =
      Q.map (fun a => (recursiveSupportResponse u n a, a)) := by
  induction n with
  | zero =>
    change (Q.map (fun _ : Fin k → E => (Fin.elim0 : ResponseHistory k 0))) ⊗ₘ Kernel.const _ Q =
      Q.map (fun a => ((Fin.elim0 : ResponseHistory k 0), a))
    simp only [Measure.map_const, measure_univ, one_smul]
    ext S hS
    rw [Measure.dirac_compProd_apply hS, Kernel.const_apply,
      Measure.map_apply measurable_prodMk_left hS]
  | succ n ih =>
    let X := recursiveSupportResponse u n
    let Z := recursiveSupportResponse u (n + 1)
    let K := recursiveSupportBelief Q u hu n
    let F : ResponseHistory k n × (Fin k → E) → Fin k × ℝ :=
      fun p => supportSingleObservation (u n p.1) p.2
    let W : (Fin k → E) → ResponseHistory k n × (Fin k × ℝ) := fun a => (X a, F (X a, a))
    have hX : Measurable X := recursiveSupportResponse_measurable u hu n
    have hZ : Measurable Z := recursiveSupportResponse_measurable u hu (n + 1)
    have hF : Measurable F := supportParametricObservation_measurable (u n) (hu n)
    have hW : Measurable W := hX.prodMk (hF.comp (hX.prodMk measurable_id))
    have hnew := observedPosterior_update_ae_eq Q X hX id measurable_id K ih F hF
    have hencode := conditionalKernel_reencoding Q W hW id measurable_id Z hZ
      responseHistoryJoin responseHistoryJoin_measurable
      responseHistorySplit responseHistorySplit_measurable
      (fun _ => rfl) (fun a => recursiveSupportResponse_split u n a)
      (observedPosterior K F hF) hnew
    have hcorrect : ∀ᵐ h ∂Q.map Z,
        recursiveSupportBelief Q u hu (n + 1) h = condDistrib id Z Q h := by
      filter_upwards [hencode] with h hh
      exact hh
    rw [Measure.compProd_congr hcorrect]
    exact compProd_map_condDistrib aemeasurable_id

theorem recursiveSupportBelief_ae_condDistrib (Q : Measure (Fin k → E)) [IsProbabilityMeasure Q]
    (u : ∀ n, ResponseHistory k n → E) (hu : ∀ n, Measurable (u n)) (n : ℕ) :
    ∀ᵐ h ∂Q.map (recursiveSupportResponse u n),
      recursiveSupportBelief Q u hu n h = condDistrib id (recursiveSupportResponse u n) Q h := by
  exact (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (recursiveSupportResponse_measurable u hu n) measurable_id
    (recursiveSupportBelief_disintegrates Q u hu n).symm).symm

end
end Nonsmooth
