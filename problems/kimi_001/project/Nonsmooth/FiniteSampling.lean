import Nonsmooth.SphericalLaw
import Nonsmooth.Minimax
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Each coordinate of a finite product of one probability law has that law. -/
theorem finite_product_coordinate (ν : Measure A) [IsProbabilityMeasure ν]
    {T : ℕ} (i : Fin T) :
    MeasurePreserving (fun ω : Fin T → A => ω i) (Measure.pi (fun _ => ν)) ν := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
    have hf : MeasurePreserving (Prod.fst : A × (Fin n → A) → A)
        (ν.prod (Measure.pi (fun _ : Fin n => ν))) ν :=
      ⟨measurable_fst, by simp⟩
    exact hf.comp hp

theorem finite_product_independent (ν : Measure A) [IsProbabilityMeasure ν] (T : ℕ) :
    iIndepFun (fun i (ω : Fin T → A) => ω i) (Measure.pi (fun _ => ν)) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp only [(finite_product_coordinate ν _).map_eq]
  exact Measure.map_id

/-- A measurable function unaffected by changing one coordinate is independent of it. -/
theorem finite_product_fresh_independent (ν : Measure A) [IsProbabilityMeasure ν]
    (a₀ : A) {T : ℕ} (i : Fin T) (X : (Fin T → A) → B) (hX : Measurable X)
    (hcausal : ∀ ω u, X (Function.update ω i u) = X ω) :
    IndepFun X (fun ω => ω i) (Measure.pi (fun _ => ν)) := by
  classical
  cases T with
  | zero => exact Fin.elim0 i
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => A) i
    have hp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) i
    have hf : (Measure.pi (fun _ : Fin (n + 1) => ν)).map (fun ω => (e ω).1) = ν :=
      (finite_product_coordinate ν i).map_eq
    have hs : (Measure.pi (fun _ : Fin (n + 1) => ν)).map (fun ω => (e ω).2) =
        Measure.pi (fun _ : Fin n => ν) := by
      have h := congrArg (Measure.map (Prod.snd : A × (Fin n → A) → (Fin n → A))) hp.map_eq
      rw [Measure.map_map measurable_snd e.measurable] at h
      simpa only [Measure.map_snd_prod, measure_univ, one_smul, Function.comp_def] using h
    have hind : IndepFun (fun ω => (e ω).1) (fun ω => (e ω).2)
        (Measure.pi (fun _ : Fin (n + 1) => ν)) := by
      apply (indepFun_iff_map_prod_eq_prod_map_map e.measurable.fst.aemeasurable
        e.measurable.snd.aemeasurable).mpr
      rw [hf, hs]
      exact hp.map_eq
    let G : (Fin n → A) → B := fun v => X (e.symm (a₀, v))
    have hG : Measurable G := hX.comp (e.symm.measurable.comp
      (measurable_const.prodMk measurable_id))
    have hfactor : (fun ω => G (e ω).2) = X := by
      funext ω
      change X (i.insertNth a₀ (i.removeNth ω)) = X ω
      rw [Fin.insertNth_removeNth, hcausal]
    have h := hind.symm.comp hG measurable_id
    have heval : (fun ω => (e ω).1) = (fun ω : Fin (n+1) → A => ω i) := by
      funext ω
      rfl
    simpa only [Function.comp_def, id_eq, hfactor, heval] using h

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

def unitToFeasible (u : UnitDirection E) : Feasible E 1 := ⟨u.val, u.property.le⟩

theorem unitToFeasible_measurable : Measurable (unitToFeasible (E := E)) :=
  measurable_subtype_coe.subtype_mk

/-- Actual uniform sphere directions, represented in the policy's feasible seed type. -/
def sphereDirectionLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] : Measure (Feasible E 1) :=
  (unitSphereLaw E).map unitToFeasible

instance sphereDirectionLaw_probability : IsProbabilityMeasure (sphereDirectionLaw E) :=
  Measure.isProbabilityMeasure_map unitToFeasible_measurable.aemeasurable

theorem sphereDirectionLaw_unit : ∀ᵐ u ∂sphereDirectionLaw E, ‖u.val‖ = 1 := by
  rw [sphereDirectionLaw]
  apply (ae_map_iff unitToFeasible_measurable.aemeasurable
    (isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun u => u.property)

def extendDirectionSeed {T : ℕ} (ω : Fin T → Feasible E 1) : ℕ → Feasible E 1 :=
  fun n => if h : n < T then ω ⟨n, h⟩ else ⟨0, by simp⟩

theorem extendDirectionSeed_measurable (T : ℕ) :
    Measurable (extendDirectionSeed (E := E) (T := T)) := by
  apply measurable_pi_lambda
  intro n
  by_cases h : n < T
  · simpa only [extendDirectionSeed, dif_pos h] using
      (measurable_pi_apply (⟨n, h⟩ : Fin T) : Measurable (fun ω : Fin T → Feasible E 1 => ω ⟨n, h⟩))
  · simpa only [extendDirectionSeed, dif_neg h] using
      (measurable_const : Measurable (fun _ : Fin T → Feasible E 1 => (⟨0, by simp⟩ : Feasible E 1)))

def sphereSeedLaw (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (T : ℕ) :
    Measure (ℕ → Feasible E 1) :=
  (Measure.pi (fun _ : Fin T => sphereDirectionLaw E)).map extendDirectionSeed

instance sphereSeedLaw_probability (T : ℕ) : IsProbabilityMeasure (sphereSeedLaw E T) :=
  Measure.isProbabilityMeasure_map (extendDirectionSeed_measurable T).aemeasurable

theorem sphereSeedLaw_coordinate {T : ℕ} {t : ℕ} (ht : t < T) :
    MeasurePreserving (fun ω : ℕ → Feasible E 1 => ω t)
      (sphereSeedLaw E T) (sphereDirectionLaw E) := by
  refine ⟨measurable_pi_apply t, ?_⟩
  rw [sphereSeedLaw, Measure.map_map (measurable_pi_apply t) (extendDirectionSeed_measurable T)]
  simpa only [Function.comp_def, extendDirectionSeed, dif_pos ht] using
    (finite_product_coordinate (sphereDirectionLaw E) (⟨t, ht⟩ : Fin T)).map_eq

theorem sphereSeedLaw_unit {T t : ℕ} (ht : t < T) :
    ∀ᵐ ω ∂sphereSeedLaw E T, ‖(ω t).val‖ = 1 :=
  (sphereSeedLaw_coordinate ht).quasiMeasurePreserving.ae sphereDirectionLaw_unit

/-- The sampled direction is fresh relative to every measurable function of the past. -/
theorem sphereSeedLaw_fresh_independent {T t : ℕ} (ht : t < T)
    (X : (ℕ → Feasible E 1) → B) (hX : Measurable X)
    (hcausal : ∀ ω ω', (∀ j < t, ω j = ω' j) → X ω = X ω') :
    IndepFun X (fun ω => ω t) (sphereSeedLaw E T) := by
  classical
  let i : Fin T := ⟨t, ht⟩
  have h := finite_product_fresh_independent (sphereDirectionLaw E)
    (⟨0, by simp⟩ : Feasible E 1) i
    (fun ω => X (extendDirectionSeed ω)) (hX.comp (extendDirectionSeed_measurable T)) (by
      intro ω u
      apply hcausal
      intro j hj
      have hjT : j < T := hj.trans ht
      have hji : (⟨j, hjT⟩ : Fin T) ≠ i := by
        intro he
        have hv := congrArg Fin.val he
        dsimp [i] at hv
        omega
      simp only [extendDirectionSeed, dif_pos hjT, Function.update_of_ne hji])
  apply (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
    (measurable_pi_apply t).aemeasurable).mpr
  have heq := (indepFun_iff_map_prod_eq_prod_map_map
    (hX.comp (extendDirectionSeed_measurable T)).aemeasurable
    (measurable_pi_apply i).aemeasurable).mp h
  simp only [sphereSeedLaw, Measure.map_map (hX.prodMk (measurable_pi_apply t))
    (extendDirectionSeed_measurable T),
    Measure.map_map hX (extendDirectionSeed_measurable T),
    Measure.map_map (measurable_pi_apply t) (extendDirectionSeed_measurable T),
    Function.comp_def, extendDirectionSeed, dif_pos ht] at *
  exact heq

theorem sphereDirectionLaw_second_moment (v : E) :
    (∫ u, ⟪v, u.val⟫_ℝ ^ 2 ∂sphereDirectionLaw E) =
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hm : Measurable (fun u : Feasible E 1 => ⟪v, u.val⟫_ℝ ^ 2) := by fun_prop
  rw [sphereDirectionLaw, integral_map_of_stronglyMeasurable
    unitToFeasible_measurable hm.stronglyMeasurable]
  exact unitSphereLaw_second_moment v

theorem sphereSeedLaw_second_moment {T t : ℕ} (ht : t < T) (v : E) :
    (∫ ω, ⟪v, (ω t).val⟫_ℝ ^ 2 ∂sphereSeedLaw E T) =
      ‖v‖ ^ 2 / (Module.finrank ℝ E : ℝ) := by
  have hm : Measurable (fun u : Feasible E 1 => ⟪v, u.val⟫_ℝ ^ 2) := by fun_prop
  have h := integral_map_of_stronglyMeasurable (μ := sphereSeedLaw E T)
    (show Measurable (fun ω : ℕ → Feasible E 1 => ω t) from measurable_pi_apply t)
    hm.stronglyMeasurable
  rw [(sphereSeedLaw_coordinate ht).map_eq] at h
  exact h.symm.trans (sphereDirectionLaw_second_moment v)

end
end Nonsmooth
