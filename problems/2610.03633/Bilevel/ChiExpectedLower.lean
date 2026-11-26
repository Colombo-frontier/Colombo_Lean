import Bilevel.MultiscaleExpectedQueries
import Mathlib.MeasureTheory.Function.Floor

/-! A fixed-horizon barrier implies an expected original-call lower bound.
The actual stopped/capped output agreement and the probability certificate
remain explicit. Natural-valued counts handle the zero-query case too. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace Bilevel.ChiExpectedLower

variable {Ω X : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]

theorem expected_cost_of_capped_barrier
    (N : Ω → ℕ) (stopped capped : Ω → X) (loss : X → ℝ)
    (hnint : Integrable (fun ω => (N ω : ℝ)) ν)
    (hlint : Integrable (fun ω => loss (stopped ω)) ν) (hlpos : ∀ x,0≤loss x)
    (n : ℕ) (ε : ℝ) (hε : 0<ε)
    (good : Set Ω) (hgood : MeasurableSet good) (hprob : (13:ℝ)/16≤ν.real good)
    (hagreement : ∀ᵐ ω ∂ν,N ω≤n → stopped ω=capped ω)
    (hbarrier : ∀ᵐ ω ∂ν,ω∈good → 8*ε≤loss (capped ω))
    (haccuracy : (∫ ω,loss (stopped ω) ∂ν)≤ε) :
    11*((n:ℝ)+1)/16≤∫ ω,(N ω:ℝ) ∂ν := by
  have hcap : 0<(n:ℝ)+1 := by positivity
  let a := 8*ε/((n:ℝ)+1)
  have ha : 0≤a := by dsimp [a]; positivity
  have haug : ∀ᵐ ω ∂ν,ω∈good → 8*ε≤loss (stopped ω)+a*(N ω:ℝ) := by
    filter_upwards [hagreement,hbarrier] with ω hag hbar
    intro hg
    by_cases hn : N ω≤n
    · have hl := hbar hg
      rw [← hag hn] at hl
      exact hl.trans (le_add_of_nonneg_right (mul_nonneg ha (Nat.cast_nonneg _)))
    · have hnc : (n:ℝ)+1≤(N ω:ℝ) := by exact_mod_cast (show n+1≤N ω by omega)
      have hm := mul_le_mul_of_nonneg_left hnc ha
      have he : a*((n:ℝ)+1)=8*ε := by dsimp [a]; field_simp
      rw [he] at hm
      linarith only [hm,hlpos (stopped ω)]
  have hle : good.indicator (fun _ => 8*ε)≤ᵐ[ν] (fun ω => loss (stopped ω)+a*(N ω:ℝ)) := by
    filter_upwards [haug] with ω hω
    by_cases hg : ω∈good
    · rw [Set.indicator_of_mem hg]
      exact hω hg
    · rw [Set.indicator_of_not_mem hg]
      exact add_nonneg (hlpos _) (mul_nonneg ha (Nat.cast_nonneg _))
  have hi := integral_mono_ae ((integrable_const (8*ε)).indicator hgood)
    (hlint.add (hnint.const_mul a)) hle
  simp only [Pi.add_apply] at hi
  rw [integral_indicator_const _ hgood,integral_add hlint (hnint.const_mul a),integral_const_mul] at hi
  simp only [smul_eq_mul] at hi
  have hp := mul_le_mul_of_nonneg_right hprob (show 0≤8*ε by positivity)
  have hr : 13*ε/2≤ε+a*(∫ ω,(N ω:ℝ) ∂ν) := by nlinarith only [hi,hp,haccuracy]
  have hm := mul_le_mul_of_nonneg_right hr hcap.le
  have he : (ε+a*(∫ ω,(N ω:ℝ) ∂ν))*((n:ℝ)+1)=
      ε*((n:ℝ)+1)+8*ε*(∫ ω,(N ω:ℝ) ∂ν) := by dsimp [a]; field_simp
  rw [he] at hm
  nlinarith only [hm,hε]

theorem expected_cost_of_fixed_horizons
    (N : Ω → ℕ) (stopped : Ω → X) (capped : ℕ → Ω → X) (loss : X → ℝ)
    (hnint : Integrable (fun ω => (N ω : ℝ)) ν)
    (hlint : Integrable (fun ω => loss (stopped ω)) ν) (hlpos : ∀ x,0≤loss x)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε)
    (hagreement : ∀ n,∀ᵐ ω ∂ν,N ω≤n → stopped ω=capped n ω)
    (hfixed : ∀ n : ℕ,(n:ℝ)≤R/16 → ∃ good : Set Ω,MeasurableSet good ∧
      (13:ℝ)/16≤ν.real good ∧ (∀ᵐ ω ∂ν,ω∈good → 8*ε≤loss (capped n ω)))
    (haccuracy : (∫ ω,loss (stopped ω) ∂ν)≤ε) :
    R/256≤∫ ω,(N ω:ℝ) ∂ν := by
  let n : ℕ := ⌊R/16⌋₊
  have hn : (n:ℝ)≤R/16 := Nat.floor_le (by positivity)
  obtain ⟨good,hgood,hprob,hbarrier⟩ := hfixed n hn
  have hh := expected_cost_of_capped_barrier ν N stopped (capped n) loss hnint hlint hlpos n ε hε
    good hgood hprob (hagreement n) hbarrier haccuracy
  have hfloor : R/16<(n:ℝ)+1 := Nat.lt_floor_add_one _
  linarith only [hh,hfloor,hR]

theorem expected_cost_of_fixed_horizons_extended
    (N : Ω → ℕ) (stopped : Ω → X) (capped : ℕ → Ω → X) (loss : X → ℝ)
    (hN : Measurable N) (hlint : Integrable (fun ω => loss (stopped ω)) ν) (hlpos : ∀ x,0≤loss x)
    (R ε : ℝ) (hR : 0≤R) (hε : 0<ε)
    (hagreement : ∀ n,∀ᵐ ω ∂ν,N ω≤n → stopped ω=capped n ω)
    (hfixed : ∀ n : ℕ,(n:ℝ)≤R/16 → ∃ good : Set Ω,MeasurableSet good ∧
      (13:ℝ)/16≤ν.real good ∧ (∀ᵐ ω ∂ν,ω∈good → 8*ε≤loss (capped n ω)))
    (haccuracy : (∫ ω,loss (stopped ω) ∂ν)≤ε) :
    ENNReal.ofReal (R/256)≤∫⁻ ω,(N ω:ENNReal) ∂ν := by
  by_cases hinf : (∫⁻ ω,(N ω:ENNReal) ∂ν)=∞
  · rw [hinf]
    exact le_top
  have hnint : Integrable (fun ω => (N ω:ℝ)) ν := by
    have hm : Measurable (fun ω => (N ω:ℝ)) := (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hN
    refine ⟨hm.aestronglyMeasurable,?_⟩
    have hf := lt_top_iff_ne_top.mpr hinf
    simpa only [HasFiniteIntegral,Real.enorm_of_nonneg (Nat.cast_nonneg _),ENNReal.ofReal_natCast] using hf
  have hh := expected_cost_of_fixed_horizons ν N stopped capped loss hnint hlint hlpos R ε hR hε hagreement hfixed haccuracy
  have he := ofReal_integral_eq_lintegral_ofReal hnint (Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg (N ω)))
  simp only [ENNReal.ofReal_natCast] at he
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq he

end Bilevel.ChiExpectedLower
