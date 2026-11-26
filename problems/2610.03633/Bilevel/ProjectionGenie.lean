import Bilevel.RawGenieTheorem
import Bilevel.RawGenieMeasurable
import Bilevel.GenieDimension

/-! The adaptive projection genie for Borel query rules, including independent private randomness. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.ProjectionGenie
open EuclideanGaussian ProjectionPosterior ProjectionEnergy GenieProtocol RawGenieProtocol

theorem randomized_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (d T M R n : ℕ) (hT : T ≤ d)
    (P : Ω → RawGenieProtocol.Protocol d T M R) (hP : RawGenieProtocol.MeasurableFamily P)
    (b : ℝ) (hb : 0 < b) (hb2 : b ≤ 2) (hd : M+R+(n+1) ≤ d)
    (hcap : (R : ℝ)*((M : ℝ)*b) ≤ 1/2) :
    (ν.prod (HaarFrame.frameLaw d T hT))
      {p | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*b) R) (P p.1) ⊥ ∅ p.2} ≤
      (M : ℝ≥0∞)*failurePerQuery T n b := by
  let Q := fun ω => normalize (P ω) ⊥ 0
  have hQ : GenieProtocol.MeasurableFamily Q := by
    have h := hP.normalized.comap (fun ω => (ω,(ProjectionStore.ofSubspace d ⊥,(0 : Frame d T))))
      (measurable_id.prodMk (measurable_const.prodMk measurable_const))
    simpa only [stored_eq_normalize] using h
  have hbad : (ν.prod (HaarFrame.frameLaw d T hT)) {p | bad b (Q p.1) p.2} ≤
      (M : ℝ≥0∞)*failurePerQuery T n b := by
    rw [Measure.prod_apply (hQ.joint_bad b)]
    calc
      _ ≤ ∫⁻ _ω, (M : ℝ≥0∞)*failurePerQuery T n b ∂ν := by
        apply lintegral_mono
        intro ω
        exact haar_failure_bound d T M R n hT (Q ω) b hb hb2 hd (hQ.regular b ω)
          (normalized_valid (P ω) ⊥ 0)
      _ = _ := by simp
  have hU : ∀ᵐ p ∂ν.prod (HaarFrame.frameLaw d T hT), Orthonormal ℝ p.2 :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd (ProjectionConcentration.orthonormal_measurable d T))).2
      (Filter.Eventually.of_forall (fun _ => ProjectionConcentration.haar_orthonormal_ae d T hT))
  have hsub : {p : Ω × Frame d T | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*b) R) (P p.1) ⊥ ∅ p.2}
      ≤ᵐ[ν.prod (HaarFrame.frameLaw d T hT)] {p | bad b (Q p.1) p.2} := by
    filter_upwards [hU] with p hp
    intro hunsafe
    by_contra hgood
    apply hunsafe
    have hs := initial_safe b hb.le (by linarith) (Q p.1) (normalized_valid (P p.1) ⊥ 0) p.2 hp hgood
    have hz : projections d T ⊥ p.2 = 0 := by funext i; simp [projections,ProjectionGeometry.project]
    have he := safe_normalize_iff (P p.1) (envelope ((M : ℝ)*b) R) ⊥ ∅ p.2 hp
    rw [hz] at he
    exact he.mp hs
  exact (measure_mono_ae hsub).trans hbad

theorem logarithmic_adaptive_energy {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (d T M n : ℕ) (hT : T ≤ d)
    (hMpos : 0 < M) (hTpos : 0 < T) (hnpos : 0 < n)
    (P : Ω → RawGenieProtocol.Protocol d T M T) (hP : RawGenieProtocol.MeasurableFamily P)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hd : M+T+(n+1) ≤ d)
    (hcap : (T : ℝ)*((M : ℝ)*logarithmicIncrement M T n δ) ≤ 1/2) :
    (ν.prod (HaarFrame.frameLaw d T hT)).real
      {p | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*logarithmicIncrement M T n δ) T) (P p.1) ⊥ ∅ p.2} ≤ δ/2 := by
  let b := logarithmicIncrement M T n δ
  have hb : 0 < b := logarithmic_increment_pos M T n hMpos hTpos hnpos δ hδ hδ1
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
  have ht : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hp : 1 ≤ (T : ℝ)*M := by nlinarith
  have hb2 : b ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_right hp hb.le
    change (T : ℝ)*((M : ℝ)*b) ≤ 1/2 at hcap
    nlinarith
  have h := randomized_energy_bound ν d T M T n hT P hP b hb hb2 hd hcap
  have hc : 0 ≤ (T : ℝ)*(2*Real.exp (-(n : ℝ)*b/8)) := by positivity
  have hf : (M : ℝ≥0∞)*failurePerQuery T n b ≠ ⊤ := by unfold failurePerQuery; finiteness
  have hreal := ENNReal.toReal_mono hf h
  simp only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_natCast,failurePerQuery,
    ENNReal.toReal_ofReal hc] at hreal
  rw [logarithmic_failure_identity M T n hMpos hTpos hnpos δ hδ] at hreal
  exact hreal

theorem source_adaptive_energy {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (d T M : ℕ)
    (hMpos : 0 < M) (hTpos : 0 < T) (hlarge : M+T+2 < d)
    (P : Ω → RawGenieProtocol.Protocol d T M T) (hP : RawGenieProtocol.MeasurableFamily P)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hcap : (T : ℝ)*((M : ℝ)*(8*Real.log (4*(M : ℝ)*T/δ)/((d : ℝ)-M-T-2))) ≤ 1/2) :
    let b := 8*Real.log (4*(M : ℝ)*T/δ)/((d : ℝ)-M-T-2)
    (ν.prod (HaarFrame.frameLaw d T (by omega))).real
      {p | ¬ RawGenieProtocol.Safe (envelope ((M : ℝ)*b) T) (P p.1) ⊥ ∅ p.2} ≤ δ/2 ∧
      envelope ((M : ℝ)*b) T ≤ 2*(M : ℝ)*b := by
  let n := d-(M+T+2)
  have hn : 0 < n := by dsimp [n]; omega
  have hncast : (n : ℝ) = (d : ℝ)-M-T-2 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega : M+T+2 ≤ d)]
    push_cast
    ring
  have he : logarithmicIncrement M T n δ = 8*Real.log (4*(M : ℝ)*T/δ)/((d : ℝ)-M-T-2) := by
    simp only [logarithmicIncrement,hncast]
  have hb := logarithmic_increment_pos M T n hMpos hTpos hn δ hδ hδ1
  rw [he] at hb
  constructor
  · have h := logarithmic_adaptive_energy ν d T M n (by omega) hMpos hTpos hn P hP δ hδ hδ1
      (by dsimp [n]; omega) (by rwa [he])
    simpa only [he] using h
  · exact envelope_twice M T _ hb.le hcap

end Bilevel.ProjectionGenie
