import Nonsmooth.FrameStep

open MeasureTheory Function
open scoped ENNReal InnerProductSpace Topology
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace Nonsmooth
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]

/-- Exactly the scalar responses of a finite adaptive linear-query protocol. -/
def adaptiveLinearInformation (q : ℕ → E → E) : ℕ → MeasurableSpace E
  | 0 => ⊥
  | n + 1 => adaptiveLinearInformation q n ⊔
      MeasurableSpace.comap (fun x => ⟪q n x, x⟫_ℝ) inferInstance

theorem adaptiveLinearInformation_le (q : ℕ → E → E) (T : ℕ)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n)) :
    adaptiveLinearInformation q T ≤ mE := by
  induction T with
  | zero => exact bot_le
  | succ T ih =>
    have hm := ih (fun n hn => hq n (Nat.lt.step hn))
    apply sup_le hm
    exact measurable_iff_comap_le.mp ((continuous_fst.inner continuous_snd).measurable.comp
      (((hq T (Nat.lt_succ_self T)).mono hm le_rfl).prodMk measurable_id))

/-- A frame is constructed recursively from the actual measurable query directions. No
countability, independence, or posterior-energy premise is assumed. -/
theorem adaptive_linear_frame (q : ℕ → E → E) (T : ℕ) (hT : T ≤ Module.finrank ℝ E)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n)) :
    ∃ (K : Submodule ℝ E) (F : SphericalFrame K),
      Module.finrank ℝ K = T ∧ adaptiveLinearInformation q T ≤ frameInformation F := by
  induction T with
  | zero =>
    exact ⟨⊥, initialSphericalFrame, finrank_bot ℝ E, bot_le⟩
  | succ T ih =>
    obtain ⟨K, F, hdim, hinfo⟩ := ih (Nat.le_trans (Nat.le_succ T) hT)
      (fun n hn => hq n (Nat.lt.step hn))
    have hr : 0 < Module.finrank ℝ Kᗮ := by
      have hh := K.finrank_add_finrank_orthogonal
      omega
    have hq' : @Measurable E E (frameInformation F) mE (q T) :=
      (hq T (Nat.lt_succ_self T)).mono hinfo le_rfl
    obtain ⟨L, G, hdim', hinfo'⟩ := spherical_frame_one_query F hr (q T) hq'
    refine ⟨L, G, by omega, ?_⟩
    exact (sup_le_sup hinfo le_rfl).trans hinfo'

theorem spherical_adaptive_linear_energy (q : ℕ → E → E) (T : ℕ)
    (hT : T ≤ Module.finrank ℝ E)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n)) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | adaptiveLinearInformation q T]) x‖ ^ 2
      ∂sphericalLaw E) ≤ (T : ℝ) / (Module.finrank ℝ E : ℝ) := by
  obtain ⟨K, F, hdim, hinfo⟩ := adaptive_linear_frame q T hT hq
  have h := spherical_frame_subinformation_energy F hinfo
  rwa [hdim] at h

/-- The unrestricted adaptive posterior-energy bound for any finite number of scalar queries,
including zero, redundant, nonunit, and continuously varying query directions. -/
theorem spherical_adaptive_linear_energy_min (q : ℕ → E → E) (T : ℕ)
    (hq : ∀ n < T, @Measurable E E (adaptiveLinearInformation q n) mE (q n)) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | adaptiveLinearInformation q T]) x‖ ^ 2
      ∂sphericalLaw E) ≤ min ((T : ℝ) / (Module.finrank ℝ E : ℝ)) 1 := by
  have hm := adaptiveLinearInformation_le q T hq
  have hV : MemLp (fun x : E => x) 2 (sphericalLaw E) :=
    MemLp.of_bound measurable_id.aestronglyMeasurable 1
      (sphericalLaw_unit.mono (fun _ h => h.le))
  have hunit : (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | adaptiveLinearInformation q T]) x‖ ^ 2
      ∂sphericalLaw E) ≤ 1 := by
    have h := condExp_second_moment_le hm hV
    have he : (∫ x : E, ‖x‖ ^ 2 ∂sphericalLaw E) = 1 := by
      calc
        _ = ∫ _ : E, (1 : ℝ) ∂sphericalLaw E := by
          apply integral_congr_ae
          filter_upwards [sphericalLaw_unit (E := E)] with x hx
          simp only [hx, one_pow]
        _ = _ := by simp
    rwa [he] at h
  by_cases hT : T ≤ Module.finrank ℝ E
  · exact le_min (spherical_adaptive_linear_energy q T hT hq) hunit
  · have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    have hdt : (Module.finrank ℝ E : ℝ) ≤ T := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hT))
    exact le_min (hunit.trans ((one_le_div hd).mpr hdt)) hunit


end
end Nonsmooth
