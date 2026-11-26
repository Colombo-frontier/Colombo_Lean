import ExactValue.SCQuadratic

open scoped ENNReal
set_option autoImplicit false
namespace ExactValue
noncomputable section

def scLowerScale (d : ℕ) (μ β R ε : ℝ) : ℝ :=
  min (min (Real.sqrt (β * R ^ 2 / ε)) (Real.sqrt (β / μ))) (dimensionScale d)

theorem scScale_floor {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hM : 1024 ≤ scLowerScale d μ β R ε) :
    let M := scLowerScale d μ β R ε
    let m := ⌊M / 512⌋₊
    0 < m ∧ 4 * m ≤ d ∧ M / 1024 ≤ (m : ℝ) ∧ (m : ℝ) ≤ M / 512 ∧
      (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d := by
  dsimp only
  let M := scLowerScale d μ β R ε
  let m := ⌊M / 512⌋₊
  have hm : 0 < m := Nat.floor_pos.mpr (by change 1 ≤ M / 512; change 1024 ≤ M at hM; linarith)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmf : (m : ℝ) ≤ M / 512 := Nat.floor_le (by change 1024 ≤ M at hM; linarith)
  have hround : M / 1024 ≤ (m : ℝ) := by
    have hlt := Nat.lt_floor_add_one (M / 512)
    change M / 512 < (m : ℝ) + 1 at hlt
    change 1024 ≤ M at hM
    linarith
  have hMD : M ≤ dimensionScale d := min_le_right _ _
  have hd1 : 1 ≤ d := by omega
  have hDd := dimensionScale_le_dimension hd1
  have hmd : 4 * m ≤ d := by
    have hh : (4 : ℝ) * m ≤ d := by linarith
    exact_mod_cast hh
  have hlog : 0 < 1 + Real.log (d : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ d by exact_mod_cast hd1)
    linarith
  have hcubic : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d := by
    have hp : (m : ℝ) ^ 3 ≤ (dimensionScale d / 512) ^ 3 :=
      pow_le_pow_left₀ hmpos.le (by linarith) 3
    have hh := mul_le_mul_of_nonneg_right hp hlog.le
    have heq := dimensionScale_cube_mul hd1
    have hdn : (0 : ℝ) ≤ d := by positivity
    nlinarith
  exact ⟨hm, hmd, hround, hmf, hcubic⟩

theorem sc_auxiliary_smoothness {m d : ℕ} {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hm : (m : ℝ) ≤ scLowerScale d μ β R ε / 512) :
    4096 * max μ (64 * ε / R ^ 2) * (m : ℝ) ^ 2 ≤ β := by
  have hβ : 0 < β := hμ.trans_le hμβ
  have hMq : scLowerScale d μ β R ε ≤ Real.sqrt (β * R ^ 2 / ε) :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hMk : scLowerScale d μ β R ε ≤ Real.sqrt (β / μ) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hk : (m : ℝ) ^ 2 ≤ (Real.sqrt (β / μ) / 512) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hq : (m : ℝ) ^ 2 ≤ (Real.sqrt (β * R ^ 2 / ε) / 512) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hks := Real.sq_sqrt (show 0 ≤ β / μ by positivity)
  have hqs := Real.sq_sqrt (show 0 ≤ β * R ^ 2 / ε by positivity)
  have hkm := mul_le_mul_of_nonneg_right hk hμ.le
  have hqm := mul_le_mul_of_nonneg_right hq hε.le
  have hkc := div_mul_cancel₀ β hμ.ne'
  have hqc := div_mul_cancel₀ (β * R ^ 2) hε.ne'
  have hkμ : 4096 * μ * (m : ℝ) ^ 2 ≤ β := by
    nlinarith [congrArg (fun v : ℝ => v * μ) hks]
  have hqε : 262144 * ε * (m : ℝ) ^ 2 ≤ β * R ^ 2 := by
    nlinarith [congrArg (fun v : ℝ => v * ε) hqs]
  rcases le_total μ (64 * ε / R ^ 2) with hle | hle
  · rw [max_eq_right hle]
    have heq : 4096 * (64 * ε / R ^ 2) * (m : ℝ) ^ 2 =
        (262144 * ε * (m : ℝ) ^ 2) / R ^ 2 := by ring
    rw [heq]
    exact (div_le_iff₀ (sq_pos_of_pos hR)).mpr hqε
  · simpa only [max_eq_left hle] using hkμ

theorem sc_calibrated_failure {d m T : ℕ} (hd : 8 ≤ d) (hm : 0 < m)
    (hmd : 4 * m ≤ d) (hT : 8 * T < d * m) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hscale : (m : ℝ) ^ 3 * (1 + Real.log (d : ℝ)) ≤ (1 / 16777216 : ℝ) * d)
    (hmM : (m : ℝ) ≤ scLowerScale d μ β R ε / 512)
    (A : ValueAlgorithm d R T) : ¬ A.SCGuarantees (μ := μ) (β := β) (ε := ε) := by
  let lam := max μ (64 * ε / R ^ 2)
  let β₀ := 4096 * lam * (m : ℝ) ^ 2
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlam : 0 < lam := hμ.trans_le (le_max_left _ _)
  have hβ₀ : 0 < β₀ := by dsimp [β₀]; positivity
  have hβ₀β : β₀ ≤ β := sc_auxiliary_smoothness hμ hμβ hR hε hmM
  have hmod : β₀ / (4096 * (m : ℝ) ^ 2) = lam := by dsimp [β₀]; field_simp; ring
  obtain ⟨f, hf, hs, _, x, hx, hbad⟩ :=
    algorithm_integer_lower_bound_with_modulus hd hm hmd hT hβ₀ hR hscale A
  rw [hmod] at hs
  have hsc : SCObjective d μ β R f := ⟨hf.smooth_mono hβ₀β, hs.mono (le_max_left _ _)⟩
  have hgap : 11 / 131072 * (β₀ * R ^ 2 / (m : ℝ) ^ 2) = 11 / 32 * lam * R ^ 2 := by
    dsimp [β₀]
    field_simp
    ring
  rw [hgap] at hbad
  have he : 64 * ε ≤ lam * R ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hR)).mp (le_max_right μ (64 * ε / R ^ 2))
  intro hA
  obtain ⟨z, hz, hgood⟩ := hA f hsc
  have := hx z
  have := hz x
  nlinarith

/-- Fixed public parameters, all accuracy scales; explicit constants c=1/8192, cε=1/64, d₀=8. -/
theorem sc_fixed_parameter_lower {d : ℕ} (hd : 8 ≤ d) {μ β R ε : ℝ}
    (hμ : 0 < μ) (hμβ : μ ≤ β) (hR : 0 < R) (hε : 0 < ε)
    (hεmax : ε ≤ β * R ^ 2 / 64) :
    ENNReal.ofReal ((1 / 8192 : ℝ) * d * scLowerScale d μ β R ε) ≤
      scValueComplexity d R μ β ε := by
  by_cases hM : 1024 ≤ scLowerScale d μ β R ε
  · obtain ⟨hm, hmd, hround, hmf, hscale⟩ := scScale_floor hd hM
    apply sc_lower_of_failure
    intro T hT A
    have hbudget : 8 * T < d * ⌊scLowerScale d μ β R ε / 512⌋₊ := by
      have hmul := mul_le_mul_of_nonneg_left hround (show (0 : ℝ) ≤ d by positivity)
      have hreal : (8 : ℝ) * T < (d : ℝ) * ⌊scLowerScale d μ β R ε / 512⌋₊ := by nlinarith
      exact_mod_cast hreal
    exact sc_calibrated_failure hd hm hmd hbudget hμ hμβ hR hε hscale hmf A
  · apply (ENNReal.ofReal_le_ofReal (show (1 / 8192 : ℝ) * d * scLowerScale d μ β R ε ≤
        (d : ℝ) - 1 from ?_)).trans (sc_quadratic_lower (by omega) hμ hμβ hR hε hεmax)
    have hd' : (8 : ℝ) ≤ d := by exact_mod_cast hd
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hM))
      (show 0 ≤ (d : ℝ) by positivity)
    nlinarith

theorem sc_main_lower_rate :
    ∃ c cε : ℝ, ∃ d₀ : ℕ, 0 < c ∧ 0 < cε ∧
      ∀ (d : ℕ), d₀ ≤ d → ∀ μ β R ε : ℝ, 0 < μ → μ ≤ β → 0 < R → 0 < ε →
        ε ≤ cε * β * R ^ 2 →
        ENNReal.ofReal (c * d * scLowerScale d μ β R ε) ≤ scValueComplexity d R μ β ε := by
  refine ⟨1 / 8192, 1 / 64, 8, by norm_num, by norm_num, ?_⟩
  intro d hd μ β R ε hμ hμβ hR hε hmax
  apply sc_fixed_parameter_lower hd hμ hμβ hR hε
  linarith

end
end ExactValue
