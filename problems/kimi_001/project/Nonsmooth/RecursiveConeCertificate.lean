import Nonsmooth.ConeLiftCoefficient
import Nonsmooth.TwoQueryOutwardCone

open Set
open scoped InnerProductSpace
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem comparisonConeExcluded_of_positive_ray {G : Set E} {f : E → ℝ} {x e : E} {B : ℝ}
    (he : ‖e‖ = 1) (hray : ∀ h : ℝ, 0 ≤ h → x + h • e ∈ G → B ≤ f (x + h • e)) :
    comparisonConeExcluded G f (ℝ ∙ e) x e 0 B := by
  intro v hv hvG hslope
  obtain ⟨h, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hh : 0 ≤ h := by
    simpa only [zero_mul, real_inner_smul_left, real_inner_self_eq_norm_sq, he,
      one_pow, mul_one] using hslope
  exact hray h hh hvG

theorem symmetric_queries_positive_ray {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) (x e n : E) {a b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h)
    (hminusG : x - b • e - a • n ∈ G) (hplusG : x - b • e + a • n ∈ G)
    (hminus : f (x - b • e - a • n) ≤ f x) (hplus : f (x - b • e + a • n) ≤ f x)
    (hzG : x + h • e ∈ G) : f x ≤ f (x + h • e) := by
  let q : Fin 2 → E := ![x - b • e - a • n, x - b • e + a • n]
  let c : ℝ := h / (2 * b)
  have hc : 0 ≤ c := div_nonneg hh (by positivity)
  have hcb : c * b + c * b = h := by dsimp [c]; field_simp; ring
  have heq : x + c • (x - q 0) + c • (x - q 1) = x + h • e := by
    calc
      _ = x + (c * b + c * b) • e := by dsimp [q]; module
      _ = _ := by rw [hcb]
  have hqG : ∀ i, q i ∈ G := by intro i; fin_cases i <;> assumption
  have hqf : ∀ i, f (q i) ≤ f x := by intro i; fin_cases i <;> assumption
  have hfz := two_query_outward_cone_value_ge hf q hqG x hqf hc hc
    (by simpa only [heq] using hzG)
  simpa only [heq] using hfz

/-- A finite flag of sections and actual comparison pairs propagates the exclusion certificate. -/
theorem comparisonConeExcluded_iterate {G : Set E} {f : E → ℝ} (hf : ConvexOn ℝ G f)
    (K : ℕ → Submodule ℝ E) (x e : E) (w n : ℕ → E) (a : ℕ → ℝ) {B ε : ℝ} (D : ℕ)
    (he : ‖e‖ = 1)
    (hflag : ∀ i < D, K i = K (i + 1) ⊓ (ℝ ∙ n i)ᗮ)
    (hnK : ∀ i < D, n i ∈ K (i + 1)) (hn : ∀ i < D, ‖n i‖ = 1)
    (heK : ∀ i < D, e ∈ K i) (hwK : ∀ i < D, w i ∈ K i)
    (ha : ∀ i < D, 0 < a i) (hw : ∀ i < D, ‖w i‖ ≤ a i * ε)
    (hminusG : ∀ i < D, x + w i - a i • n i ∈ G)
    (hplusG : ∀ i < D, x + w i + a i • n i ∈ G)
    (hminusB : ∀ i < D, f (x + w i - a i • n i) ≤ B)
    (hplusB : ∀ i < D, f (x + w i + a i • n i) ≤ B)
    (hbase : comparisonConeExcluded G f (K 0) x e 0 B) :
    comparisonConeExcluded G f (K D) x e (coneLiftCoefficient ε D) B := by
  have hstep (m : ℕ) (hm : m ≤ D) :
      comparisonConeExcluded G f (K m) x e (coneLiftCoefficient ε m) B := by
    induction m with
    | zero => exact hbase
    | succ m ih =>
      have hmD : m < D := by omega
      have hi := ih (by omega)
      have heH : e ∈ K (m + 1) ⊓ (ℝ ∙ n m)ᗮ := by rw [← hflag m hmD]; exact heK m hmD
      have hwH : w m ∈ K (m + 1) ⊓ (ℝ ∙ n m)ᗮ := by rw [← hflag m hmD]; exact hwK m hmD
      rw [hflag m hmD] at hi
      exact comparisonConeExcluded_lift hf (K (m + 1)) x (w m) (n m) e
        (hnK m hmD) (hn m hmD) he heH hwH (coneLiftCoefficient_nonneg ε m)
        (ha m hmD) (hw m hmD) (hminusG m hmD) (hplusG m hmD)
        (hminusB m hmD) (hplusB m hmD) hi
  exact hstep D le_rfl

theorem comparisonConeExcluded_dimension_scale {G : Set E} {f : E → ℝ}
    {K : Submodule ℝ E} {x e : E} {B : ℝ} (D : ℕ) (hD : 0 < D) (m : ℕ) (hm : m ≤ D)
    (hcone : comparisonConeExcluded G f K x e (coneLiftCoefficient (1 / (8 * (D : ℝ) ^ 2)) m) B) :
    comparisonConeExcluded G f K x e (1 / (4 * (D : ℝ))) B :=
  comparisonConeExcluded_mono_coefficient hcone (coneLiftCoefficient_dimension_scale D hD m hm)

end
end Nonsmooth
