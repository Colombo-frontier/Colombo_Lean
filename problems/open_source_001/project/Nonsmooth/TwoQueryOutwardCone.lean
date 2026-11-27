import Nonsmooth.FiniteComparisonCone
import Mathlib.Tactic.Module

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [AddCommGroup E] [Module ℝ E]

theorem two_query_outward_cone_mem (v : Fin 2 → E) (x : E) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    x + a • (x - v 0) + b • (x - v 1) ∈ finiteComparisonCone v x := by
  have hp0 : v 0 ∈ convexHull ℝ (range v) := subset_convexHull ℝ _ ⟨0, rfl⟩
  have hp1 : v 1 ∈ convexHull ℝ (range v) := subset_convexHull ℝ _ ⟨1, rfl⟩
  by_cases hs : a + b = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    rw [ha0, hb0]
    simp only [zero_smul, add_zero]
    exact ⟨v 0, hp0, 1, zero_lt_one, le_rfl, by simp⟩
  · let s := a + b
    have hspos : 0 < s := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hs)
    have hden : 0 < 1 + s := by linarith
    let p := (a / s) • v 0 + (b / s) • v 1
    let t : ℝ := 1 / (1 + s)
    let z := x + a • (x - v 0) + b • (x - v 1)
    have hp : p ∈ convexHull ℝ (range v) := by
      apply (convex_convexHull ℝ (range v)) hp0 hp1 (div_nonneg ha hspos.le) (div_nonneg hb hspos.le)
      dsimp [s]
      field_simp
    have htpos : 0 < t := one_div_pos.mpr hden
    have htone : t ≤ 1 := (div_le_one hden).mpr (by linarith)
    have htc : t * (1 + s) = 1 := by dsimp [t]; field_simp
    have hca : (1 - t) * (a / s) = t * a := by
      dsimp [t]
      field_simp [ne_of_gt hspos, ne_of_gt hden]
      ring
    have hcb : (1 - t) * (b / s) = t * b := by
      dsimp [t]
      field_simp [ne_of_gt hspos, ne_of_gt hden]
      ring
    have hz : z + a • v 0 + b • v 1 = (1 + s) • x := by
      dsimp [z, s]
      module
    refine ⟨p, hp, t, htpos, htone, ?_⟩
    calc
      x = t • ((1 + s) • x) := by rw [smul_smul, htc, one_smul]
      _ = t • (z + a • v 0 + b • v 1) := by rw [hz]
      _ = (1 - t) • p + t • z := by
        dsimp only [p]
        simp only [smul_add, smul_smul, hca, hcb]
        module

theorem two_query_outward_cone_value_ge {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) (v : Fin 2 → E) (hv : ∀ i, v i ∈ G) (x : E)
    (hval : ∀ i, f (v i) ≤ f x) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : x + a • (x - v 0) + b • (x - v 1) ∈ G) :
    f x ≤ f (x + a • (x - v 0) + b • (x - v 1)) :=
  finiteComparisonCone_value_ge hf v hv hval hz (two_query_outward_cone_mem v x ha hb)

end
end Nonsmooth
