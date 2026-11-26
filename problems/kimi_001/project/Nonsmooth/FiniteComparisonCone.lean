import Nonsmooth.ProtasovTransfer
import Mathlib.Analysis.Convex.Hull

open Set
set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [AddCommGroup E] [Module ℝ E]

/-- The outward cone justified by comparing an apex with finitely many values. -/
def finiteComparisonCone {m : ℕ} (v : Fin m → E) (x : E) : Set E :=
  {z | ∃ p ∈ convexHull ℝ (range v), ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    x = (1 - t) • p + t • z}

theorem convex_value_le_on_query_hull {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) {m : ℕ} (v : Fin m → E)
    (hv : ∀ i, v i ∈ G) {B : ℝ} (hb : ∀ i, f (v i) ≤ B) :
    ∀ p ∈ convexHull ℝ (range v), p ∈ G ∧ f p ≤ B := by
  apply convexHull_min _ (hf.convex_le B)
  rintro p ⟨i, rfl⟩
  exact ⟨hv i, hb i⟩

theorem finiteComparisonCone_value_ge {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) {m : ℕ} (v : Fin m → E)
    (hv : ∀ i, v i ∈ G) {x z : E} (hb : ∀ i, f (v i) ≤ f x)
    (hz : z ∈ G) (hcone : z ∈ finiteComparisonCone v x) : f x ≤ f z := by
  obtain ⟨p, hp, t, ht, ht1, he⟩ := hcone
  obtain ⟨hpG, hpf⟩ := convex_value_le_on_query_hull hf v hv hb p hp
  have hc := hf.2 hpG hz (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  rw [← he] at hc
  simp only [smul_eq_mul] at hc
  have hm := mul_le_mul_of_nonneg_left hpf (sub_nonneg.mpr ht1)
  nlinarith

theorem finiteComparisonCone_preserves_better_points {G : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ G f) {m : ℕ} (v : Fin m → E)
    (hv : ∀ i, v i ∈ G) {x : E} (hb : ∀ i, f (v i) ≤ f x) :
    {z | z ∈ G ∧ f z < f x} ⊆ G \ finiteComparisonCone v x := by
  rintro z ⟨hz, hzf⟩
  exact ⟨hz, fun hc => (not_lt_of_ge (finiteComparisonCone_value_ge hf v hv hb hz hc)) hzf⟩

end
end Nonsmooth
