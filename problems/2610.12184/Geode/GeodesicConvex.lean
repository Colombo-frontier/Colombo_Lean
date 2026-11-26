import Geode.Halfspace
import Geode.HyperbolicCompact
import Mathlib.Topology.Compactness.Compact

/-! Geodesic convex sets, functions, and the closed geodesic convex hull in the
actual hyperboloid model. -/
namespace Geode.Lorentz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def GConvex (S : Set (Point E)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → segment x y t ∈ S

def GConvexFunction (f : Point E → ℝ) : Prop :=
  ∀ x y : Point E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (segment x y t) ≤ (1 - t) * f x + t * f y

theorem segment_val_combination (x y : Point E) (hne : x ≠ y) (t : ℝ) :
    (segment x y t).val =
      (Real.sinh ((1 - t) * dist x y) / Real.sinh (dist x y)) • x.val +
      (Real.sinh (t * dist x y) / Real.sinh (dist x y)) • y.val := by
  have hs : Real.sinh (dist x y) ≠ 0 := (Real.sinh_pos_iff.mpr (dist_pos.mpr hne)).ne'
  have hcoef : Real.cosh (t * dist x y) -
        Real.sinh (t * dist x y) / Real.sinh (dist x y) * Real.cosh (dist x y) =
      Real.sinh ((1 - t) * dist x y) / Real.sinh (dist x y) := by
    rw [show (1 - t) * dist x y = dist x y - t * dist x y by ring, Real.sinh_sub]
    field_simp only [hs]
    ring
  unfold segment
  rw [dif_neg hne]
  change Real.cosh (t * dist x y) • x.val +
      Real.sinh (t * dist x y) • direction x y = _
  rw [direction, smul_smul, ← div_eq_mul_inv, smul_sub, smul_smul]
  rw [← hcoef]
  module

theorem gconvex_halfspace (h : Ambient E) : GConvex (halfspace h) := by
  intro x hx y hy t ht ht1
  by_cases hxy : x = y
  · subst y
    simpa [segment] using hx
  · have hs := Real.sinh_pos_iff.mpr (dist_pos.mpr hxy)
    have ha : 0 ≤ Real.sinh ((1 - t) * dist x y) / Real.sinh (dist x y) := by
      apply div_nonneg _ hs.le
      exact Real.sinh_nonneg_iff.mpr (mul_nonneg (by linarith) dist_nonneg)
    have hb : 0 ≤ Real.sinh (t * dist x y) / Real.sinh (dist x y) := by
      apply div_nonneg _ hs.le
      exact Real.sinh_nonneg_iff.mpr (mul_nonneg ht dist_nonneg)
    change form E h (segment x y t).val ≤ 0
    rw [segment_val_combination x y hxy, form_add_right, form_smul_right, form_smul_right]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
      (mul_nonpos_of_nonneg_of_nonpos hb hy)

theorem continuous_form_point (h : Ambient E) :
    Continuous (fun x : Point E => form E h x.val) := by
  unfold form
  exact (continuous_const.mul continuous_val.fst).add
    (continuous_const.inner continuous_val.snd)

theorem isClosed_halfspace (h : Ambient E) : IsClosed (halfspace h) :=
  isClosed_le (continuous_form_point h) continuous_const

theorem gconvex_section (W : Submodule ℝ (Ambient E)) :
    GConvex {x : Point E | x.val ∈ W} := by
  intro x hx y hy t _ _
  exact section_segment_mem W x y hx hy t

theorem isClosed_section (W : Submodule ℝ (Ambient E)) (hW : IsClosed (W : Set (Ambient E))) :
    IsClosed {x : Point E | x.val ∈ W} :=
  hW.preimage continuous_val

theorem gconvex_univ : GConvex (Set.univ : Set (Point E)) := by
  intro x hx y hy t ht ht1
  trivial

theorem GConvex.sInter {C : Set (Set (Point E))} (hC : ∀ S ∈ C, GConvex S) :
    GConvex (⋂₀ C) := by
  intro x hx y hy t ht ht1 S hS
  exact hC S hS x (hx S hS) y (hy S hS) t ht ht1

theorem GConvex.inter {S T : Set (Point E)} (hS : GConvex S) (hT : GConvex T) :
    GConvex (S ∩ T) := by
  intro x hx y hy t ht ht1
  exact ⟨hS x hx.1 y hy.1 t ht ht1, hT x hx.2 y hy.2 t ht ht1⟩

theorem GConvexFunction.sublevel {f : Point E → ℝ} (hf : GConvexFunction f) (a : ℝ) :
    GConvex {x | f x ≤ a} := by
  intro x hx y hy t ht ht1
  have h := hf x y t ht ht1
  change f (segment x y t) ≤ a
  nlinarith [mul_le_mul_of_nonneg_left hx (show 0 ≤ 1 - t by linarith),
    mul_le_mul_of_nonneg_left hy ht]

def closedGConv (S : Set (Point E)) : Set (Point E) :=
  ⋂₀ {C : Set (Point E) | IsClosed C ∧ GConvex C ∧ S ⊆ C}

theorem isClosed_closedGConv (S : Set (Point E)) : IsClosed (closedGConv S) :=
  isClosed_sInter (fun _C hC => hC.1)

theorem gconvex_closedGConv (S : Set (Point E)) : GConvex (closedGConv S) :=
  GConvex.sInter (fun _C hC => hC.2.1)

theorem subset_closedGConv (S : Set (Point E)) : S ⊆ closedGConv S := by
  intro x hx C hC
  exact hC.2.2 hx

theorem closedGConv_minimal {S C : Set (Point E)} (hS : S ⊆ C)
    (hC : IsClosed C) (hCg : GConvex C) : closedGConv S ⊆ C := by
  intro x hx
  exact hx C ⟨hC, hCg, hS⟩

theorem closedGConv_mono {S T : Set (Point E)} (hST : S ⊆ T) :
    closedGConv S ⊆ closedGConv T :=
  closedGConv_minimal (hST.trans (subset_closedGConv T))
    (isClosed_closedGConv T) (gconvex_closedGConv T)

@[simp] theorem closedGConv_idem (S : Set (Point E)) :
    closedGConv (closedGConv S) = closedGConv S := by
  apply Set.Subset.antisymm
  · exact closedGConv_minimal (Set.Subset.refl _) (isClosed_closedGConv S) (gconvex_closedGConv S)
  · exact subset_closedGConv _

theorem closedGConv_eq {S : Set (Point E)} (hS : IsClosed S) (hSg : GConvex S) :
    closedGConv S = S :=
  Set.Subset.antisymm (closedGConv_minimal (Set.Subset.refl _) hS hSg) (subset_closedGConv S)

theorem isCompact_closedGConv {S K : Set (Point E)} (hK : IsCompact K)
    (hKg : GConvex K) (hSK : S ⊆ K) : IsCompact (closedGConv S) :=
  hK.of_isClosed_subset (isClosed_closedGConv S) (closedGConv_minimal hSK hK.isClosed hKg)

theorem closedGConv_subset_halfspace {S : Set (Point E)} (h : Ambient E)
    (hS : S ⊆ halfspace h) : closedGConv S ⊆ halfspace h :=
  closedGConv_minimal hS (isClosed_halfspace h) (gconvex_halfspace h)

theorem closedGConv_subset_section {S : Set (Point E)} (W : Submodule ℝ (Ambient E))
    (hW : IsClosed (W : Set (Ambient E))) (hS : ∀ x ∈ S, x.val ∈ W) :
    ∀ x ∈ closedGConv S, x.val ∈ W :=
  closedGConv_minimal hS (isClosed_section W hW) (gconvex_section W)

theorem closedGConv_nonempty {S : Set (Point E)} (hne : S.Nonempty) :
    (closedGConv S).Nonempty := hne.mono (subset_closedGConv S)

end Geode.Lorentz
