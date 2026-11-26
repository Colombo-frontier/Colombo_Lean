import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Orthogonal branch maps and the exact averaged pipe quadratic

The branch family consists of actual linear isometries with orthogonal ranges.
Its normalized sum is proved to be an isometry. Adjoint identities and actual
partial-gradient formulas give the value/gradient branch-action interface.
The finite-layer pipe average is derived exactly by exchanging finite sums and
expanding squared differences; the layer spaces may have different dimensions.
-/

namespace NCConcave16991
namespace BranchGeometry

open scoped BigOperators InnerProductSpace

variable (ι : Type*) [Fintype ι]

noncomputable def beta : ℝ := 1 / Real.sqrt (Fintype.card ι)

theorem cardReal_pos [Nonempty ι] : 0 < (Fintype.card ι : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem beta_pos [Nonempty ι] : 0 < beta ι := by
  unfold beta
  exact div_pos (by norm_num) (Real.sqrt_pos.mpr (cardReal_pos ι))

theorem beta_sq [Nonempty ι] : beta ι ^ 2 = 1 / (Fintype.card ι : ℝ) := by
  unfold beta
  rw [div_pow, one_pow, Real.sq_sqrt (cardReal_pos ι).le]

theorem beta_normalization [Nonempty ι] : beta ι ^ 2 * (Fintype.card ι : ℝ) = 1 := by
  rw [beta_sq]
  field_simp [ne_of_gt (cardReal_pos ι)]

variable {ι} [DecidableEq ι]
variable (H K : Type*) [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℝ H] [InnerProductSpace ℝ K]

/-- The geometric assumptions are about the actual maps: each map is an
isometry and any two distinct ranges are orthogonal. -/
structure BranchFamily where
  branch : ι → H →ₗᵢ[ℝ] K
  orthogonal : ∀ i j, i ≠ j → ∀ x y,
    ⟪branch i x, branch j y⟫_ℝ = 0

variable {H K}

namespace BranchFamily

variable (B : BranchFamily (ι := ι) H K)

omit [Fintype ι] in
theorem inner_branch (i j : ι) (x y : H) :
    ⟪B.branch i x, B.branch j y⟫_ℝ = if i = j then ⟪x, y⟫_ℝ else 0 := by
  classical
  by_cases h : i = j
  · subst j
    simp [(B.branch i).inner_map_map]
  · simpa only [h, ↓reduceIte] using B.orthogonal i j h x y

noncomputable def rawSum : H →ₗ[ℝ] K := ∑ i, (B.branch i).toLinearMap

omit [DecidableEq ι] in
theorem rawSum_apply (x : H) : B.rawSum x = ∑ i, B.branch i x := by
  simp [rawSum]

theorem rawSum_inner (x y : H) :
    ⟪B.rawSum x, B.rawSum y⟫_ℝ = (Fintype.card ι : ℝ) * ⟪x, y⟫_ℝ := by
  classical
  simp only [rawSum_apply, sum_inner, inner_sum, B.inner_branch]
  simp

noncomputable def normalizedMap : H →ₗ[ℝ] K := (beta ι) • B.rawSum

theorem normalizedMap_inner [Nonempty ι] (x y : H) :
    ⟪B.normalizedMap x, B.normalizedMap y⟫_ℝ = ⟪x, y⟫_ℝ := by
  simp only [normalizedMap, LinearMap.smul_apply, real_inner_smul_left,
    real_inner_smul_right, B.rawSum_inner]
  calc
    beta ι * (beta ι * ((Fintype.card ι : ℝ) * ⟪x, y⟫_ℝ)) =
        (beta ι ^ 2 * (Fintype.card ι : ℝ)) * ⟪x, y⟫_ℝ := by ring
    _ = ⟪x, y⟫_ℝ := by rw [beta_normalization, one_mul]

/-- The normalized branch sum is an actual linear isometry. -/
noncomputable def normalizedIsometry [Nonempty ι] : H →ₗᵢ[ℝ] K :=
  B.normalizedMap.isometryOfInner B.normalizedMap_inner

theorem normalizedIsometry_apply [Nonempty ι] (x : H) :
    B.normalizedIsometry x = beta ι • ∑ i, B.branch i x := by
  change B.normalizedMap x = _
  simp only [normalizedMap, LinearMap.smul_apply, B.rawSum_apply]

theorem average_action [Nonempty ι] (x : H) :
    (1 / (Fintype.card ι : ℝ)) • (∑ i, B.branch i x) =
      beta ι • B.normalizedIsometry x := by
  rw [B.normalizedIsometry_apply, smul_smul]
  have hb : beta ι * beta ι = 1 / (Fintype.card ι : ℝ) := by
    nlinarith [beta_sq ι]
  rw [hb]

theorem average_bilinear [Nonempty ι] (x : H) (y : K) :
    (1 / (Fintype.card ι : ℝ)) * (∑ i, ⟪y, B.branch i x⟫_ℝ) =
      beta ι * ⟪y, B.normalizedIsometry x⟫_ℝ := by
  have hh := congrArg (fun z : K => ⟪y, z⟫_ℝ) (B.average_action x)
  simpa only [real_inner_smul_right, inner_sum] using hh

section Adjoint

variable [CompleteSpace H] [CompleteSpace K]

omit [Fintype ι] in
/-- Exact transpose action on another branch. -/
theorem branch_adjoint_branch (i j : ι) (x : H) :
    (B.branch i).toContinuousLinearMap.adjoint (B.branch j x) = if i = j then x else 0 := by
  classical
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪B.branch i z, B.branch j x⟫_ℝ = _
  rw [B.inner_branch]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] in
theorem branch_adjoint_norm_le (i : ι) (y : K) :
    ‖(B.branch i).toContinuousLinearMap.adjoint y‖ ≤ ‖y‖ := by
  let A := (B.branch i).toContinuousLinearMap
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound A (by norm_num)
    intro x
    simp [A]
  have hnorm := (A.adjoint).le_opNorm y
  rw [ContinuousLinearMap.adjoint.norm_map] at hnorm
  have hh := mul_le_mul_of_nonneg_right hA (norm_nonneg y)
  change ‖A.adjoint y‖ ≤ ‖y‖
  nlinarith

theorem branch_adjoint_normalized [Nonempty ι] (i : ι) (x : H) :
    (B.branch i).toContinuousLinearMap.adjoint (B.normalizedIsometry x) = beta ι • x := by
  classical
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪B.branch i z, B.normalizedIsometry x⟫_ℝ = _
  simp only [B.normalizedIsometry_apply, real_inner_smul_right, inner_sum, B.inner_branch]
  simp

theorem normalized_adjoint_branch [Nonempty ι] (i : ι) (x : H) :
    B.normalizedIsometry.toContinuousLinearMap.adjoint (B.branch i x) = beta ι • x := by
  classical
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  change ⟪B.normalizedIsometry z, B.branch i x⟫_ℝ = _
  simp only [B.normalizedIsometry_apply, real_inner_smul_left, sum_inner, B.inner_branch,
    real_inner_smul_right]
  simp

end Adjoint

/-- Independent orthogonal coordinate changes preserve the branch geometry.
This gives the paper's `O_next ∘ J_i ∘ O_prev⁻¹` construction from the canonical
coordinate family below. -/
noncomputable def conjugate {H' K' : Type*}
    [NormedAddCommGroup H'] [NormedAddCommGroup K']
    [InnerProductSpace ℝ H'] [InnerProductSpace ℝ K']
    (R : H' ≃ₗᵢ[ℝ] H) (S : K ≃ₗᵢ[ℝ] K') : BranchFamily (ι := ι) H' K' where
  branch i := S.toLinearIsometry.comp ((B.branch i).comp R.toLinearIsometry)
  orthogonal := by
    intro i j hij x y
    change ⟪S (B.branch i (R x)), S (B.branch j (R y))⟫_ℝ = 0
    rw [S.inner_map_map]
    exact B.orthogonal i j hij (R x) (R y)

end BranchFamily

noncomputable def coordinateMap (i : ι) : H →ₗ[ℝ] PiLp 2 (fun _ : ι => H) where
  toFun := fun x => (PiLp.single 2 i x : PiLp 2 (fun _ : ι => H))
  map_add' := fun _ _ => PiLp.single_add 2 i
  map_smul' := by
    intro c x
    ext j
    simp only [PiLp.single_apply, PiLp.smul_apply]
    split_ifs <;> simp

/-- Canonical coordinate injections realize the assumptions in a finite L²
sum. A finite-dimensional source gives a finite-dimensional branch target. -/
noncomputable def coordinateIsometry (i : ι) : H →ₗᵢ[ℝ] PiLp 2 (fun _ : ι => H) :=
  (coordinateMap i).isometryOfInner (by
    intro x y
    change ⟪(PiLp.single 2 i x : PiLp 2 (fun _ : ι => H)), PiLp.single 2 i y⟫_ℝ = ⟪x, y⟫_ℝ
    rw [PiLp.inner_apply]
    simp only [PiLp.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp)

noncomputable def coordinateBranchFamily : BranchFamily (ι := ι) H (PiLp 2 (fun _ : ι => H)) where
  branch := coordinateIsometry
  orthogonal := by
    intro i j hij x y
    change ⟪(PiLp.single 2 i x : PiLp 2 (fun _ : ι => H)), PiLp.single 2 j y⟫_ℝ = 0
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k = i
    · subst k
      simp [hij]
    · simp [hk]

/-- A bilinear term's actual first partial gradient is one transpose action. -/
theorem bilinear_hasGradientAt_left [CompleteSpace H] [CompleteSpace K]
    (A : H →L[ℝ] K) (x : H) (y : K) :
    HasGradientAt (fun z => ⟪y, A z⟫_ℝ) (A.adjoint y) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (InnerProductSpace.toDual ℝ H (A.adjoint y)).hasFDerivAt using 1
  ext z
  simp [ContinuousLinearMap.adjoint_inner_left]

/-- The second partial gradient is one forward branch action. -/
theorem bilinear_hasGradientAt_right [CompleteSpace K]
    (A : H →L[ℝ] K) (x : H) (y : K) :
    HasGradientAt (fun z => ⟪z, A x⟫_ℝ) (A x) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (InnerProductSpace.toDual ℝ K (A x)).hasFDerivAt using 1
  ext z
  simp [real_inner_comm]

section Pipe

variable {N : ℕ} {V : Fin (N + 1) → Type*}
    [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
    [Nonempty ι]

/-- Literal selected-component pipe quadratic. `base` is its common connector
penalty and endpoint coupling, independent of the selected index. -/
noncomputable def pipeComponent
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (base μ : ℝ) (w : ∀ j, V j) (i : ι) : ℝ :=
  base - beta ι / 2 * (μ * (∑ j, ‖w j‖ ^ 2) +
    ∑ t : Fin N, (‖w t.castSucc‖ ^ 2 + ‖w t.succ‖ ^ 2)) +
      ∑ t : Fin N, ⟪w t.succ, (B t).branch i (w t.castSucc)⟫_ℝ

/-- The averaged dual quadratic is exactly a sum of squared discrepancies
along the normalized branch isometries, as in equation (82). -/
theorem pipe_average
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (base μ : ℝ) (w : ∀ j, V j) :
    (1 / (Fintype.card ι : ℝ)) * (∑ i, pipeComponent B base μ w i) =
      base - beta ι / 2 * (μ * (∑ j, ‖w j‖ ^ 2) +
        ∑ t : Fin N, ‖w t.succ - (B t).normalizedIsometry (w t.castSucc)‖ ^ 2) := by
  have hcross : (1 / (Fintype.card ι : ℝ)) *
      (∑ i, ∑ t : Fin N, ⟪w t.succ, (B t).branch i (w t.castSucc)⟫_ℝ) =
      beta ι * (∑ t : Fin N, ⟪w t.succ, (B t).normalizedIsometry (w t.castSucc)⟫_ℝ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact (B t).average_bilinear _ _
  have hsquares : (∑ t : Fin N,
      ‖w t.succ - (B t).normalizedIsometry (w t.castSucc)‖ ^ 2) =
      (∑ t : Fin N, (‖w t.castSucc‖ ^ 2 + ‖w t.succ‖ ^ 2)) -
        2 * (∑ t : Fin N, ⟪w t.succ, (B t).normalizedIsometry (w t.castSucc)⟫_ℝ) := by
    simp only [norm_sub_sq_real, LinearIsometry.norm_map, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hn : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt (cardReal_pos ι)
  simp only [pipeComponent, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_add]
  rw [hcross, hsquares]
  simp only [Finset.sum_add_distrib]
  field_simp
  ring

/-- The complete endpoint/connector part of the component is retained in the
literal full pipe definition. -/
noncomputable def fullPipeComponent
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (a : V 0) (b : V (Fin.last N)) (w : ∀ j, V j) (i : ι) : ℝ :=
  pipeComponent B (d * (‖a‖ ^ 2 + ‖b‖ ^ 2) +
    r * (⟪a, w 0⟫_ℝ - ⟪b, w (Fin.last N)⟫_ℝ)) μ w i

theorem fullPipe_average
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (a : V 0) (b : V (Fin.last N)) (w : ∀ j, V j) :
    (1 / (Fintype.card ι : ℝ)) * (∑ i, fullPipeComponent B d r μ a b w i) =
      d * (‖a‖ ^ 2 + ‖b‖ ^ 2) + r * (⟪a, w 0⟫_ℝ - ⟪b, w (Fin.last N)⟫_ℝ) -
        beta ι / 2 * (μ * (∑ j, ‖w j‖ ^ 2) +
          ∑ t : Fin N, ‖w t.succ - (B t).normalizedIsometry (w t.castSucc)‖ ^ 2) :=
  pipe_average B _ μ w

omit [∀ j, InnerProductSpace ℝ (V j)] in
/-- Each layer occurs in at most two adjacent edge energies. -/
theorem edge_norm_sum_bound (w : ∀ j, V j) :
    (∑ t : Fin N, (‖w t.castSucc‖ ^ 2 + ‖w t.succ‖ ^ 2)) ≤
      2 * (∑ j, ‖w j‖ ^ 2) := by
  have hleft := Fin.sum_univ_castSucc (fun j : Fin (N + 1) => ‖w j‖ ^ 2)
  have hright := Fin.sum_univ_succ (fun j : Fin (N + 1) => ‖w j‖ ^ 2)
  rw [Finset.sum_add_distrib]
  nlinarith [sq_nonneg ‖w 0‖, sq_nonneg ‖w (Fin.last N)‖]

omit [∀ j, InnerProductSpace ℝ (V j)] in
theorem layer_norm_sq_le_sum (w : ∀ j, V j) (j : Fin (N + 1)) :
    ‖w j‖ ^ 2 ≤ ∑ k, ‖w k‖ ^ 2 :=
  Finset.single_le_sum (fun k _ => sq_nonneg ‖w k‖) (Finset.mem_univ j)

end Pipe

theorem abs_inner_le_half_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) :
    |⟪x, y⟫_ℝ| ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have hh := abs_real_inner_le_norm x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

omit [DecidableEq ι] in
theorem beta_le_one [Nonempty ι] : beta ι ≤ 1 := by
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : 1 ≤ Real.sqrt (Fintype.card ι) := by
    simpa using Real.sqrt_le_sqrt hn
  unfold beta
  apply (div_le_one (Real.sqrt_pos.mpr (cardReal_pos ι))).mpr
  exact hs

section PipeBound

variable {N : ℕ} {V : Fin (N + 1) → Type*}
    [∀ j, NormedAddCommGroup (V j)] [∀ j, InnerProductSpace ℝ (V j)]
    [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem selected_cross_sum_bound
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (w : ∀ j, V j) (i : ι) :
    |∑ t : Fin N, ⟪w t.succ, (B t).branch i (w t.castSucc)⟫_ℝ| ≤ ∑ j, ‖w j‖ ^ 2 := by
  have hnorm := norm_sum_le Finset.univ
    (fun t : Fin N => ⟪w t.succ, (B t).branch i (w t.castSucc)⟫_ℝ)
  simp only [Real.norm_eq_abs] at hnorm
  have hpoint : ∀ t : Fin N,
      |⟪w t.succ, (B t).branch i (w t.castSucc)⟫_ℝ| ≤
        (‖w t.castSucc‖ ^ 2 + ‖w t.succ‖ ^ 2) / 2 := by
    intro t
    simpa only [LinearIsometry.norm_map, add_comm] using
      abs_inner_le_half_norm_sq (w t.succ) ((B t).branch i (w t.castSucc))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hpoint t)
  rw [← Finset.sum_div] at hs
  have he := edge_norm_sum_bound w
  linarith

omit [DecidableEq ι] in
/-- A dimension-free bound on the actual selected-component joint quadratic
form. It is proved from the explicit component terms, not assumed as an
operator-norm interface. An identification of the full joint Hessian operator
is a separate calculus statement. -/
theorem fullPipeComponent_quadratic_bound
    (B : ∀ t : Fin N, BranchFamily (ι := ι) (V t.castSucc) (V t.succ))
    (d r μ : ℝ) (hd : |d| ≤ 1 / 2) (hr : |r| ≤ 1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (a : V 0) (b : V (Fin.last N)) (w : ∀ j, V j) (i : ι) :
    |fullPipeComponent B d r μ a b w i| ≤
      4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ∑ j, ‖w j‖ ^ 2) := by
  let C := ‖a‖ ^ 2 + ‖b‖ ^ 2
  let W := ∑ j, ‖w j‖ ^ 2
  let E := ∑ t : Fin N, (‖w t.castSucc‖ ^ 2 + ‖w t.succ‖ ^ 2)
  let T := ⟪a, w 0⟫_ℝ - ⟪b, w (Fin.last N)⟫_ℝ
  let X := ∑ t : Fin N, ⟪w t.succ, (B t).branch i (w t.castSucc)⟫_ℝ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : 0 ≤ W := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => by positivity)
  have he : E ≤ 2 * W := edge_norm_sum_bound w
  have hx : |X| ≤ W := selected_cross_sum_bound B w i
  have ht : |T| ≤ C / 2 + W := by
    have htri := abs_add_le ⟪a, w 0⟫_ℝ (-⟪b, w (Fin.last N)⟫_ℝ)
    rw [abs_neg] at htri
    have ha := abs_inner_le_half_norm_sq a (w 0)
    have hb := abs_inner_le_half_norm_sq b (w (Fin.last N))
    have hw0 := layer_norm_sq_le_sum w 0
    have hwlast := layer_norm_sq_le_sum w (Fin.last N)
    dsimp [T, C]
    rw [sub_eq_add_neg]
    dsimp [W] at *
    linarith
  have hpen : |d * C| ≤ C / 2 := by
    rw [abs_mul, abs_of_nonneg hC]
    have hh := mul_le_mul_of_nonneg_right hd hC
    linarith
  have hcoup : |r * T| ≤ C / 2 + W := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_right hr (abs_nonneg T)
    nlinarith
  have hdiag : |beta ι / 2 * (μ * W + E)| ≤ 3 / 2 * W := by
    have hb0 := (beta_pos ι).le
    have hb1 := beta_le_one (ι := ι)
    have hμW := mul_le_mul_of_nonneg_right hμ1 hW
    have hinside : 0 ≤ μ * W + E := by positivity
    rw [abs_of_nonneg (by positivity : 0 ≤ beta ι / 2 * (μ * W + E))]
    have hh := mul_le_mul_of_nonneg_right hb1 hinside
    nlinarith
  have hbase : |d * C + r * T| ≤ C + W := by
    have hh := abs_add_le (d * C) (r * T)
    linarith
  have hsub := abs_add_le (d * C + r * T) (-(beta ι / 2 * (μ * W + E)))
  rw [abs_neg] at hsub
  have hfull := abs_add_le (d * C + r * T - beta ι / 2 * (μ * W + E)) X
  change |d * C + r * T - beta ι / 2 * (μ * W + E) + X| ≤ 4 * (C + W)
  rw [sub_eq_add_neg] at hfull ⊢
  nlinarith

end PipeBound
end BranchGeometry
end NCConcave16991
