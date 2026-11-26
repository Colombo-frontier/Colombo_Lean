import Smoothness2601.PrefixProducts
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Order.Filter.Finite

/-!
# The bounded frontier from 2601.tex

The separated-support condition is expressed locally: at every scalar point,
either ell vanishes in a neighborhood or the gate vanishes in a neighborhood.
It follows that the actual frontier is locally zero or a single summand.
-/
noncomputable section
namespace Smoothness2601
namespace BoundedFrontier
open Finset Filter
open scoped Topology BigOperators RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def prefixSet (i : ι) : Finset ι := univ.filter fun j => j < i

@[simp] theorem mem_prefixSet {i j : ι} : j ∈ prefixSet i ↔ j < i := by simp [prefixSet]

def prefixValue (a : ℝ → ℝ) (i : ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  ∏ j ∈ prefixSet i, a (z j)

def summand (a ell : ℝ → ℝ) (i : ι) (z : EuclideanSpace ℝ ι) : ℝ :=
  prefixValue a i z * ell (z i)

def frontier (a ell : ℝ → ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  -∑ i, summand a ell i z

def SeparatedSupport (a ell : ℝ → ℝ) : Prop :=
  ∀ t, (∀ᶠ u in 𝓝 t, ell u = 0) ∨ (∀ᶠ u in 𝓝 t, a u = 0)

theorem separatedSupport_of_abs_cutoffs {a ell : ℝ → ℝ} {b c : ℝ} (hbc : b < c)
    (hell : ∀ t, b ≤ |t| → ell t = 0) (ha : ∀ t, |t| ≤ c → a t = 0) :
    SeparatedSupport a ell := by
  intro t
  by_cases ht : |t| < c
  · right
    have hnear : ∀ᶠ u : ℝ in 𝓝 t, |u| < c :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds ht
    exact hnear.mono fun u hu => ha u hu.le
  · left
    have hb : b < |t| := hbc.trans_le (le_of_not_gt ht)
    have hnear : ∀ᶠ u : ℝ in 𝓝 t, b < |u| :=
      (isOpen_lt continuous_const continuous_abs).mem_nhds hb
    exact hnear.mono fun u hu => hell u hu.le

theorem prefix_zero_of_earlier {a : ℝ → ℝ} {i k : ι} {z : EuclideanSpace ℝ ι}
    (hki : k < i) (hk : a (z k) = 0) : prefixValue a i z = 0 := by
  exact Finset.prod_eq_zero (mem_prefixSet.mpr hki) hk

/-- Separated supports imply that all derivatives of the sum at a point come
from at most one summand, because the equality holds on a neighborhood. -/
theorem frontier_locally_single {a ell : ℝ → ℝ} (hsep : SeparatedSupport a ell)
    (z : EuclideanSpace ℝ ι) :
    frontier a ell =ᶠ[𝓝 z] (fun _ => 0) ∨
      ∃ k : ι, frontier a ell =ᶠ[𝓝 z] (fun x => -summand a ell k x) := by
  classical
  let active : Finset ι := univ.filter fun i => ¬(∀ᶠ t in 𝓝 (z i), ell t = 0)
  by_cases hn : active.Nonempty
  · let k := active.min' hn
    have hk : k ∈ active := Finset.min'_mem active hn
    have hknot : ¬(∀ᶠ t in 𝓝 (z k), ell t = 0) := (mem_filter.mp hk).2
    have hgate : ∀ᶠ x : EuclideanSpace ℝ ι in 𝓝 z, a (x k) = 0 :=
      (EuclideanSpace.proj (𝕜 := ℝ) k).continuous.continuousAt.tendsto.eventually ((hsep (z k)).resolve_left hknot)
    have hearly : ∀ i : ι, ∀ᶠ x : EuclideanSpace ℝ ι in 𝓝 z, i < k → ell (x i) = 0 := by
      intro i
      by_cases hik : i < k
      · have hi : ∀ᶠ t in 𝓝 (z i), ell t = 0 := by
          by_cases hi' : ∀ᶠ t in 𝓝 (z i), ell t = 0
          · exact hi'
          · have himem : i ∈ active := mem_filter.mpr ⟨mem_univ i, hi'⟩
            exact False.elim ((not_le_of_gt hik) (Finset.min'_le active i himem))
        exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.tendsto.eventually hi).mono fun _ h _ => h
      · exact Filter.Eventually.of_forall fun _ h => (hik h).elim
    refine Or.inr ⟨k, ?_⟩
    filter_upwards [hgate, Filter.eventually_all.mpr hearly] with x hx hxe
    unfold frontier
    congr 1
    apply Finset.sum_eq_single k
    · intro i _ hik
      rcases lt_or_gt_of_ne hik with hi | hi
      · simp [summand, hxe i hi]
      · simp [summand, prefix_zero_of_earlier hi hx]
    · simp
  · have hall : ∀ i : ι, ∀ᶠ x : EuclideanSpace ℝ ι in 𝓝 z, ell (x i) = 0 := by
      intro i
      have hi : ∀ᶠ t in 𝓝 (z i), ell t = 0 := by
        by_cases hi' : ∀ᶠ t in 𝓝 (z i), ell t = 0
        · exact hi'
        · exact False.elim (hn ⟨i, mem_filter.mpr ⟨mem_univ i, hi'⟩⟩)
      exact (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.continuousAt.tendsto.eventually hi
    refine Or.inl ?_
    filter_upwards [Filter.eventually_all.mpr hall] with x hx
    simp [frontier, summand, hx]

theorem prefix_bounds {a : ℝ → ℝ} (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1)
    (i : ι) (z : EuclideanSpace ℝ ι) : 0 ≤ prefixValue a i z ∧ prefixValue a i z ≤ 1 :=
  ⟨Finset.prod_nonneg fun j _ => (ha (z j)).1,
    Finset.prod_le_one (fun j _ => (ha (z j)).1) (fun j _ => (ha (z j)).2)⟩

theorem summand_abs_le {a ell : ℝ → ℝ} {B : ℝ} (_hB : 0 ≤ B)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hell : ∀ t, |ell t| ≤ B)
    (i : ι) (z : EuclideanSpace ℝ ι) : |summand a ell i z| ≤ B := by
  rw [summand, abs_mul, abs_of_nonneg (prefix_bounds ha i z).1]
  exact (mul_le_mul (prefix_bounds ha i z).2 (hell (z i)) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)

theorem frontier_abs_le {a ell : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hell : ∀ t, |ell t| ≤ B)
    (hsep : SeparatedSupport a ell) (z : EuclideanSpace ℝ ι) : |frontier a ell z| ≤ B := by
  rcases frontier_locally_single hsep z with h | ⟨k, h⟩
  · rw [h.eq_of_nhds]
    simpa using hB
  · rw [h.eq_of_nhds, abs_neg]
    exact summand_abs_le hB ha hell k z

def prefixProjection (i : ι) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  PrefixProducts.diagonalOperator fun j => if j < i then 1 else 0

theorem prefixProjection_norm_le (i : ι) : ‖prefixProjection i‖ ≤ 1 := by
  apply PrefixProducts.diagonalOperator_norm_le _ (by norm_num)
  intro j
  split_ifs <;> norm_num

def prefixOffset (i : ι) (t₁ : ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm fun j => if j < i then 0 else t₁

def prefixMask (i : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  prefixProjection i z + prefixOffset i t₁

@[simp] theorem prefixMask_apply (i j : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) :
    prefixMask i t₁ z j = if j < i then z j else t₁ := by
  change (if j < i then 1 else 0) * z j + (if j < i then 0 else t₁) = _
  split_ifs <;> simp_all

theorem prefixMask_hasFDerivAt (i : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) :
    HasFDerivAt (prefixMask i t₁) (prefixProjection i) z :=
  (prefixProjection i).hasFDerivAt.add_const (prefixOffset i t₁)

theorem prefix_eq_masked_product {a : ℝ → ℝ} {t₁ : ℝ} (ht : a t₁ = 1)
    (i : ι) (z : EuclideanSpace ℝ ι) :
    prefixValue a i z = PrefixProducts.productFunction a (prefixMask i t₁ z) := by
  unfold prefixValue prefixSet PrefixProducts.productFunction
  simp only [Finset.prod_filter, prefixMask_apply]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs <;> simp [ht]

def prefixGradient (a d : ℝ → ℝ) (i : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (prefixProjection i).adjoint (PrefixProducts.productGradient a d (prefixMask i t₁ z))

def prefixHessian (a d e : ℝ → ℝ) (i : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (prefixProjection i).adjoint.comp
    ((PrefixProducts.normalizedHessian (fun j => a (prefixMask i t₁ z j))
      (fun j => d (prefixMask i t₁ z j)) (fun j => e (prefixMask i t₁ z j))).comp (prefixProjection i))

theorem hasGradientAt_prefix {a d : ℝ → ℝ} {t₁ : ℝ} (ht : a t₁ = 1)
    (hd : ∀ t, HasDerivAt a (d t) t) (i : ι) (z : EuclideanSpace ℝ ι) :
    HasGradientAt (prefixValue a i) (prefixGradient a d i t₁ z) z := by
  have hp := (PrefixProducts.hasGradientAt_productFunction a d (prefixMask i t₁ z)
    (fun j => hd _)).hasFDerivAt.comp z (prefixMask_hasFDerivAt i t₁ z)
  rw [hasGradientAt_iff_hasFDerivAt]
  have hf : prefixValue a i = fun x => PrefixProducts.productFunction a (prefixMask i t₁ x) :=
    funext (prefix_eq_masked_product ht i)
  rw [hf]
  convert hp using 1
  ext v
  simp only [prefixGradient, InnerProductSpace.toDual_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem hasFDerivAt_prefixGradient {a d e : ℝ → ℝ} {t₁ : ℝ}
    (hd : ∀ t, HasDerivAt a (d t) t) (he : ∀ t, HasDerivAt d (e t) t)
    (hzero : ∀ t, a t = 0 → d t = 0) (i : ι) (z : EuclideanSpace ℝ ι) :
    HasFDerivAt (prefixGradient a d i t₁) (prefixHessian a d e i t₁ z) z := by
  exact (prefixProjection i).adjoint.hasFDerivAt.comp z
    ((PrefixProducts.hasFDerivAt_productGradient a d e (prefixMask i t₁ z)
      (fun j => hd _) (fun j => he _) (fun j => hzero _)).comp z (prefixMask_hasFDerivAt i t₁ z))

theorem prefixGradient_norm_le {a d : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hd : ∀ t, d t ^ 2 ≤ C * a t * (1 - a t))
    (i : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) : ‖prefixGradient a d i t₁ z‖ ≤ Real.sqrt C := by
  have hproj : ‖(prefixProjection i).adjoint‖ ≤ 1 := by simpa using prefixProjection_norm_le i
  have hg := PrefixProducts.productGradient_norm_le hC ha hd (prefixMask i t₁ z)
  exact ((prefixProjection i).adjoint.le_opNorm _).trans
    ((mul_le_mul hproj hg (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

theorem prefixHessian_norm_le {a d e : ℝ → ℝ} {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hd : ∀ t, d t ^ 2 ≤ C * a t * (1 - a t))
    (he : ∀ t, |e t| ≤ M) (i : ι) (t₁ : ℝ) (z : EuclideanSpace ℝ ι) :
    ‖prefixHessian a d e i t₁ z‖ ≤ 2 * C + M := by
  have hproj : ‖(prefixProjection i).adjoint‖ ≤ 1 := by simpa using prefixProjection_norm_le i
  have hH := PrefixProducts.normalizedHessian_norm_le (fun j => a (prefixMask i t₁ z j))
    (fun j => d (prefixMask i t₁ z j)) (fun j => e (prefixMask i t₁ z j))
    hC hM (fun j => ha _) (fun j => hd _) (fun j => he _)
  unfold prefixHessian
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)).trans
  have hnon : 0 ≤ 2 * C + M := by positivity
  calc
    _ ≤ 1 * ((2 * C + M) * 1) := mul_le_mul hproj
      (mul_le_mul hH (prefixProjection_norm_le i) (norm_nonneg _) hnon)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

abbrev Space := EuclideanSpace ℝ ι

/-- A scalar function together with genuine first and second derivative certificates. -/
structure ScalarC2 where
  value : Space (ι := ι) → ℝ
  grad : Space (ι := ι) → Space (ι := ι)
  hessian : Space (ι := ι) → Space (ι := ι) →L[ℝ] Space (ι := ι)
  hasGradient : ∀ z, HasGradientAt value (grad z) z
  hasHessian : ∀ z, HasFDerivAt grad (hessian z) z

def outer (u v : Space (ι := ι)) : Space (ι := ι) →L[ℝ] Space (ι := ι) :=
  (InnerProductSpace.toDual ℝ _ u).smulRight v

omit [LinearOrder ι] in
@[simp] theorem outer_apply (u v w : Space (ι := ι)) : outer u v w = ⟪u, w⟫ • v := rfl

omit [LinearOrder ι] in
theorem outer_norm_le (u v : Space (ι := ι)) : ‖outer u v‖ ≤ ‖u‖ * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro w
  rw [outer_apply, norm_smul, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (abs_real_inner_le_norm u w) (norm_nonneg v)
  nlinarith

namespace ScalarC2

def mul (F G : ScalarC2 (ι := ι)) : ScalarC2 (ι := ι) where
  value z := F.value z * G.value z
  grad z := G.value z • F.grad z + F.value z • G.grad z
  hessian z := (G.value z • F.hessian z + outer (G.grad z) (F.grad z)) +
    (F.value z • G.hessian z + outer (F.grad z) (G.grad z))
  hasGradient z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (F.hasGradient z).hasFDerivAt.mul (G.hasGradient z).hasFDerivAt using 1
    ext v
    simp [InnerProductSpace.toDual_apply, inner_add_left, real_inner_smul_left, mul_comm, add_comm]
  hasHessian z := by
    exact (((G.hasGradient z).hasFDerivAt.smul (F.hasHessian z)).add
      ((F.hasGradient z).hasFDerivAt.smul (G.hasHessian z)))

def neg (F : ScalarC2 (ι := ι)) : ScalarC2 (ι := ι) where
  value z := -F.value z
  grad z := -F.grad z
  hessian z := -F.hessian z
  hasGradient z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (F.hasGradient z).hasFDerivAt.neg using 1
    ext v
    simp [InnerProductSpace.toDual_apply]
  hasHessian z := (F.hasHessian z).neg

omit [LinearOrder ι] in
theorem gradient_eq (F : ScalarC2 (ι := ι)) (z : Space (ι := ι)) :
    gradient F.value z = F.grad z := (F.hasGradient z).gradient

omit [LinearOrder ι] in
theorem hessian_eq (F : ScalarC2 (ι := ι)) (z : Space (ι := ι)) :
    fderiv ℝ (gradient F.value) z = F.hessian z := by
  have hg : gradient F.value = F.grad := funext F.gradient_eq
  rw [hg, (F.hasHessian z).fderiv]

omit [LinearOrder ι] in
theorem mul_grad_bound (F G : ScalarC2 (ι := ι)) (z : Space (ι := ι))
    {B S L : ℝ} (hB : 0 ≤ B) (_hS : 0 ≤ S) (_hL : 0 ≤ L)
    (hf : |F.value z| ≤ 1) (hg : |G.value z| ≤ B)
    (hfg : ‖F.grad z‖ ≤ S) (hgg : ‖G.grad z‖ ≤ L) :
    ‖(F.mul G).grad z‖ ≤ B * S + L := by
  change ‖G.value z • F.grad z + F.value z • G.grad z‖ ≤ _
  apply (norm_add_le _ _).trans
  simp only [norm_smul, Real.norm_eq_abs]
  have h1 := mul_le_mul hg hfg (norm_nonneg _) hB
  have h2 := mul_le_mul hf hgg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  linarith

omit [LinearOrder ι] in
theorem mul_hessian_bound (F G : ScalarC2 (ι := ι)) (z : Space (ι := ι))
    {B S L H K : ℝ} (hB : 0 ≤ B) (hS : 0 ≤ S) (hL : 0 ≤ L) (_hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hf : |F.value z| ≤ 1) (hg : |G.value z| ≤ B)
    (hfg : ‖F.grad z‖ ≤ S) (hgg : ‖G.grad z‖ ≤ L)
    (hfh : ‖F.hessian z‖ ≤ H) (hgh : ‖G.hessian z‖ ≤ K) :
    ‖(F.mul G).hessian z‖ ≤ B * H + 2 * S * L + K := by
  have h1 : ‖G.value z • F.hessian z‖ ≤ B * H := by
    exact (norm_smul_le (G.value z) (F.hessian z)).trans (by simpa only [Real.norm_eq_abs] using mul_le_mul hg hfh (norm_nonneg _) hB)
  have h2 : ‖outer (G.grad z) (F.grad z)‖ ≤ L * S :=
    (outer_norm_le _ _).trans (mul_le_mul hgg hfg (norm_nonneg _) hL)
  have h3 : ‖F.value z • G.hessian z‖ ≤ K := by
    exact (norm_smul_le (F.value z) (G.hessian z)).trans (by simpa only [Real.norm_eq_abs] using
      (mul_le_mul hf hgh (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).trans_eq (one_mul K))
  have h4 : ‖outer (F.grad z) (G.grad z)‖ ≤ S * L :=
    (outer_norm_le _ _).trans (mul_le_mul hfg hgg (norm_nonneg _) hS)
  change ‖(_ + _) + (_ + _)‖ ≤ _
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (norm_add_le _ _)).trans
  nlinarith

end ScalarC2

def prefixC2 {a d e : ℝ → ℝ} {t₁ : ℝ} (ht : a t₁ = 1)
    (hd : ∀ t, HasDerivAt a (d t) t) (he : ∀ t, HasDerivAt d (e t) t)
    (hzero : ∀ t, a t = 0 → d t = 0) (i : ι) : ScalarC2 (ι := ι) where
  value := prefixValue a i
  grad := prefixGradient a d i t₁
  hessian := prefixHessian a d e i t₁
  hasGradient := hasGradientAt_prefix ht hd i
  hasHessian := hasFDerivAt_prefixGradient hd he hzero i

def coordinateC2 {ell d e : ℝ → ℝ} (hd : ∀ t, HasDerivAt ell (d t) t)
    (he : ∀ t, HasDerivAt d (e t) t) (i : ι) : ScalarC2 (ι := ι) where
  value z := ell (z i)
  grad z := d (z i) • EuclideanSpace.single i 1
  hessian z := e (z i) • PrefixProducts.rankOneOperator (EuclideanSpace.single i 1)
  hasGradient z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert (hd (z i)).comp_hasFDerivAt z (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt using 1
    ext v
    simp [InnerProductSpace.toDual_apply, real_inner_smul_left, EuclideanSpace.inner_single_left]
  hasHessian z := by
    convert ((he (z i)).comp_hasFDerivAt z
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).smul_const (EuclideanSpace.single (𝕜 := ℝ) i 1) using 1
    ext v j
    simp [PrefixProducts.rankOneOperator, InnerProductSpace.toDual_apply, smul_smul,
      EuclideanSpace.inner_single_left, mul_assoc]

theorem coordinateC2_grad_norm {ell d e : ℝ → ℝ} (hd : ∀ t, HasDerivAt ell (d t) t)
    (he : ∀ t, HasDerivAt d (e t) t) (i : ι) (z : Space (ι := ι)) :
    ‖(coordinateC2 hd he i).grad z‖ = |d (z i)| := by
  simp [coordinateC2, norm_smul, Real.norm_eq_abs]

theorem coordinateC2_hessian_norm_le {ell d e : ℝ → ℝ} (hd : ∀ t, HasDerivAt ell (d t) t)
    (he : ∀ t, HasDerivAt d (e t) t) (i : ι) (z : Space (ι := ι)) :
    ‖(coordinateC2 hd he i).hessian z‖ ≤ |e (z i)| := by
  have h : ‖PrefixProducts.rankOneOperator (EuclideanSpace.single (𝕜 := ℝ) i 1)‖ ≤ 1 := by
    simpa only [one_smul] using PrefixProducts.scaled_rankOne_norm_le
      (EuclideanSpace.single (𝕜 := ℝ) i 1) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1) (by simp)
  change ‖e (z i) • _‖ ≤ _
  have hmul : |e (z i)| * ‖PrefixProducts.rankOneOperator (EuclideanSpace.single (𝕜 := ℝ) i 1)‖ ≤ |e (z i)| := by
    nlinarith [mul_le_mul_of_nonneg_left h (abs_nonneg (e (z i)))]
  calc
    _ ≤ |e (z i)| * ‖PrefixProducts.rankOneOperator (EuclideanSpace.single (𝕜 := ℝ) i 1)‖ := by
      simpa only [Real.norm_eq_abs] using norm_smul_le (e (z i))
        (PrefixProducts.rankOneOperator (EuclideanSpace.single (𝕜 := ℝ) i 1))
    _ ≤ _ := hmul

structure GateData where
  a : ℝ → ℝ
  d : ℝ → ℝ
  e : ℝ → ℝ
  t₁ : ℝ
  C : ℝ
  M : ℝ
  C_nonneg : 0 ≤ C
  M_nonneg : 0 ≤ M
  interval : ∀ t, 0 ≤ a t ∧ a t ≤ 1
  unit : a t₁ = 1
  slope_bound : ∀ t, d t ^ 2 ≤ C * a t * (1 - a t)
  curvature_bound : ∀ t, |e t| ≤ M
  hasDeriv : ∀ t, HasDerivAt a (d t) t
  hasSecond : ∀ t, HasDerivAt d (e t) t

structure BumpData where
  ell : ℝ → ℝ
  d : ℝ → ℝ
  e : ℝ → ℝ
  B : ℝ
  L : ℝ
  K : ℝ
  B_nonneg : 0 ≤ B
  L_nonneg : 0 ≤ L
  K_nonneg : 0 ≤ K
  value_bound : ∀ t, |ell t| ≤ B
  slope_bound : ∀ t, |d t| ≤ L
  curvature_bound : ∀ t, |e t| ≤ K
  hasDeriv : ∀ t, HasDerivAt ell (d t) t
  hasSecond : ∀ t, HasDerivAt d (e t) t

theorem GateData.zero_slope (A : GateData) (t : ℝ) (ht : A.a t = 0) : A.d t = 0 := by
  have h := A.slope_bound t
  rw [ht] at h
  nlinarith [sq_nonneg (A.d t)]

def summandC2 (A : GateData) (L : BumpData) (i : ι) : ScalarC2 (ι := ι) :=
  (prefixC2 A.unit A.hasDeriv A.hasSecond A.zero_slope i).mul
    (coordinateC2 L.hasDeriv L.hasSecond i)

theorem summandC2_value (A : GateData) (L : BumpData) (i : ι) :
    (summandC2 A L i).value = summand A.a L.ell i := rfl

theorem summandC2_grad_bound (A : GateData) (L : BumpData) (i : ι) (z : Space (ι := ι)) :
    ‖(summandC2 A L i).grad z‖ ≤ L.B * Real.sqrt A.C + L.L := by
  apply ScalarC2.mul_grad_bound _ _ z L.B_nonneg (Real.sqrt_nonneg _) L.L_nonneg
  · change |prefixValue A.a i z| ≤ 1
    rw [abs_of_nonneg (prefix_bounds A.interval i z).1]
    exact (prefix_bounds A.interval i z).2
  · exact L.value_bound (z i)
  · exact prefixGradient_norm_le A.C_nonneg A.interval A.slope_bound i A.t₁ z
  · rw [coordinateC2_grad_norm]
    exact L.slope_bound (z i)

theorem summandC2_hessian_bound (A : GateData) (L : BumpData) (i : ι) (z : Space (ι := ι)) :
    ‖(summandC2 A L i).hessian z‖ ≤
      L.B * (2 * A.C + A.M) + 2 * Real.sqrt A.C * L.L + L.K := by
  apply ScalarC2.mul_hessian_bound _ _ z L.B_nonneg (Real.sqrt_nonneg _) L.L_nonneg
    (by have := A.C_nonneg; have := A.M_nonneg; positivity) L.K_nonneg
  · change |prefixValue A.a i z| ≤ 1
    rw [abs_of_nonneg (prefix_bounds A.interval i z).1]
    exact (prefix_bounds A.interval i z).2
  · exact L.value_bound (z i)
  · exact prefixGradient_norm_le A.C_nonneg A.interval A.slope_bound i A.t₁ z
  · rw [coordinateC2_grad_norm]
    exact L.slope_bound (z i)
  · exact prefixHessian_norm_le A.C_nonneg A.M_nonneg A.interval A.slope_bound A.curvature_bound i A.t₁ z
  · exact (coordinateC2_hessian_norm_le L.hasDeriv L.hasSecond i z).trans (L.curvature_bound (z i))

/-- `lem:B-bounds` for the actual finite frontier and actual gradient/Hessian,
with constants independent of the dimension. The source's scalar cutoff
functions must be instantiated separately through `GateData` and `BumpData`. -/
theorem frontier_verified_bounds (A : GateData) (L : BumpData)
    (hsep : SeparatedSupport A.a L.ell) (z : Space (ι := ι)) :
    |frontier A.a L.ell z| ≤ L.B ∧
    ‖gradient (frontier A.a L.ell) z‖ ≤ L.B * Real.sqrt A.C + L.L ∧
    ‖fderiv ℝ (gradient (frontier A.a L.ell)) z‖ ≤
      L.B * (2 * A.C + A.M) + 2 * Real.sqrt A.C * L.L + L.K := by
  refine ⟨frontier_abs_le L.B_nonneg A.interval L.value_bound hsep z, ?_⟩
  rcases frontier_locally_single hsep z with h | ⟨k, h⟩
  · constructor
    · rw [h.gradient_eq]
      simp only [gradient_const, norm_zero]
      exact add_nonneg (mul_nonneg L.B_nonneg (Real.sqrt_nonneg _)) L.L_nonneg
    · rw [h.gradient.fderiv_eq]
      have hconst : gradient (fun _ : Space (ι := ι) => (0 : ℝ)) = fun _ => 0 :=
        funext fun x => gradient_const x 0
      rw [hconst, fderiv_const]
      simp only [Pi.zero_apply, norm_zero]
      have := A.C_nonneg
      have := A.M_nonneg
      have := L.B_nonneg
      have := L.L_nonneg
      have := L.K_nonneg
      positivity
  · let F := (summandC2 A L k).neg
    have heq : frontier A.a L.ell =ᶠ[𝓝 z] F.value := h
    constructor
    · rw [heq.gradient_eq, F.gradient_eq]
      change ‖-(summandC2 A L k).grad z‖ ≤ _
      rw [norm_neg]
      exact summandC2_grad_bound A L k z
    · rw [heq.gradient.fderiv_eq, F.hessian_eq]
      change ‖-(summandC2 A L k).hessian z‖ ≤ _
      rw [norm_neg]
      exact summandC2_hessian_bound A L k z

/-- Existence of the genuine derivatives used in the norm statement; no
totalized-derivative convention is used to obtain the frontier bound. -/
theorem frontier_differentiable (A : GateData) (L : BumpData)
    (hsep : SeparatedSupport A.a L.ell) (z : Space (ι := ι)) :
    DifferentiableAt ℝ (frontier A.a L.ell) z ∧
      DifferentiableAt ℝ (gradient (frontier A.a L.ell)) z := by
  rcases frontier_locally_single hsep z with h | ⟨k, h⟩
  · constructor
    · exact ((hasFDerivAt_const (0 : ℝ) z).congr_of_eventuallyEq h).differentiableAt
    · have hg := h.gradient
      have hconst : gradient (fun _ : Space (ι := ι) => (0 : ℝ)) = fun _ => 0 :=
        funext fun x => gradient_const x 0
      rw [hconst] at hg
      exact ((hasFDerivAt_const (0 : Space (ι := ι)) z).congr_of_eventuallyEq hg).differentiableAt
  · let F := (summandC2 A L k).neg
    have heq : frontier A.a L.ell =ᶠ[𝓝 z] F.value := h
    constructor
    · exact ((F.hasGradient z).hasFDerivAt.congr_of_eventuallyEq heq).differentiableAt
    · have hg : gradient (frontier A.a L.ell) =ᶠ[𝓝 z] F.grad := by
        filter_upwards [heq.gradient] with x hx
        exact hx.trans (F.gradient_eq x)
      exact ((F.hasHessian z).congr_of_eventuallyEq hg).differentiableAt

end BoundedFrontier
end Smoothness2601

