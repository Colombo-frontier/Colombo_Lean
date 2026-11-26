import Bilevel.ChiPrefixCompletion
import Bilevel.ChiCarrierBlockSlice

/-! Isometric zero-auxiliary inclusions for actual finite Hilbert products.
Composition with these maps preserves every established global jet bound. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiCarrier PrimitiveGeometry
variable {E A X Y X' Y' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X'] [InnerProductSpace ℝ X'] [CompleteSpace X']
  [NormedAddCommGroup Y'] [InnerProductSpace ℝ Y'] [CompleteSpace Y']

def zeroInclusion : E →ₗᵢ[ℝ] Joint E A where
  toLinearMap :=
    { toFun := fun u => pack u 0
      map_add' := by intro x y;change pack (x+y) (0:A)=pack (x+y) (0+0);rw [add_zero]
      map_smul' := by intro c x;change pack (c • x) (0:A)=pack (c • x) (c • 0);rw [smul_zero] }
  norm_map' := norm_pack_zero

def blockInclusion (m : ℕ) : Blocks m E →ₗᵢ[ℝ] Blocks m (Joint E A) where
  toLinearMap :=
    { toFun := fun x => (WithLp.equiv 2 (Fin m → Joint E A)).symm (fun i => pack (x i) 0)
      map_add' := by intro x y;ext i;change pack (x i+y i) (0:A)=pack (x i+y i) (0+0);rw [add_zero]
      map_smul' := by intro c x;ext i;change pack (c • x i) (0:A)=pack (c • x i) (c • 0);rw [smul_zero] }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [←real_inner_self_eq_norm_sq,←real_inner_self_eq_norm_sq,PiLp.inner_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change ⟪pack (x i) (0:A),pack (x i) (0:A)⟫=⟪x i,x i⟫
    simp [WithLp.prod_inner_apply,pack]

omit [CompleteSpace E] [CompleteSpace A] in
theorem blockInclusion_apply (m : ℕ) (x : Blocks m E) (i : Fin m) :
    blockInclusion (A:=A) m x i=pack (x i) 0 := rfl

omit [CompleteSpace E] [CompleteSpace A] in
theorem block_blockInclusion (m j : ℕ) (x : Blocks m E) :
    block m j (blockInclusion (A:=A) m x)=pack (block m j x) 0 := by
  by_cases hj : j<m
  · simp only [block,dif_pos hj,PiLp.proj_apply,blockInclusion_apply]
  · simp only [block,dif_neg hj,ContinuousLinearMap.zero_apply]
    rfl

def jointMap (T : X →ₗᵢ[ℝ] X') (S : Y →ₗᵢ[ℝ] Y') : Joint X Y →ₗᵢ[ℝ] Joint X' Y' where
  toLinearMap :=
    { toFun := fun q => pack (T q.fst) (S q.snd)
      map_add' := by intro x y;change pack (T (x.fst+y.fst)) (S (x.snd+y.snd))=_;simp only [map_add];rfl
      map_smul' := by intro c x;change pack (T (c • x.fst)) (S (c • x.snd))=_;simp only [map_smul];rfl }
  norm_map' q := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    change ‖T q.fst‖^2+‖S q.snd‖^2=‖q.fst‖^2+‖q.snd‖^2
    rw [T.norm_map,S.norm_map]

omit [CompleteSpace E] [CompleteSpace A] in
theorem isometric_jet_restriction (T : E →ₗᵢ[ℝ] A) (f : A → ℝ) (hf : ContDiff ℝ 3 f)
    (x : E) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (f ∘ T) x‖≤‖iteratedFDeriv ℝ k f (T x)‖ := by
  change ‖iteratedFDeriv ℝ k (f ∘ T.toContinuousLinearMap) x‖≤_
  rw [T.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hT : ‖T.toContinuousLinearMap‖≤1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simp only [LinearIsometry.coe_toContinuousLinearMap,T.norm_map,one_mul,le_refl]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg _) hT) (norm_nonneg _)

end Bilevel.ChiPrefixEvaluation
