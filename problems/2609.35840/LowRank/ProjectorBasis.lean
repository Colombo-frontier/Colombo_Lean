import LowRank.SpectralCompression
import LowRank.ProjectorRank

/-! Every real orthogonal projector has an orthonormal column factor with
exactly its rank many columns. This supplies the actual compression space
for a residual I-P. -/

namespace LowRank
open Matrix
open scoped Matrix BigOperators RealInnerProductSpace
noncomputable section

theorem projector_rank_complement {d : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) : (1 - P).rank + P.rank = d := by
  have h : ((1 - P).rank : ℝ) + (P.rank : ℝ) = (d : ℝ) := by
    rw [← hP.complement.trace_eq_rank, ← hP.trace_eq_rank, Matrix.trace_sub,
      sub_add_cancel, Matrix.trace_one, Fintype.card_fin]
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
theorem projector_basis_factorization {d m : ℕ} {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = m) :
    ∃ B : Matrix (Fin d) (Fin m) ℝ, Bᵀ * B = 1 ∧ B * Bᵀ = P := by
  let K := LinearMap.range P.toEuclideanLin
  have hdim : Module.finrank ℝ K = m := by
    change Module.finrank ℝ (LinearMap.range
      (Matrix.toLin (PiLp.basisFun 2 ℝ (Fin d)) (PiLp.basisFun 2 ℝ (Fin d)) P)) = m
    rw [← P.rank_eq_finrank_range_toLin (PiLp.basisFun 2 ℝ (Fin d)) (PiLp.basisFun 2 ℝ (Fin d))]
    exact hrank
  let b : OrthonormalBasis (Fin m) ℝ K :=
    (stdOrthonormalBasis ℝ K).reindex (finCongr hdim)
  let B : Matrix (Fin d) (Fin m) ℝ := fun i j => (b j : EuclideanSpace ℝ (Fin d)) i
  have hcol : ∀ j, P *ᵥ (fun i => B i j) = fun i => B i j := by
    intro j
    obtain ⟨x, hx⟩ := (b j).property
    have hx' : P *ᵥ (fun i => x i) = fun i => B i j := congrArg (fun v : EuclideanSpace ℝ (Fin d) => ⇑v) hx
    rw [← hx', Matrix.mulVec_mulVec, hP.idempotent]
  have hB : Bᵀ * B = 1 := by
    ext i j
    have h := (orthonormal_iff_ite.mp b.orthonormal) i j
    change inner (𝕜 := ℝ) (b i : EuclideanSpace ℝ (Fin d)) (b j : EuclideanSpace ℝ (Fin d)) = _ at h
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h
    change (fun x => B x j) ⬝ᵥ (fun x => B x i) = if i = j then 1 else 0 at h
    change (fun x => B x i) ⬝ᵥ (fun x => B x j) = if i = j then 1 else 0
    exact (dotProduct_comm _ _).trans h
  refine ⟨B, hB, ?_⟩
  apply Matrix.ext
  intro i j
  let x : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.basisFun (Fin d) ℝ) j
  let px : K := ⟨P.toEuclideanLin x, LinearMap.mem_range_self _ x⟩
  let coord : K →ₗ[ℝ] ℝ := (PiLp.projₗ 2 (fun _ : Fin d => ℝ) i).comp K.subtype
  have hexp := congrArg coord (b.sum_repr' px)
  have hinner : ∀ a : Fin m, inner (𝕜 := ℝ) (b a) px = B j a := by
    intro a
    change inner (𝕜 := ℝ) (b a : EuclideanSpace ℝ (Fin d)) (P.toEuclideanLin x) = B j a
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
    change (fun l => B l a) ⬝ᵥ (P *ᵥ (fun l => x l)) = B j a
    rw [Matrix.dotProduct_mulVec]
    have hv : (fun l => B l a) ᵥ* P = fun l => B l a := by
      rw [← hP.symmetric, Matrix.vecMul_transpose, hcol]
    rw [hv]
    simp [x, EuclideanSpace.basisFun_apply, dotProduct, B, Pi.single_apply]
  simp only [map_sum, map_smul, smul_eq_mul, hinner] at hexp
  change (∑ a, B j a * B i a) = (P *ᵥ (fun l => x l)) i at hexp
  have hright : P *ᵥ (fun l => x l) = fun l => P l j := by
    ext l
    simp [Matrix.mulVec, dotProduct, x, EuclideanSpace.basisFun_apply, Pi.single_apply]
  rw [hright] at hexp
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, mul_comm] using hexp

theorem projector_complement_basis {k m : ℕ} {P : Matrix (Fin (k + m)) (Fin (k + m)) ℝ}
    (hP : IsOrthogonalProjector P) (hrank : P.rank = k) :
    ∃ B : Matrix (Fin (k + m)) (Fin m) ℝ, Bᵀ * B = 1 ∧ B * Bᵀ = 1 - P := by
  have h := projector_rank_complement hP
  rw [hrank] at h
  exact projector_basis_factorization hP.complement (by omega)

end
end LowRank
