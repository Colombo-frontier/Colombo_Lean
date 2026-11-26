import Bilevel.EndpointTransportFrameCompletion
import Bilevel.EndpointTransportReadout

/-! Finite Euclidean realization of independently completed endpoint
frames, with an isometric embedding of the entire physical query. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiPrefixEvaluation EndpointTransportMatrix

def completionDimension (D K : ℕ) : ℕ := Module.finrank ℝ (Joint (Block D) (Space K))

def completionBlockEquiv (D K : ℕ) :
    Joint (Block D) (Space K) ≃ₗᵢ[ℝ] Block (completionDimension D K) :=
  (stdOrthonormalBasis ℝ (Joint (Block D) (Space K))).repr

def completionBlockInclusion (D K : ℕ) : Block D →ₗᵢ[ℝ] Block (completionDimension D K) :=
  (completionBlockEquiv D K).toLinearIsometry.comp (zeroInclusion (E:=Block D) (A:=Space K))

def commonCompletionFrame (D K : ℕ) : Space K →ₗᵢ[ℝ] Block (completionDimension D K) :=
  (completionBlockEquiv D K).toLinearIsometry.comp
    (completionFrame K 0 (fun _ => (0:Block D)) (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry
      (by intro a b ha;omega))

theorem completed_rotations_exist (n D K : ℕ) (r : Index n → ℕ)
    (columns : Index n → Fin (K+1) → Block D)
    (hGram : ∀ i,∀ a b : Fin (K+1),a.val<r i → b.val<r i →
      ⟪columns i a,columns i b⟫=if a=b then 1 else 0) :
    ∃ Q : Rotations n (completionDimension D K),∀ i k,
      Q i (commonCompletionFrame D K (basis k))=
        completionBlockEquiv D K (completedColumn K (r i) (columns i)
          (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry k) := by
  let U := completionFrame K 0 (fun _ => (0:Block D))
    (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry (by intro a b ha;omega)
  obtain ⟨Q,hQ⟩ := prefix_rotations_exist K r columns U
    (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry hGram
  let e := completionBlockEquiv D K
  refine ⟨fun i => (e.symm.trans (Q i)).trans e,?_⟩
  intro i k
  change e (Q i (e.symm (e (U (basis k)))))=_
  rw [e.symm_apply_apply,hQ]

def physicalMap {n D D' : ℕ} (I : Block D →ₗᵢ[ℝ] Block D') : Physical n D →ₗᵢ[ℝ] Physical n D' where
  toLinearMap :=
    { toFun := fun Y => (WithLp.equiv 2 (Index n → Block D')).symm (fun v => I (Y v))
      map_add' := by intro x y;ext v;simp
      map_smul' := by intro c x;ext v;simp }
  norm_map' Y := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,PiLp.inner_apply,PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro v _
    exact I.inner_map_map (Y v) (Y v)

theorem physicalMap_apply {n D D' : ℕ} (I : Block D →ₗᵢ[ℝ] Block D')
    (Y : Physical n D) (v : Index n) : physicalMap I Y v=I (Y v) := rfl

theorem physicalMap_compress {n D D' : ℕ} (I : Block D →ₗᵢ[ℝ] Block D')
    (R : ℝ) (Y : Physical n D) :
    RadialWrapper.compress R (physicalMap I Y)=physicalMap I (RadialWrapper.compress R Y) := by
  simp only [RadialWrapper.compress,RadialWrapper.scale,(physicalMap I).norm_map,map_smul]

theorem completed_endpoint_inner {n D K : ℕ} (r : Index n → ℕ)
    (columns : Index n → Fin (K+1) → Block D) (Q : Rotations n (completionDimension D K))
    (hQ : ∀ i k,Q i (commonCompletionFrame D K (basis k))=
      completionBlockEquiv D K (completedColumn K (r i) (columns i)
        (LinearIsometryEquiv.refl ℝ (Space K)).toLinearIsometry k))
    (i : Index n) (k : Fin (K+1)) (Y : Physical n D) :
    ⟪endpointFrame Q (commonCompletionFrame D K) i (basis k),physicalMap (completionBlockInclusion D K) Y⟫=
      if k.val<r i then ⟪columns i k,Y i⟫ else 0 := by
  rw [endpointFrame_inner,physicalMap_apply,hQ]
  change ⟪completionBlockEquiv D K _,completionBlockEquiv D K (pack (Y i) 0)⟫=_
  rw [(completionBlockEquiv D K).inner_map_map]
  by_cases hk : k.val<r i <;> simp [completedColumn,hk,WithLp.prod_inner_apply,pack]

end Bilevel.EndpointTransportResponse
