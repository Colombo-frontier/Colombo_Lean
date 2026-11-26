import NCConcave16991.ConditionalHaarCompletion

/-! # Literal mixed forward/inverse observation fibres -/

noncomputable section

open Set

namespace NCConcave16991.MixedHaar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {I J : Type*}

def mixedObservation (v : I → E) (x : J → E) (Q : E ≃ₗᵢ[ℝ] E) :
    (I → E) × (J → E) := (fun i ↦ Q (v i), fun j ↦ Q.symm (x j))

def mixedInputs (v : I → E) (x : J → E) (Q : E ≃ₗᵢ[ℝ] E) : Sum I J → E :=
  Sum.elim v (fun j ↦ Q.symm (x j))

theorem same_mixed_iff_same_augmented (v : I → E) (x : J → E) (Q R : E ≃ₗᵢ[ℝ] E) :
    mixedObservation v x Q = mixedObservation v x R ↔
      ∀ i, Q (mixedInputs v x Q i) = R (mixedInputs v x Q i) := by
  constructor
  · intro h i
    cases i with
    | inl i => exact congrFun (congrArg Prod.fst h) i
    | inr j =>
      have hj := congrFun (congrArg Prod.snd h) j
      change Q.symm (x j) = R.symm (x j) at hj
      change Q (Q.symm (x j)) = R (Q.symm (x j))
      rw [Q.apply_symm_apply, hj, R.apply_symm_apply]
  · intro h
    apply Prod.ext
    · exact funext (fun i ↦ h (Sum.inl i))
    · funext j
      apply R.injective
      change R (Q.symm (x j)) = R (R.symm (x j))
      have hj := h (Sum.inr j)
      change Q (Q.symm (x j)) = R (Q.symm (x j)) at hj
      simpa only [Q.apply_symm_apply, R.apply_symm_apply] using hj.symm

def exposedFormalSpan (v : I → E) (x : J → E) (Q : E ≃ₗᵢ[ℝ] E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (mixedInputs v x Q))

theorem same_mixed_iff_same_span (v : I → E) (x : J → E) (Q R : E ≃ₗᵢ[ℝ] E) :
    mixedObservation v x Q = mixedObservation v x R ↔
      ∀ z ∈ exposedFormalSpan v x Q, Q z = R z := by
  rw [same_mixed_iff_same_augmented]
  constructor
  · intro h z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i,rfl⟩ := hz; exact h i
    | zero => simp
    | add a b ha hb iha ihb => simp only [map_add, iha, ihb]
    | smul a z hz ih => simp only [map_smul, ih]
  · intro h i
    exact h _ (Submodule.subset_span (Set.mem_range_self i))

/-- Every inverse reveal is an ordinary new formal input once its actual
answer has been included. This is an exact observation-fibre identity. -/
theorem mixed_fibre_coset {k : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (v : I → EuclideanSpace ℝ (Fin k)) (x : J → EuclideanSpace ℝ (Fin k))
    (Q R : Haar.OrthogonalGroup k) :
    mixedObservation v x (Haar.orthogonalLinearIsometryEquiv Q) =
        mixedObservation v x (Haar.orthogonalLinearIsometryEquiv R) ↔
      Q⁻¹ * R ∈ Haar.inputStabilizer
        (mixedInputs v x (Haar.orthogonalLinearIsometryEquiv Q)) := by
  rw [same_mixed_iff_same_augmented]
  rw [← Haar.same_inputs_iff_relative_stabilizer]
  exact funext_iff.symm

end NCConcave16991.MixedHaar
