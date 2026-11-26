import Bilevel.ChiCarrierAncestorLocality

/-! Actual child release support. A terminal is either already contained
in the disclosed prefix or its release is exactly flat. -/
noncomputable section
namespace Bilevel.ChiRecursive.Node
open ChiBoundedChain
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem release_gradient_mem (D : Node E) (r : ℕ) (hR : 0<D.radius)
    (hhp : 0<D.parentWidth) (hwidth : D.width≤D.parentWidth)
    (u : E) (W : Submodule ℝ E) (hu : u∈W)
    (hU : ∀ k : Fin (D.n+1),k.val < r → D.frame (basis k)∈W)
    (hz : ∀ k : Fin (D.n+1),r ≤ k.val → |D.coordinates u k|≤D.width/4) :
    gradient D.release u∈W := by
  by_cases ht : D.n < r
  · apply WrappedPrefixLocality.carried_gradient_mem D.n r D.radius hR D.frame
      (fun z => releaseGate (z (Fin.last D.n)/D.parentWidth))
      ((releaseGate_contDiff.comp ((EuclideanSpace.proj (𝕜:=ℝ) (Fin.last D.n)).contDiff.div_const
        D.parentWidth) : ContDiff ℝ 3 _).differentiable (by norm_num)) u W hu hU
    intro k hk
    have := k.isLt
    omega
  · rw [D.release_gradient_zero_of_blind hhp hwidth u (hz (Fin.last D.n) (by simp;omega))]
    exact W.zero_mem

end Bilevel.ChiRecursive.Node
