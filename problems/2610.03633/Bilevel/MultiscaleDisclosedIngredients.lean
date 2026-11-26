import Bilevel.DisclosedScalarGerm
import Bilevel.MultiscalePrefixLocality

/-! Actual macro-free residuals evaluated from finite disclosed columns.
Inactive ingredients use the old prefix; the residual uses one new column. -/
noncomputable section
set_option autoImplicit false
open scoped Topology
namespace Bilevel.MultiscaleMean
open ZeroChain ZeroChainSchedule ZeroChainResidualScaled ZeroChainFlatteningBounds
  WrappedChain ChiPrefixEvaluation RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E:=E) n)

def disclosedResidual (r : ℕ) (columns : Fin (n+1) → E) : E → ℝ :=
  disclosedEvaluator n r P.R columns (ZeroChainResidualScaled.R n P.amplitude P.β)

def disclosedFlat (δ : ℝ) (r : ℕ) (columns : Fin (n+1) → E) : E → ℝ :=
  disclosedEvaluator n r P.R columns (flattenedResidual n P.amplitude P.β δ)

def disclosedRevealed (r : ℕ) (columns : Fin (n+1) → E) (u : E) : ℝ :=
  disclosedEvaluator n r P.R columns (A n P.amplitude P.β) u+bowl P.ν P.R u

theorem residual_disclosed_germ (r : ℕ) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<r+1 → columns k=P.U (basis k))
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n P.R P.U u k|<P.signalResolution) :
    P.residual=ᶠ[𝓝 u] P.disclosedResidual (r+1) columns := by
  apply disclosedEvaluator_actual_germ P.R columns P.U hcols
    (ZeroChainResidualScaled.R n P.amplitude P.β)
    ((R_contDiff _ _ _).differentiable (by norm_num)) _ u hu
  intro w hw k hk
  apply R_gradient_support n r P.amplitude P.β P.β_pos w _ k hk
  intro j hj
  exact (hw j hj).trans (P.signalResolution_small.trans (by linarith [P.β_pos]))

theorem flat_disclosed_germ (δ : ℝ) (hδ : P.signalResolution≤δ)
    (r s : ℕ) (hrs : r≤s) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<s → columns k=P.U (basis k))
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n P.R P.U u k|<P.signalResolution) :
    (flattenedResidual n P.amplitude P.β δ ∘ coordinates n P.R P.U)=ᶠ[𝓝 u]
      P.disclosedFlat δ s columns := by
  apply disclosedEvaluator_actual_germ P.R columns P.U hcols _
    ((flattenedResidual_contDiff _ _ _ _).differentiable (by norm_num)) _ u hu
  intro w hw k hk
  exact flattened_gradient_coordinate_zero n P.amplitude P.β δ
    (P.signalResolution_pos.trans_le hδ) w k ((hw k (hrs.trans hk)).trans hδ)

theorem inactive_disclosed_germ (r : ℕ) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<r → columns k=P.U (basis k))
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n P.R P.U u k|<P.signalResolution) :
    P.inactiveResidual=ᶠ[𝓝 u] P.disclosedFlat P.signalResolution r columns :=
  P.flat_disclosed_germ _ le_rfl r r le_rfl columns hcols u hu

theorem approximation_disclosed_germ (j : ℕ) (hj : j<levels P.θ)
    (r s : ℕ) (hrs : r≤s) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<s → columns k=P.U (basis k))
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n P.R P.U u k|<P.signalResolution) :
    P.flatApproximation j=ᶠ[𝓝 u] P.disclosedFlat (resolution P.c P.β P.θ j) s columns :=
  P.flat_disclosed_germ _ (P.signalResolution_le_resolution j hj) r s hrs columns hcols u hu

theorem revealed_disclosed_germ (r : ℕ) (columns : Fin (n+1) → E)
    (hcols : ∀ k : Fin (n+1),k.val<r → columns k=P.U (basis k))
    (u : E) (hu : ∀ k : Fin (n+1),r≤k.val → |coordinates n P.R P.U u k|<P.signalResolution) :
    P.revealed=ᶠ[𝓝 u] P.disclosedRevealed r columns := by
  have hh := disclosedEvaluator_actual_germ P.R columns P.U hcols (A n P.amplitude P.β)
    ((A_contDiff _ _ _).differentiable (by norm_num)) (r:=r) (τ:=P.signalResolution)
    (fun w hw k hk => A_gradient_support n r P.amplitude P.β P.β_pos w
      (fun j hj => (hw j hj).trans (P.signalResolution_small.trans (by linarith [P.β_pos]))) k hk) u hu
  rw [P.revealed_wrapped]
  filter_upwards [hh] with v hv
  exact congrArg (fun z => z+bowl P.ν P.R v) hv

end Parameters
end Bilevel.MultiscaleMean
