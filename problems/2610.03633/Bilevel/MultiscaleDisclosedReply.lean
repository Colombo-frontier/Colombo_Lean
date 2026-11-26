import Bilevel.MultiscaleDisclosedPotentials
import Bilevel.MultiscaleOriginalExecution

/-! The literal full reply from the old store and the current successful
new store. The current query is fixed before that coin is read. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open scoped Topology
namespace Bilevel.MultiscaleMean
open ZeroChain CompensatedMean
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace Parameters
variable {n : ℕ} (P : Parameters (E:=E) n)

def disclosedSample (p : ℝ) (r s : ℕ) (old new : Fin (n+1) → E) (coin : Bool) (x : E) (y : LowerSpace E) : ℝ :=
  let inactive := P.disclosedLower false r old x y
  inactive+(if coin then p⁻¹ else 0)*(P.disclosedLower true s new x y-inactive)

def disclosedReply (p : ℝ) (r s : ℕ) (old new : Fin (n+1) → E) (q : InnerQuery E) (coin : Bool) : InnerReply E :=
  ((0,gradient (P.disclosedUpper r old q.1) q.2),
    (-P.L • uProj E q.2,gradient (P.disclosedSample p r s old new coin q.1) q.2))

theorem sample_disclosed_germ (p : ℝ) (r : ℕ) (old new : Fin (n+1) → E) (coin : Bool)
    (hold : ∀ k : Fin (n+1),k.val<r → old k=P.U (basis k))
    (hnew : coin=true → ∀ k : Fin (n+1),k.val<r+1 → new k=P.U (basis k))
    (x : E) (y : LowerSpace E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n P.R P.U (uProj E y) k|<P.signalResolution) :
    (fun z => P.sampleLower p x z coin)=ᶠ[𝓝 y]
      P.disclosedSample p r (r+if coin then 1 else 0) old new coin x := by
  have hi := P.inactive_lower_disclosed_germ r old hold x y hu
  cases coin with
  | false =>
    filter_upwards [hi] with z hz
    simpa only [sampleLower,BernoulliOracle.sample,disclosedSample,Bool.false_eq_true,
      if_false,zero_smul,add_zero,zero_mul,Nat.add_zero] using hz
  | true =>
    have ha := P.active_lower_disclosed_germ r new (hnew rfl) x y hu
    filter_upwards [hi,ha] with z hz hza
    simp only [sampleLower,BernoulliOracle.sample,disclosedSample,if_true,smul_eq_mul]
    rw [←hz,←hza]
    simp only [inactiveLower]
    ring

theorem original_eq_disclosed_reply (p : ℝ) (r : ℕ) (old new : Fin (n+1) → E) (coin : Bool)
    (hold : ∀ k : Fin (n+1),k.val<r → old k=P.U (basis k))
    (hnew : coin=true → ∀ k : Fin (n+1),k.val<r+1 → new k=P.U (basis k))
    (q : InnerQuery E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n P.R P.U (uProj E q.2) k|<P.signalResolution) :
    innerOriginalReply P p q coin=P.disclosedReply p r (r+if coin then 1 else 0) old new q coin := by
  have hu' := (P.upper_disclosed_germ r old hold q.1 q.2 hu).gradient_eq
  have hg' := (P.sample_disclosed_germ p r old new coin hold hnew q.1 q.2 hu).gradient_eq
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · exact (P.data.upper_hasGradientY q.1 q.2).gradient.symm.trans hu'
  · apply Prod.ext
    · rfl
    · exact (P.sampleLower_hasGradientY p q.1 q.2 coin).gradient.symm.trans hg'

def withFrame (V : Space n →ₗᵢ[ℝ] E) : Parameters (E:=E) n := { P with U:=V }

omit [CompleteSpace E] in
theorem disclosedUpper_withFrame (V : Space n →ₗᵢ[ℝ] E) :
    (P.withFrame V).disclosedUpper=P.disclosedUpper := rfl

omit [CompleteSpace E] in
theorem disclosedLower_withFrame (V : Space n →ₗᵢ[ℝ] E) :
    (P.withFrame V).disclosedLower=P.disclosedLower := rfl

theorem disclosedReply_withFrame (V : Space n →ₗᵢ[ℝ] E) :
    (P.withFrame V).disclosedReply=P.disclosedReply := rfl

end Parameters
end Bilevel.MultiscaleMean
