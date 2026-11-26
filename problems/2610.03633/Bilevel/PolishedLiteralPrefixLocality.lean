import Bilevel.PolishedLiteralResidual
import Bilevel.PolishedLiteralEndgame
import Bilevel.ChiPrefixClosedJet

/-! Prefix locality of the actual one-sided macro chain after its signed
release correction. This is the cancellation that prevents the exact upper
oracle from disclosing a macro frontier before a successful lower sample. -/
noncomputable section
open scoped Topology
open Filter
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ChiPrefixEvaluation ZeroChainPotential

theorem literal_penalty_flat {t : ℝ} (ht : -(1/2:ℝ)≤t) : penalty t=0 :=
  ChiOuter.penalty_flat ht

theorem literal_selectorDerivative_basis_small {n : ℕ} (i j : Fin (n+1)) (z : Space n)
    (hj : |z j|≤1/4) : selectorDerivative n i z (basis j)=0 := by
  refine Fin.cases (maskDerivative_basis_small 0 j z hj) (fun k => ?_) i
  simp only [selectorDerivative,Fin.cases_succ,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,maskDerivative_basis_small k.succ j z hj,smul_zero,add_zero]
  by_cases he : j=k.castSucc
  · have h0 : deriv psi (z k.castSucc)=0 := by
      rw [← he]
      exact psi_deriv_zero (by linarith [(abs_le.mp hj).2])
    simp [h0]
  · simp [basis,he,Ne.symm he]

theorem literal_selector_gradient_small (n : ℕ) (i k : Fin (n+1)) (z : Space n)
    (hk : |z k|≤1/4) : gradient (selector n i) z k=0 := by
  rw [ZeroChainResidualLocality.gradient_coordinate_eq (selector_hasFDerivAt n i z)]
  exact literal_selectorDerivative_basis_small i k z hk

def incoming (n : ℕ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  Fin.cases (-phi (z 0)) (fun k => edge (z k.castSucc) (z k.succ)) i

def closedValue (n : ℕ) (q : Fin (n+1) → ℝ) (z : Space n) : ℝ :=
  value n z+∑ i : Fin (n+1),residualTerm n i z*(q i-1)

theorem value_sum_incoming (n : ℕ) (z : Space n) :
    value n z=(∑ i : Fin (n+1),incoming n i z)+∑ i : Fin (n+1),penalty (z i) := by
  rw [Fin.sum_univ_succ]
  rfl

theorem residualTerm_eq_incoming (n : ℕ) (i : Fin (n+1)) (z : Space n) :
    residualTerm n i z=incoming n i z*tailMask i z := by
  refine Fin.cases ?_ (fun k => ?_) i
  · simp only [residualTerm,selector,incoming,Fin.cases_zero]
    ring
  · simp only [residualTerm,selector,incoming,Fin.cases_succ,edge]
    ring

theorem selector_prefix_value (n r : ℕ) (i : Fin (n+1)) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|≤1/4) :
    selector n i z=selector n i (retain n r z) :=
  value_eq_retain _ ((selector_contDiff n 3 i).differentiable (by norm_num))
    (fun w hw k hk => literal_selector_gradient_small n i k w (hw k hk)) z hz

theorem incoming_prefix_value (n r : ℕ) (i : Fin (n+1)) (hi : i.val<r) (z : Space n) :
    incoming n i z=incoming n i (retain n r z) := by
  revert hi
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hi
    simp only [incoming,Fin.cases_zero,retain_apply,if_pos hi]
  · intro hi
    have hk : k.castSucc.val<r := by simp only [Fin.val_succ] at hi;exact (Nat.lt_succ_self _).trans hi
    simp only [incoming,Fin.cases_succ,retain_apply,if_pos hi,if_pos hk]

theorem closedValue_prefix_value (n r : ℕ) (q : Fin (n+1) → ℝ)
    (hq : ∀ i : Fin (n+1),r≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|≤1/4) :
    closedValue n q z=closedValue n q (retain n r z) := by
  have hr : ∀ k : Fin (n+1),r ≤ k.val → |retain n r z k|≤1/4 := by
    intro k hk
    rw [retain_apply,if_neg (by omega)]
    norm_num
  have hsum (w : Space n) : closedValue n q w=
      (∑ i : Fin (n+1),(incoming n i w+residualTerm n i w*(q i-1)))+
        ∑ i : Fin (n+1),penalty (w i) := by
    simp only [closedValue,value_sum_incoming,Finset.sum_add_distrib]
    ring
  rw [hsum,hsum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<r
    · rw [incoming_prefix_value n r i hi z]
      simp only [residualTerm,selector_prefix_value n r i z hz,retain_apply,if_pos hi]
    · have hil : r≤ i.val := by omega
      have hz0 (w : Space n) (hw : ∀ k : Fin (n+1),r ≤ k.val → |w k|≤1/4) :
          incoming n i w+residualTerm n i w*(q i-1)=0 := by
        rw [residualTerm_eq_incoming,tailMask_one_of_small i w
          (fun k hik => hw k (hil.trans hik)),hq i hil]
        ring
      rw [hz0 z hz,hz0 _ hr]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.val<r
    · rw [retain_apply,if_pos hi]
    · rw [literal_penalty_flat (by linarith [(abs_le.mp (hz i (by omega))).1]),
        literal_penalty_flat (by linarith [(abs_le.mp (hr i (by omega))).1])]

def closedChain (n : ℕ) (ell h : ℝ) (q : Fin (n+1) → ℝ) (z : Space n) : ℝ :=
  (ell*h^2)*closedValue n q (h⁻¹ • z)

theorem closedChain_prefix_value (n r : ℕ) (ell h : ℝ) (hh : 0<h)
    (q : Fin (n+1) → ℝ) (hq : ∀ i : Fin (n+1),r≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|≤h/4) :
    closedChain n ell h q z=closedChain n ell h q (retain n r z) := by
  unfold closedChain
  rw [closedValue_prefix_value n r q hq _
    (fun k hk => ZeroChainResidualScaled.scaled_coordinate_small h hh z k (hz k hk)),map_smul]


/-! Value invariance gives exact first jets of the retained evaluator. -/
theorem prefix_gradient_of_value {n r : ℕ} {τ : ℝ} (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hval : ∀ w : Space n,(∀ k : Fin (n+1),r ≤ k.val → |w k|≤τ) →
      f w=f (retain n r w)) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|<τ) :
    gradient f z=retain n r (gradient f (retain n r z)) := by
  have ho : IsOpen {w : Space n | ∀ k : Fin (n+1),r ≤ k.val → |w k|<τ} := by
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro k
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_lt (EuclideanSpace.proj (𝕜:=ℝ) k).continuous.abs continuous_const
  have he : f=ᶠ[𝓝 z] (f ∘ retain n r) := by
    filter_upwards [ho.mem_nhds hz] with w hw
    exact hval w (fun k hk => (hw k hk).le)
  have hg : gradient f z=gradient (f ∘ retain n r) z := by
    simp only [gradient,he.fderiv_eq]
  rw [hg,ChiPrefixEvaluation.gradient_comp_retain f hf]

theorem closedValue_contDiff (n : ℕ) (q : Fin (n+1) → ℝ) : ContDiff ℝ 3 (closedValue n q) :=
  (value_contDiff n 3).add (ContDiff.sum (fun i _ =>
    (residualTerm_contDiff n 3 i).mul contDiff_const))

theorem closedValue_prefix_gradient (n r : ℕ) (q : Fin (n+1) → ℝ)
    (hq : ∀ i : Fin (n+1),r ≤ i.val → q i=0) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|<1/4) :
    gradient (closedValue n q) z=retain n r (gradient (closedValue n q) (retain n r z)) :=
  prefix_gradient_of_value _ ((closedValue_contDiff n q).differentiable (by norm_num))
    (closedValue_prefix_value n r q hq) z hz

def normalizedCarrier (n : ℕ) (z : Space n) : ℝ := value n z-normalizedResidual n z

theorem normalizedCarrier_eq_closed (n : ℕ) (z : Space n) :
    normalizedCarrier n z=closedValue n (fun _ => 0) z-ZeroChainPotential.phi 0 := by
  simp only [normalizedCarrier,normalizedResidual,closedValue,zero_sub,sub_zero,
    mul_neg,mul_one,Finset.sum_neg_distrib]
  ring

theorem normalizedCarrier_contDiff (n : ℕ) : ContDiff ℝ 3 (normalizedCarrier n) :=
  (value_contDiff n 3).sub (normalizedResidual_contDiff n 3)

theorem normalizedCarrier_prefix_value (n r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|≤1/4) :
    normalizedCarrier n z=normalizedCarrier n (retain n r z) := by
  rw [normalizedCarrier_eq_closed,normalizedCarrier_eq_closed,
    closedValue_prefix_value n r (fun _ => 0) (fun _ _ => rfl) z hz]

theorem normalizedCarrier_prefix_gradient (n r : ℕ) (z : Space n)
    (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|<1/4) :
    gradient (normalizedCarrier n) z=retain n r (gradient (normalizedCarrier n) (retain n r z)) :=
  prefix_gradient_of_value _ ((normalizedCarrier_contDiff n).differentiable (by norm_num))
    (normalizedCarrier_prefix_value n r) z hz


/-- The physical source carrier has the same single centering constant. -/
def microCarrier (n : ℕ) (L β : ℝ) (z : Space n) : ℝ :=
  chain n L β z-residual n L β z

theorem microCarrier_eq_scaled (n : ℕ) (L β : ℝ) :
    microCarrier n L β=ZeroChainResidualScaled.scaled (normalizedCarrier n) (L*β^2) β := by
  funext z
  simp only [microCarrier,chain,residual,ZeroChainResidualScaled.scaled,normalizedCarrier]
  ring

theorem microCarrier_contDiff (n : ℕ) (L β : ℝ) : ContDiff ℝ 3 (microCarrier n L β) :=
  (chain_contDiff n L β 3).sub (residual_contDiff n 3 L β)

theorem microCarrier_prefix_value (n r : ℕ) (L β : ℝ) (hβ : 0<β) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤β/4) :
    microCarrier n L β z=microCarrier n L β (retain n r z) := by
  rw [microCarrier_eq_scaled]
  unfold ZeroChainResidualScaled.scaled
  rw [normalizedCarrier_prefix_value n r (β⁻¹ • z)
    (fun k hk => ZeroChainResidualScaled.scaled_coordinate_small β hβ z k (hz k hk)),map_smul]

/-- Actual value and ambient vector derivative are computed from a retained
prefix evaluator. This theorem is generic in the latent scalar function,
and is instantiated below for the literal carrier. -/
theorem wrapped_prefix_of_value {n r : ℕ} {τ : ℝ} (f : Space n → ℝ)
    (hf : Differentiable ℝ f)
    (hval : ∀ z : Space n,(∀ k : Fin (n+1),r≤k.val → |z k|≤τ) → f z=f (retain n r z))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (R : ℝ) (hR : 0<R) (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<τ) :
    f (WrappedChain.coordinates n R U u)=ChiPrefixEvaluation.prefixWrapped n r R U f u ∧
    gradient (f ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n r R U f) u := by
  refine ⟨hval _ (fun k hk => (hu k hk).le),?_⟩
  change gradient (f ∘ WrappedChain.coordinates n R U) u=
    gradient ((f ∘ retain n r) ∘ WrappedChain.coordinates n R U) u
  rw [WrappedPrefixLocality.carried_gradient n R hR U f hf,
    WrappedPrefixLocality.carried_gradient n R hR U (f ∘ retain n r) (hf.comp (retain n r).differentiable),
    ChiPrefixEvaluation.gradient_comp_retain f hf,
    ← prefix_gradient_of_value f hf hval (WrappedChain.coordinates n R U u) hu]

theorem microCarrier_wrapped_prefix {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (L β R : ℝ) (hβ : 0<β) (hR : 0<R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<β/4) :
    microCarrier n L β (WrappedChain.coordinates n R U u)=
      ChiPrefixEvaluation.prefixWrapped n r R U (microCarrier n L β) u ∧
    gradient (microCarrier n L β ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n r R U (microCarrier n L β)) u :=
  wrapped_prefix_of_value _ ((microCarrier_contDiff n L β).differentiable (by norm_num))
    (microCarrier_prefix_value n r L β hβ) R hR U u hu

theorem positiveReceiver_zero_core (A ν g β b : ℝ) (hβ : 0<β) {t : ℝ} (ht : t≤β/4) :
    positiveReceiver A ν g β b t=0 := by
  have hs (s : ℝ) (hs : s≤β/4) : positiveReceiverSlope A ν g β b s=0 := by
    have hg : receiverGate (s/β)=0 := receiverGate_zero ((div_le_iff₀ hβ).mpr (by linarith))
    simp only [positiveReceiverSlope,hg,mul_zero,zero_mul]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s∈Set.Iic (β/4)) => (positiveReceiver_hasDerivAt A ν g β b s).differentiableAt)
    (fun s (hs' : s∈Set.Iic (β/4)) => by
      rw [(positiveReceiver_hasDerivAt A ν g β b s).deriv,hs s hs',norm_zero])
    (convex_Iic _) (show (0:ℝ)∈Set.Iic (β/4) by change (0:ℝ)≤β/4;positivity) ht
  simpa only [positiveReceiver,primitive_zero,sub_zero,zero_mul,norm_le_zero_iff] using h


def microClosedCarrier (n : ℕ) (L β A ν g b : ℝ) (z : Space n) : ℝ :=
  microCarrier n L β z+positiveReceiver A ν g β b (z (Fin.last n))

theorem microClosedCarrier_contDiff (n : ℕ) (L β A ν g b : ℝ) :
    ContDiff ℝ 3 (microClosedCarrier n L β A ν g b) :=
  (microCarrier_contDiff n L β).add
    ((positiveReceiver_contDiff A ν g β b 3).comp (EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)).contDiff)

theorem microClosedCarrier_prefix_value (n r : ℕ) (hr : r≤n) (L β A ν g b : ℝ)
    (hβ : 0<β) (z : Space n)
    (hz : ∀ k : Fin (n+1),r≤k.val → |z k|≤β/4) :
    microClosedCarrier n L β A ν g b z=microClosedCarrier n L β A ν g b (retain n r z) := by
  have hlast : z (Fin.last n)≤β/4 := (abs_le.mp (hz _ hr)).2
  have hret : retain n r z (Fin.last n)=0 := by rw [retain_apply,if_neg (by simpa using not_lt.mpr hr)]
  unfold microClosedCarrier
  rw [microCarrier_prefix_value n r L β hβ z hz,positiveReceiver_zero_core A ν g β b hβ hlast,
    hret,positiveReceiver_zero_core A ν g β b hβ (by positivity)]

theorem microClosedCarrier_wrapped_prefix {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (hr : r≤n) (L β A ν g b R : ℝ) (hβ : 0<β) (hR : 0<R)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<β/4) :
    microClosedCarrier n L β A ν g b (WrappedChain.coordinates n R U u)=
      ChiPrefixEvaluation.prefixWrapped n r R U (microClosedCarrier n L β A ν g b) u ∧
    gradient (microClosedCarrier n L β A ν g b ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n r R U (microClosedCarrier n L β A ν g b)) u :=
  wrapped_prefix_of_value _ ((microClosedCarrier_contDiff n L β A ν g b).differentiable (by norm_num))
    (microClosedCarrier_prefix_value n r hr L β A ν g b hβ) R hR U u hu

theorem closedChain_contDiff (n : ℕ) (L β : ℝ) (q : Fin (n+1) → ℝ) :
    ContDiff ℝ 3 (closedChain n L β q) :=
  contDiff_const.mul ((closedValue_contDiff n q).comp (contDiff_id.const_smul β⁻¹))

theorem closedChain_wrapped_prefix {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (n r : ℕ) (L β R : ℝ) (hβ : 0<β) (hR : 0<R)
    (q : Fin (n+1) → ℝ) (hq : ∀ i,r ≤ i.val → q i=0)
    (U : Space n →ₗᵢ[ℝ] E) (u : E)
    (hu : ∀ k : Fin (n+1),r≤k.val → |WrappedChain.coordinates n R U u k|<β/4) :
    closedChain n L β q (WrappedChain.coordinates n R U u)=
      ChiPrefixEvaluation.prefixWrapped n r R U (closedChain n L β q) u ∧
    gradient (closedChain n L β q ∘ WrappedChain.coordinates n R U) u=
      gradient (ChiPrefixEvaluation.prefixWrapped n r R U (closedChain n L β q)) u :=
  wrapped_prefix_of_value _ ((closedChain_contDiff n L β q).differentiable (by norm_num))
    (closedChain_prefix_value n r L β hβ q hq) R hR U u hu

end Bilevel.PolishedLiteral
