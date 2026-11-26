import SecondOrder.ConservativeFeatures

open scoped Classical

namespace SecondOrder
noncomputable section

abbrev ScalarRichResponse (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] :=
  ℝ × H × (H →L[ℝ] H)

def scalarRichResponse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (x : H) : ScalarRichResponse H :=
  (f x,gradient f x,fderiv ℝ (gradient f) x)

theorem scalarRichResponse_continuous {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {f : H → ℝ} (hf : ContDiff ℝ 2 f) : Continuous (scalarRichResponse f) := by
  have hg : ContDiff ℝ 1 (gradient f) :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (show (1:WithTop ℕ∞)+1 ≤ 2 by norm_num))
  exact hf.continuous.prodMk (hg.continuous.prodMk (hg.continuous_fderiv (by norm_num)))

def conservativeExtendHidden {T k : ℕ} {Θ : Type*} (θ₀ : Θ) (past : Fin k → Θ)
    (i : Fin (T+1)) : Θ := if hi : i.val<k then past ⟨i.val,hi⟩ else θ₀

def conservativeExtendCoefficients {T k m : ℕ} {R : ℝ}
    (past : Fin k → Fin m → SignedCoefficient R) (fresh : Fin m → SignedCoefficient R)
    (i : Fin (T+1)) : Fin m → SignedCoefficient R :=
  if hi : i.val<k then past ⟨i.val,hi⟩ else fresh

variable {T m : ℕ} {E : Fin (T+1) → Type*} {Θ : Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

namespace ConservativeFeatureData

def reply (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) {R : ℝ}
    (z : Fin (T+1) → Fin m → SignedCoefficient R) : PiLp 2 E → ScalarRichResponse (PiLp 2 E) :=
  scalarRichResponse (D.loss reg gate θ z)

def truncatedReply (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) {R : ℝ}
    (z : Fin (T+1) → Fin m → SignedCoefficient R) (k : ℕ) :
    PiLp 2 E → ScalarRichResponse (PiLp 2 E) :=
  scalarRichResponse (D.truncatedLoss reg gate θ z k)

theorem reply_truncate (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ)
    (hreg : ContDiff ℝ 2 reg) (h0 : ∀ i, ContDiff ℝ 2 (D.offset i))
    (hφ : ∀ i a, ContDiff ℝ 2 (D.feature i a)) (hgate : ∀ i θ, ContDiff ℝ 2 (gate i θ))
    (hflat : ∀ i θ y, gate i θ y=0 → gradient (gate i θ) y=0 ∧ fderiv ℝ (gradient (gate i θ)) y=0)
    {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) (k : ℕ) (x : PiLp 2 E)
    (hfuture : ∀ i, k ≤ i.val → gate i (θ i) (x i)=0) :
    D.reply reg gate θ z x=D.truncatedReply reg gate θ z k x := by
  have hj := conservativeChain_truncate_jet reg (fun i => D.population i (θ i))
    (fun i => D.sample i (z i)) (fun i => gate i (θ i)) hreg
    (fun i => D.population_contDiff h0 hφ i (θ i)) (fun i => D.sample_contDiff h0 hφ i (z i))
    (fun i => hgate i (θ i)) (fun i => hflat i (θ i)) k x hfuture
  exact Prod.ext hj.value (Prod.ext hj.gradient_eq hj.hessian_eq)

theorem truncatedReply_prefix_invariant (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ θ' : Fin (T+1) → Θ) {R : ℝ}
    (z z' : Fin (T+1) → Fin m → SignedCoefficient R) {k : ℕ} (hk : k ≤ T)
    (hθ : ∀ i, i.val<k → θ i=θ' i) (hz : ∀ i, i.val ≤ k → z i=z' i) (x : PiLp 2 E) :
    D.truncatedReply reg gate θ z k x=D.truncatedReply reg gate θ' z' k x := by
  unfold truncatedReply
  rw [D.truncatedLoss_prefix_invariant reg gate θ θ' z z' hk hθ hz]

/-- No fresh hidden variable is an argument of this response function. -/
def frontierReply (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ : Θ) {k : ℕ} (pastθ : Fin k → Θ)
    {R : ℝ} (x : PiLp 2 E)
    (a : (Fin k → Fin m → SignedCoefficient R) × (Fin m → SignedCoefficient R)) :
    ScalarRichResponse (PiLp 2 E) :=
  D.truncatedReply reg gate (conservativeExtendHidden θ₀ pastθ)
    (conservativeExtendCoefficients a.1 a.2) k x

theorem frontierReply_base_independent (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ₀ θ₁ : Θ) {k : ℕ} (pastθ : Fin k → Θ)
    (hk : k ≤ T) {R : ℝ} (x : PiLp 2 E)
    (a : (Fin k → Fin m → SignedCoefficient R) × (Fin m → SignedCoefficient R)) :
    D.frontierReply reg gate θ₀ pastθ x a=D.frontierReply reg gate θ₁ pastθ x a := by
  apply D.truncatedReply_prefix_invariant _ _ _ _ _ _ hk
  · intro i hi
    simp only [conservativeExtendHidden,dif_pos hi]
  · intro _ _
    rfl

theorem truncatedReply_frontier_map (D : ConservativeFeatureData T m E Θ) (reg : PiLp 2 E → ℝ)
    (gate : (i : Fin (T+1)) → Θ → E i → ℝ) (θ : Fin (T+1) → Θ) (θ₀ : Θ) {k : ℕ}
    (hk : k ≤ T) {R : ℝ} (z : Fin (T+1) → Fin m → SignedCoefficient R) (x : PiLp 2 E) :
    D.truncatedReply reg gate θ z k x=
      D.frontierReply reg gate θ₀ (fun i : Fin k => θ ⟨i.val,by omega⟩) x
        ((fun i : Fin k => z ⟨i.val,by omega⟩),z ⟨k,by omega⟩) := by
  apply D.truncatedReply_prefix_invariant _ _ _ _ _ _ hk
  · intro i hi
    simp only [conservativeExtendHidden,dif_pos hi]
  · intro i hi
    unfold conservativeExtendCoefficients
    split_ifs with hik
    · rfl
    · have he : i=(⟨k,by omega⟩ : Fin (T+1)) := by apply Fin.ext; change i.val=k; omega
      rw [he]

end ConservativeFeatureData
end
end SecondOrder
