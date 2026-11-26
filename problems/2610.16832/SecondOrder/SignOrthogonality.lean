import SecondOrder.DyadicIntervals
import SecondOrder.FiniteMartingale

open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def signValue (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem signValue_not (b : Bool) : signValue (!b) = -signValue b := by
  cases b <;> norm_num [signValue]

def signPrefix {M : ℕ} (i : Fin M) (w : Fin M → Bool) : Fin i.val → Bool :=
  fun k => w ⟨k.val, k.isLt.trans i.isLt⟩

/-- A displacement whose direction, size, and decision to stop can depend on
all preceding signs. Multiplication by zero encodes predictable stopping. -/
def signedInnovation {E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : (i : Fin M) → (Fin i.val → Bool) → E) (i : Fin M) (w : Fin M → Bool) : E :=
  signValue (w i) • v i (signPrefix i w)

def flipSign {M : ℕ} (j : Fin M) (w : Fin M → Bool) : Fin M → Bool :=
  Function.update w j (!w j)

theorem flipSign_involutive {M : ℕ} (j : Fin M) : Function.Involutive (flipSign j) := by
  intro w
  funext k
  by_cases hk : k=j
  · subst k
    simp [flipSign]
  · simp [flipSign, hk]

def flipSignEquiv {M : ℕ} (j : Fin M) : (Fin M → Bool) ≃ (Fin M → Bool) :=
  (flipSign_involutive j).toPerm

theorem signPrefix_flip {M : ℕ} (i j : Fin M) (hij : i ≤ j) (w : Fin M → Bool) :
    signPrefix i (flipSign j w) = signPrefix i w := by
  funext k
  have hk : (⟨k.val,k.isLt.trans i.isLt⟩ : Fin M) ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    change k.val = j.val at hv
    have hklt := k.isLt
    have hij' : i.val ≤ j.val := hij
    omega
  simp [signPrefix, flipSign, hk]

theorem signedInnovation_flip_self {E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : (i : Fin M) → (Fin i.val → Bool) → E) (i : Fin M) (w : Fin M → Bool) :
    signedInnovation v i (flipSign i w) = -signedInnovation v i w := by
  unfold signedInnovation
  rw [signPrefix_flip i i le_rfl]
  simp [flipSign]

theorem signedInnovation_flip_later {E : Type*} [AddCommGroup E] [Module ℝ E] {M : ℕ}
    (v : (i : Fin M) → (Fin i.val → Bool) → E) (i j : Fin M) (hij : i < j)
    (w : Fin M → Bool) : signedInnovation v i (flipSign j w) = signedInnovation v i w := by
  unfold signedInnovation
  rw [signPrefix_flip i j hij.le]
  simp [flipSign, ne_of_lt hij]

theorem signedInnovation_orthogonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {M : ℕ}
    (v : (i : Fin M) → (Fin i.val → Bool) → E) (i j : Fin M) (hij : i ≠ j) :
    uniformMean (fun w => ⟪signedInnovation v i w,signedInnovation v j w⟫_ℝ) = 0 := by
  have hordered (i j : Fin M) (hij : i < j) :
      uniformMean (fun w => ⟪signedInnovation v i w,signedInnovation v j w⟫_ℝ) = 0 := by
    have he := uniformMean_equiv (flipSignEquiv j)
      (fun w => ⟪signedInnovation v i w,signedInnovation v j w⟫_ℝ)
    change uniformMean (fun w => ⟪signedInnovation v i (flipSign j w),
      signedInnovation v j (flipSign j w)⟫_ℝ) = _ at he
    simp only [signedInnovation_flip_later v i j hij, signedInnovation_flip_self,
      inner_neg_right] at he
    have hneg : uniformMean (fun w => -⟪signedInnovation v i w,signedInnovation v j w⟫_ℝ) =
      -uniformMean (fun w => ⟪signedInnovation v i w,signedInnovation v j w⟫_ℝ) := by
      simp [uniformMean, pmfMean, Finset.sum_neg_distrib]
    rw [hneg] at he
    linarith
  rcases lt_or_gt_of_ne hij with h|h
  · exact hordered i j h
  · simpa only [real_inner_comm] using hordered j i h

/-- The dyadic energy bound for an actual adaptive sign experiment, including
predictable stopping encoded in v. No orthogonality assumption remains. -/
theorem adaptive_sign_dyadic_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M L q : ℕ)
    (a : Fin M → (Fin M → Bool) → E)
    (v : (i : Fin M) → (Fin i.val → Bool) → E)
    (created : (Fin M → Bool) → Fin L × Fin M → Prop)
    (hs : ∀ w, (Finset.univ.filter (fun k => a k w ≠ 0)).card ≤ q) :
    uniformMean (fun w => ∑ i : Fin L × Fin M, if created w i then
      ‖∑ k ∈ dyadicBlock M i.1.val i.2, (a k w+signedInnovation v k w)‖^2 else 0) ≤
      2*(L:ℝ)*((q:ℝ)*uniformMean (fun w => ∑ k, ‖a k w‖^2) +
        uniformMean (fun w => ∑ k, ‖signedInnovation v k w‖^2)) := by
  exact selected_dyadic_energy (PMF.uniformOfFintype _) M L q a (signedInnovation v) created hs
    (signedInnovation_orthogonal v)

end
end SecondOrder
