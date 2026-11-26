import GradientHessian.HigherHierarchyRegularityStep

/-! The public offsets and all newly introduced derivatives in the actual
recursive residual. These bounds retain the selected-child top coefficient. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
open ScaledJets CouplingCost
open scoped BigOperators

def offsetConstant : ℝ := 512*weightConstant + 64*(8*profileConstant)^8
theorem offsetConstant_pos : 0 < offsetConstant := by
  have hw := weightConstant_pos
  have hp := profileConstant_pos
  unfold offsetConstant
  positivity

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def publicOffset (S w : ℝ) (c : Fin 8 → E) (Z : Layer F E) : ℝ :=
  (∑ i, InnerSelector.weight (nodePorts w c Z) i * ((i.val:ℝ)*S)) + 8*S*∏ i, nodePorts w c Z i

theorem scaledJets_add {f g : Layer F E → ℝ} {C D r : ℝ}
    (hf : Bound f C r) (hg : Bound g D r) : Bound (fun x => f x+g x) (C+D) r := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_⟩
  intro n hn Z
  exact (Inner.norm_iteratedFDeriv_add_le hf.smooth hg.smooth hn Z).trans
    ((add_le_add (hf.norm_le n hn Z) (hg.norm_le n hn Z)).trans_eq (by rw [add_div]))

theorem publicOffset_scaledJets {S w : ℝ} (hS : 0 ≤ S) (hw : 0 < w) (c : Fin 8 → E) :
    Bound (publicOffset S w c : Layer F E → ℝ) (offsetConstant*S) w := by
  have hconst (i : Fin 8) : Bound (fun _ : Layer F E => (i.val:ℝ)*S) (8*S) w := by
    apply constant hw
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hS)]
    apply mul_le_mul_of_nonneg_right _ hS
    exact_mod_cast i.isLt.le
  have hterms := finset_sum (Finset.univ : Finset (Fin 8))
    (fun (i : Fin 8) (Z : Layer F E) => InnerSelector.weight (nodePorts w c Z) i * ((i.val:ℝ)*S)) hw
    (mul_nonneg (mul_nonneg (by norm_num) weightConstant_pos.le) (mul_nonneg (by norm_num) hS))
    (fun i _ => (weight_scaledJets (F := F) hw c i).mul (hconst i) hw)
  have hp := finset_prod (Finset.univ : Finset (Fin 8))
    (fun (i : Fin 8) (Z : Layer F E) => nodePorts w c Z i) hw
    (fun i _ => nodePort_scaledJets (F := F) hw c i)
  have ht := (constant (F := Layer F E) hw (c := 8*S) (C := 8*S)
    (by rw [abs_of_nonneg (mul_nonneg (by norm_num) hS)])).mul hp hw
  convert scaledJets_add hterms ht using 1
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, offsetConstant]
  ring

theorem nodeResidual_eq_components (Q : F → ℝ) (f o : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) : nodeResidual Q f o S R w c = fun Z =>
      selectedChildren w c (fun i x => f i x-Q x) Z - publicOffset S w c Z -
        CouplingCost.coupling R w c o Z + nodePerturbation R w c Z := by
  funext Z
  rw [nodeResidual_eq]
  simp only [nodeSelected, FirstHeightSelector.select_eq_inner, InnerSelector.select_eq_weighted_sum,
    selectedChildren, nodePayload, publicOffset, CouplingCost.coupling, CouplingCost.term]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

theorem childScale_div_bound {w b A : ℝ} (hw : 0 < w) (hb : 0 < b)
    (hwb : w ≤ 3*b) (hA : 0 ≤ A) {n : ℕ} (hn : n ≤ 3) : A/b^n ≤ 27*A/w^n := by
  apply (div_le_div_iff₀ (pow_pos hb n) (pow_pos hw n)).mpr
  have hp : w^n ≤ 27*b^n := by
    calc w^n ≤ (3*b)^n := pow_le_pow_left₀ hw.le hwb n
         _ = 3^n*b^n := mul_pow _ _ _
         _ ≤ 27*b^n := by
           apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb.le n)
           calc (3:ℝ)^n ≤ 3^3 := pow_le_pow_right₀ (by norm_num) hn
                _ = _ := by norm_num
  have h := mul_le_mul_of_nonneg_left hp hA
  nlinarith

variable [CompleteSpace E]

theorem nodeResidual_derivative_bound {S R w b : ℝ} (hS : 0 ≤ S) (hw : 0 < w) (hb : 0 < b)
    (hs : 16*w ≤ R) (hbw : b ≤ 4*w) (hwb : w ≤ 3*b)
    (Q : F → ℝ) (f o : Fin 8 → F → ℝ) (hQ : ContDiff ℝ 3 Q)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (ho : ∀ i, Bound (o i) profileConstant b)
    (c : Fin 8 → E) (hc : ∀ i, ‖c i‖ = R) (Z : Layer F E) {n : ℕ} (hn : n ≤ 3) :
    ‖iteratedFDeriv ℝ n (nodeResidual Q f o S R w c) Z‖ ≤
      ‖iteratedFDeriv ℝ n (selectedChildren w c (fun i x => f i x-Q x)) Z‖ +
      (offsetConstant*S + 27*couplingConstant*R + 8*profileConstant*w)/w^n := by
  have hR : 0 < R := by linarith
  have hsel := selectedChildren_contDiff hw c (fun i x => f i x-Q x) (fun i => (hf i).sub hQ)
  have hoff := publicOffset_scaledJets (F := F) hS hw c
  have hcouple := coupling_scaledJets hw hb hs hbw c hc o ho
  have hself := nodePerturbation_scaledJets (F := F) hw (by linarith : w ≤ R) c
  have hn' : (n : WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn
  rw [nodeResidual_eq_components]
  have h := Inner.norm_iteratedFDeriv_add_le ((hsel.sub hoff.smooth).sub hcouple.smooth) hself.smooth hn Z
  have h1 := LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le
    ((hsel.sub hoff.smooth).of_le hn').contDiffAt (hcouple.smooth.of_le hn').contDiffAt (x := Z)
  have h2 := LocalizedProductDerivatives.norm_iteratedFDeriv_sub_le
    (hsel.of_le hn').contDiffAt (hoff.smooth.of_le hn').contDiffAt (x := Z)
  have hcB := (hcouple.norm_le n hn Z).trans
    (childScale_div_bound hw hb hwb (mul_nonneg couplingConstant_pos.le hR.le) hn)
  have hsB := hself.norm_le n hn Z
  have hoB := hoff.norm_le n hn Z
  apply (h.trans (add_le_add (h1.trans (add_le_add_right h2 _)) le_rfl)).trans
  have hall := add_le_add (add_le_add (add_le_add_left hoB
    ‖iteratedFDeriv ℝ n (selectedChildren w c (fun i x => f i x-Q x)) Z‖) hcB) hsB
  convert hall using 1; ring

end GradientHessian.HigherHierarchy
