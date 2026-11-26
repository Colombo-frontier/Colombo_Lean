import Bilevel.PolishedLiteralSelectorJets
import Bilevel.PolishedLiteralWrappedSelectors

/-! Arbitrary-order one-active-jet theorem for the manuscript's literal
exponential Psi and genuine C-infinity coordinate/energy cutoffs. The
statement includes mixed derivative orders and the cutoff boundaries. -/
noncomputable section
open scoped BigOperators ContDiff
namespace Bilevel.PolishedLiteral.AllJets
open ChiBoundedChain ChiRecursive

/-- A smooth scalar plateau is flat to every positive derivative order,
including its boundary by unique differentiability of the plateau. -/
theorem scalar_plateau_flat {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hf : ∀ k : ℕ,ContDiff ℝ k f) (hs : UniqueDiffOn ℝ s)
    (he : Set.EqOn f (fun _ => c) s) (j : ℕ) (hj : 1≤j) :
    ∀ x∈s,iteratedDeriv j f x=0 := by
  induction j with
  | zero => omega
  | succ j ih =>
      intro x hx
      rw [iteratedDeriv_succ]
      have hd := (hf (j+1)).differentiable_iteratedDeriv j (by exact_mod_cast Nat.lt_succ_self j)
      cases j with
      | zero =>
          simpa only [iteratedDeriv_zero] using
            ZeroChainResidualCutoffs.deriv_zero_of_constant_on
              ((hf 1).differentiable (by norm_num) x) hs he hx
      | succ j =>
          exact ZeroChainResidualCutoffs.deriv_zero_of_constant_on
            (hd x) hs (ih (by omega)) hx

theorem energyCutoff_flat (k : ℕ) (s : ℝ) (hs : 1≤s) :
    iteratedDeriv k ChiBoundedChain.energyCutoff s=0 := by
  cases k with
  | zero => simpa only [iteratedDeriv_zero] using ChiBoundedChain.energyCutoff_zero hs
  | succ k =>
      exact scalar_plateau_flat (fun j => ChiBoundedChain.energyCutoff_contDiff)
        (uniqueDiffOn_Ici 1) (fun _ h => ChiBoundedChain.energyCutoff_zero h)
        (k+1) (by omega) s hs

section General
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem scalar_linear_flat {f : ℝ → ℝ} (k : ℕ) (hf : ContDiff ℝ k f)
    (p : E →L[ℝ] ℝ) (x : E) (hz : iteratedDeriv k f (p x)=0) :
    iteratedFDeriv ℝ k (f ∘ p) x=0 := by
  rw [p.iteratedFDeriv_comp_right hf x le_rfl]
  apply norm_le_zero_iff.mp
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,hz,norm_zero,zero_mul]

theorem product_flat_left {f g : E → ℝ} (k : ℕ)
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (x : E)
    (hz : ∀ j,j≤k → iteratedFDeriv ℝ j f x=0) :
    iteratedFDeriv ℝ k (fun y => f y*g y) x=0 := by
  have hb := norm_iteratedFDeriv_mul_le hf hg x le_rfl
  have hs : (∑ j ∈ Finset.range (k+1),(k.choose j:ℝ)*‖iteratedFDeriv ℝ j f x‖*
      ‖iteratedFDeriv ℝ (k-j) g x‖)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hz j (by have := Finset.mem_range.mp hj;omega),norm_zero,mul_zero,zero_mul]
  rw [hs] at hb
  exact norm_le_zero_iff.mp hb

theorem product_flat_right {f g : E → ℝ} (k : ℕ)
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (x : E)
    (hz : ∀ j,j≤k → iteratedFDeriv ℝ j g x=0) :
    iteratedFDeriv ℝ k (fun y => f y*g y) x=0 := by
  have he : (fun y => f y*g y)=(fun y => g y*f y) := by funext y;ring
  rw [he]
  exact product_flat_left k hg hf x hz

/-- Vanishing of all outer jets up to the requested order forces the same
jet of a smooth composition to vanish, with no fixed order ceiling. -/
theorem composition_flat {f : E → F} {g : F → G} (k : ℕ)
    (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (x : E)
    (hz : ∀ j,j≤k → iteratedFDeriv ℝ j g (f x)=0) :
    iteratedFDeriv ℝ k (g ∘ f) x=0 := by
  let D := 1+∑ j ∈ Finset.range (k+1),‖iteratedFDeriv ℝ j f x‖
  have hD : 1≤D := le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hi (j : ℕ) (hj : 1≤j) (hjk : j≤k) : ‖iteratedFDeriv ℝ j f x‖≤D^j := by
    have hs := Finset.single_le_sum (f:=fun l => ‖iteratedFDeriv ℝ l f x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (show j<k+1 by omega))
    have hb : ‖iteratedFDeriv ℝ j f x‖≤D := by dsimp [D];linarith
    exact hb.trans (by simpa only [pow_one] using pow_le_pow_right₀ hD hj)
  have hb := norm_iteratedFDeriv_comp_le hg hf le_rfl x (C:=0) (D:=D)
    (fun j hj => by rw [hz j hj,norm_zero]) hi
  simpa only [mul_zero,zero_mul,norm_le_zero_iff] using hb

end General

theorem tailMask_flat {n : ℕ} (i : Fin (n+1)) (z : Space n)
    (hz : 1≤tailEnergy i z) (k : ℕ) : iteratedFDeriv ℝ k (tailMask i) z=0 := by
  apply composition_flat k (tailEnergy_contDiff i k) ChiBoundedChain.energyCutoff_contDiff z
  intro j hj
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,energyCutoff_flat j _ hz,norm_zero]

theorem selector_succ_flat {n : ℕ} (i : Fin n) (z : Space n)
    (hz : z i.castSucc≤1/2) (k : ℕ) : iteratedFDeriv ℝ k (PolishedLiteral.selector n i.succ) z=0 := by
  apply product_flat_left k
    ((PolishedLiteral.psi_contDiff (k:=k)).comp (EuclideanSpace.proj (𝕜:=ℝ) i.castSucc).contDiff)
    (tailMask_contDiff i.succ k) z
  intro j hj
  exact scalar_linear_flat j PolishedLiteral.psi_contDiff
    (EuclideanSpace.proj (𝕜:=ℝ) i.castSucc) z
    (ZeroChainProfiles.psi_iteratedDeriv_zero_of_le j hz)

theorem selector_large_tail_flat {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (hil : i≤l) (hz : 1/2≤|z l|) (k : ℕ) :
    iteratedFDeriv ℝ k (PolishedLiteral.selector n i) z=0 := by
  have he : 1≤tailEnergy i z := by
    have hh := ChiBoundedChain.coordinate_energy_le i l z hil
    simpa only [ChiBoundedChain.coordinateCutoff_one hz,one_pow] using hh
  revert he
  refine Fin.cases (fun he => tailMask_flat 0 z he k) (fun j he => ?_) i
  exact product_flat_right k
    ((PolishedLiteral.psi_contDiff (k:=k)).comp (EuclideanSpace.proj (𝕜:=ℝ) j.castSucc).contDiff)
    (tailMask_contDiff j.succ k) z (fun q _ => tailMask_flat j.succ z he q)

theorem selector_before_later_flat {n : ℕ} (i l : Fin (n+1)) (z : Space n)
    (k q : ℕ) (hil : i<l)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.selector n l) z≠0) :
    iteratedFDeriv ℝ k (PolishedLiteral.selector n i) z=0 := by
  revert hil hl
  refine Fin.cases (by intro h;exact False.elim (Fin.not_lt_zero i h)) (fun j => ?_) l
  intro hij hj
  have hz : 1/2<z j.castSucc := by
    by_contra! hz
    exact hj (selector_succ_flat j z hz q)
  apply selector_large_tail_flat i j.castSucc z _ (hz.le.trans (le_abs_self _)) k
  change i.val≤j.val
  change i.val<j.val+1 at hij
  omega

/-- The source's unrestricted fixed-order, mixed-order one-active-selector
jet property. There is no `k≤3` or `q≤3` hypothesis. -/
theorem selector_all_orders_unique {n : ℕ} (i l : Fin (n+1)) (z : Space n) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.selector n i) z≠0)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.selector n l) z≠0) : i=l := by
  rcases lt_trichotomy i l with h|h|h
  · exact False.elim (hi (selector_before_later_flat i l z k q h hl))
  · exact h
  · exact False.elim (hl (selector_before_later_flat l i z q k h hi))

/-- The fixed exponential Psi and both actual tail cutoffs are C-infinity.
The coordinate cutoff here is Real.smoothTransition, and the energy cutoff
is its squared complement, not a finite-order septic replacement. -/
theorem source_profiles_smooth :
    ContDiff ℝ ∞ PolishedLiteral.psi ∧
    ContDiff ℝ ∞ ChiBoundedChain.coordinateCutoff ∧
    ContDiff ℝ ∞ ChiBoundedChain.energyCutoff :=
  ⟨ZeroChainProfiles.psi_contDiff,ChiBoundedChain.coordinateCutoff_contDiff,
    ChiBoundedChain.energyCutoff_contDiff⟩

/-- A nonzero residual jet must come from a nonzero jet of the same
selector, at some no larger derivative order. -/
theorem residual_jet_has_selector {n : ℕ} (i : Fin (n+1)) (z : Space n) (k : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.residualTerm n i) z≠0) :
    ∃ j≤k,iteratedFDeriv ℝ j (PolishedLiteral.selector n i) z≠0 := by
  by_contra! hz
  apply hi
  apply product_flat_left k (PolishedLiteral.selector_contDiff n k i).neg
    ((ZeroChainPotential.phi_contDiff k).comp (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff) z
  intro j hj
  change iteratedFDeriv ℝ j (-PolishedLiteral.selector n i) z=0
  rw [iteratedFDeriv_neg_apply,hz j hj,neg_zero]

theorem residual_all_orders_unique {n : ℕ} (i l : Fin (n+1)) (z : Space n) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.residualTerm n i) z≠0)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.residualTerm n l) z≠0) : i=l := by
  obtain ⟨a,_,hai⟩ := residual_jet_has_selector i z k hi
  obtain ⟨b,_,hbl⟩ := residual_jet_has_selector l z q hl
  exact selector_all_orders_unique i l z a b hai hbl

/-- At every point there is at most one index carrying any selector or
residual jet through any prescribed finite derivative order. -/
theorem prescribed_order_one_active (n : ℕ) (z : Space n) (K : ℕ) :
    Set.Subsingleton {i : Fin (n+1) | ∃ k≤K,
      iteratedFDeriv ℝ k (PolishedLiteral.selector n i) z≠0 ∨
      iteratedFDeriv ℝ k (PolishedLiteral.residualTerm n i) z≠0} := by
  intro i hi l hl
  obtain ⟨k,_,hi⟩ := hi
  obtain ⟨q,_,hl⟩ := hl
  have his : ∃ a,iteratedFDeriv ℝ a (PolishedLiteral.selector n i) z≠0 := by
    rcases hi with hi|hi
    · exact ⟨k,hi⟩
    · obtain ⟨a,_,ha⟩ := residual_jet_has_selector i z k hi
      exact ⟨a,ha⟩
  have hls : ∃ b,iteratedFDeriv ℝ b (PolishedLiteral.selector n l) z≠0 := by
    rcases hl with hl|hl
    · exact ⟨q,hl⟩
    · obtain ⟨b,_,hb⟩ := residual_jet_has_selector l z q hl
      exact ⟨b,hb⟩
  obtain ⟨a,ha⟩ := his
  obtain ⟨b,hb⟩ := hls
  exact selector_all_orders_unique i l z a b ha hb

section Composition
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} (f : E → Space n) (hf : ∀ k : ℕ,ContDiff ℝ k f)

include hf in
theorem selector_composition_orders_unique (i l : Fin (n+1)) (x : E) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.selector n i ∘ f) x≠0)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.selector n l ∘ f) x≠0) : i=l := by
  have hlatent (a : Fin (n+1)) (s : ℕ)
      (ha : iteratedFDeriv ℝ s (PolishedLiteral.selector n a ∘ f) x≠0) :
      ∃ j≤s,iteratedFDeriv ℝ j (PolishedLiteral.selector n a) (f x)≠0 := by
    by_contra! hz
    exact ha (composition_flat s (hf s) (PolishedLiteral.selector_contDiff n s a) x hz)
  obtain ⟨a,_,ha⟩ := hlatent i k hi
  obtain ⟨b,_,hb⟩ := hlatent l q hl
  exact selector_all_orders_unique i l (f x) a b ha hb

include hf in
theorem residual_composition_orders_unique (i l : Fin (n+1)) (x : E) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.residualTerm n i ∘ f) x≠0)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.residualTerm n l ∘ f) x≠0) : i=l := by
  have hlatent (a : Fin (n+1)) (s : ℕ)
      (ha : iteratedFDeriv ℝ s (PolishedLiteral.residualTerm n a ∘ f) x≠0) :
      ∃ j≤s,iteratedFDeriv ℝ j (PolishedLiteral.residualTerm n a) (f x)≠0 := by
    by_contra! hz
    exact ha (composition_flat s (hf s) (PolishedLiteral.residualTerm_contDiff n s a) x hz)
  obtain ⟨a,_,ha⟩ := hlatent i k hi
  obtain ⟨b,_,hb⟩ := hlatent l q hl
  exact residual_all_orders_unique i l (f x) a b ha hb

end Composition

section Wrapped
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem wrappedSelector_all_orders_unique (D : Node E) (i l : Fin (D.n+1))
    (u : E) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.wrappedSelector D i) u≠0)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.wrappedSelector D l) u≠0) : i=l :=
  selector_composition_orders_unique (fun x => D.width⁻¹ • D.coordinates x)
    (fun s => (D.coordinates_contDiff s).const_smul D.width⁻¹) i l u k q hi hl

theorem wrappedResidual_all_orders_unique (D : Node E) (i l : Fin (D.n+1))
    (u : E) (k q : ℕ)
    (hi : iteratedFDeriv ℝ k (PolishedLiteral.wrappedResidual D i) u≠0)
    (hl : iteratedFDeriv ℝ q (PolishedLiteral.wrappedResidual D l) u≠0) : i=l := by
  let f := fun x => D.width⁻¹ • D.coordinates x
  have hf (s : ℕ) : ContDiff ℝ s f := (D.coordinates_contDiff s).const_smul D.width⁻¹
  have hlatent (a : Fin (D.n+1)) (s : ℕ)
      (ha : iteratedFDeriv ℝ s (PolishedLiteral.wrappedResidual D a) u≠0) :
      iteratedFDeriv ℝ s (PolishedLiteral.residualTerm D.n a ∘ f) u≠0 := by
    intro hz
    apply ha
    change iteratedFDeriv ℝ s (fun x => (D.ell*D.width^2) •
      (PolishedLiteral.residualTerm D.n a ∘ f) x) u=0
    rw [iteratedFDeriv_const_smul_apply'
      ((PolishedLiteral.residualTerm_contDiff D.n s a).comp (hf s)).contDiffAt,hz,smul_zero]
  exact residual_composition_orders_unique f hf i l u k q (hlatent i k hi) (hlatent l q hl)

end Wrapped

end Bilevel.PolishedLiteral.AllJets
