import FullJet.ChainSmoothness
import FullJet.Model

open scoped ContDiff BigOperators

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {T : ℕ}

/-- A closed concrete link is flat at every order, including at the gate boundary. -/
theorem chainLink_flat_at (θ s : Fin (T + 1) → E) (ρ : ℝ)
    (j : Fin T) (x : BlockSpace T E)
    (hx : alignment (θ j.castSucc) (x j.castSucc) ≤ 5 / 32) :
    FlatAt (chainLink θ s ρ j) x := by
  have hu := (alignment_contDiff (θ j.castSucc)).comp
    (blockProjection (E := E) j.castSucc).contDiff
  have hv := (rowFactor_contDiff (s j.succ) ρ).comp
    (adjacentProjection (E := E) j).contDiff
  exact flatAt_mul ((gate_contDiff _ _).comp hu) hv
    (flatAt_comp (gate_contDiff _ _) hu (explicit_gate_flat hx))

/-- Keep any selected set of links, while retaining the first row and regularizer. -/
noncomputable def truncatedComponentChain (θ s : Fin (T + 1) → E) (ρ lam : ℝ)
    (retained : Finset (Fin T)) (x : BlockSpace T E) : ℝ :=
  -(ρ⁻¹ * alignment (s 0) (x 0)) - ∑ j ∈ retained, chainLink θ s ρ j x + lam / 2 * ‖x‖ ^ 2

theorem truncatedComponentChain_contDiff (θ s : Fin (T + 1) → E) (ρ lam : ℝ)
    (retained : Finset (Fin T)) :
    ContDiff ℝ ∞ (truncatedComponentChain θ s ρ lam retained) :=
  ((contDiff_const.mul ((alignment_contDiff (s 0)).comp
    (blockProjection (E := E) (T := T) 0).contDiff)).neg.sub
    (ContDiff.sum (fun j hj => chainLink_contDiff θ s ρ j))).add
      (contDiff_const.mul (contDiff_norm_sq ℝ))

/-- Removing all closed links leaves the actual Fréchet derivatives unchanged.
There is no bound on the query point, and order zero is included. -/
theorem componentChain_iteratedFDeriv_eq_truncated (θ s : Fin (T + 1) → E)
    (ρ lam : ℝ) (retained : Finset (Fin T)) (x : BlockSpace T E)
    (hclosed : ∀ j ∉ retained, alignment (θ j.castSucc) (x j.castSucc) ≤ 5 / 32)
    (r : ℕ) :
    iteratedFDeriv ℝ r (componentChain θ s ρ lam) x =
      iteratedFDeriv ℝ r (truncatedComponentChain θ s ρ lam retained) x := by
  let removed : BlockSpace T E → ℝ := fun y => ∑ j ∈ retainedᶜ, -(chainLink θ s ρ j y)
  have hr : ContDiff ℝ ∞ removed := ContDiff.sum (fun j hj => (chainLink_contDiff θ s ρ j).neg)
  have hflat : FlatAt removed x := by
    apply flatAt_sum retainedᶜ (fun j hj => (chainLink_contDiff θ s ρ j).neg)
    intro j hj k
    have h := chainLink_flat_at θ s ρ j x (hclosed j (Finset.mem_compl.mp hj)) k
    change iteratedFDeriv ℝ k (-(chainLink θ s ρ j)) x = 0
    rw [iteratedFDeriv_neg_apply (𝕜 := ℝ), h, neg_zero]
  have heq : componentChain θ s ρ lam =
      truncatedComponentChain θ s ρ lam retained + removed := by
    funext y
    have hsplit := retained.sum_add_sum_compl (fun j => chainLink θ s ρ j y)
    change -(ρ⁻¹ * alignment (s 0) (y 0)) - ∑ j, chainLink θ s ρ j y + lam / 2 * ‖y‖ ^ 2 =
      (-(ρ⁻¹ * alignment (s 0) (y 0)) - ∑ j ∈ retained, chainLink θ s ρ j y + lam / 2 * ‖y‖ ^ 2) +
        ∑ j ∈ retainedᶜ, -(chainLink θ s ρ j y)
    rw [← hsplit, Finset.sum_neg_distrib]
    ring
  have horder : (r : WithTop ℕ∞) ≤ ∞ := by
    exact_mod_cast (show (r : ℕ∞) ≤ ⊤ from le_top)
  rw [heq, iteratedFDeriv_add_apply (𝕜 := ℝ) (x := x) (i := r)
    ((truncatedComponentChain_contDiff θ s ρ lam retained).contDiffAt.of_le horder)
    (hr.contDiffAt.of_le horder), hflat r, add_zero]

/-- Exact equality of the value-inclusive packet returned by the component oracle. -/
theorem componentChain_fullJet_eq_truncated (θ s : Fin (T + 1) → E)
    (ρ lam : ℝ) (retained : Finset (Fin T)) (x : BlockSpace T E)
    (hclosed : ∀ j ∉ retained, alignment (θ j.castSucc) (x j.castSucc) ≤ 5 / 32)
    (p : ℕ) :
    fullJet p (componentChain θ s ρ lam) x =
      fullJet p (truncatedComponentChain θ s ρ lam retained) x := by
  funext r
  exact componentChain_iteratedFDeriv_eq_truncated θ s ρ lam retained x hclosed r.val

/-- The truncated function depends only on the first row and the direction/row
pairs on retained links. All other hidden data can be replaced freely. -/
theorem truncatedComponentChain_eq_of_visible_data
    (θ s θ' s' : Fin (T + 1) → E) (ρ lam : ℝ) (retained : Finset (Fin T))
    (hhead : s 0 = s' 0)
    (hθ : ∀ j ∈ retained, θ j.castSucc = θ' j.castSucc)
    (hs : ∀ j ∈ retained, s j.succ = s' j.succ) :
    truncatedComponentChain θ s ρ lam retained =
      truncatedComponentChain θ' s' ρ lam retained := by
  funext y
  unfold truncatedComponentChain
  rw [hhead]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  unfold chainLink
  rw [hθ j hj, hs j hj]

/-- Two chains with the same visible data give exactly the same full oracle
reply when their unretained gates are closed at the query point. -/
theorem componentChain_fullJet_eq_of_visible_data
    (θ s θ' s' : Fin (T + 1) → E) (ρ lam : ℝ) (retained : Finset (Fin T))
    (hhead : s 0 = s' 0)
    (hθ : ∀ j ∈ retained, θ j.castSucc = θ' j.castSucc)
    (hs : ∀ j ∈ retained, s j.succ = s' j.succ) (x : BlockSpace T E)
    (hclosed : ∀ j ∉ retained, alignment (θ j.castSucc) (x j.castSucc) ≤ 5 / 32)
    (hclosed' : ∀ j ∉ retained, alignment (θ' j.castSucc) (x j.castSucc) ≤ 5 / 32)
    (p : ℕ) :
    fullJet p (componentChain θ s ρ lam) x = fullJet p (componentChain θ' s' ρ lam) x := by
  rw [componentChain_fullJet_eq_truncated θ s ρ lam retained x hclosed p,
    componentChain_fullJet_eq_truncated θ' s' ρ lam retained x hclosed' p,
    truncatedComponentChain_eq_of_visible_data θ s θ' s' ρ lam retained hhead hθ hs]

end FullJet
