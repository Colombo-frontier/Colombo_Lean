import HiddenSigns254
import ProductMarginal254

noncomputable section
open scoped BigOperators
namespace Paper254

def uniformFinite (ι : Type*) [Fintype ι] [Nonempty ι] : ProbabilityWeights ι where
  weight _ := 1/(Fintype.card ι : ℝ)
  nonneg _ := by positivity
  total := by
    have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hc]

theorem uniformFinite_equiv {ι : Type*} [Fintype ι] [Nonempty ι]
    (e : ι ≃ ι) (F : ι → ℝ) :
    finiteExpectation (uniformFinite ι) (fun s => F (e s)) = finiteExpectation (uniformFinite ι) F := by
  unfold finiteExpectation uniformFinite
  simp only [← Finset.mul_sum]
  rw [e.sum_comp]

theorem finiteExpectation_mono {ι : Type*} [Fintype ι] (p : ProbabilityWeights ι)
    (F G : ι → ℝ) (h : ∀ i, F i ≤ G i) : finiteExpectation p F ≤ finiteExpectation p G := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (p.nonneg i))

def hiddenRisk {κ : Type*} [DecidableEq κ] (n : ℕ) (θ : ℝ) (hθ : |θ| ≤ 1)
    (query : Fin n → κ) (g : κ) (x : (Fin n → Bool) → ℝ) (s : κ → Bool) : ℝ :=
  finiteExpectation (productWeights (fun t => signObservation θ hθ s (query t)))
    (fun ω => (x ω-signedMean θ (s g))^2)

theorem hidden_sign_pair_risk {κ : Type*} [DecidableEq κ] (n : ℕ)
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin n → κ) (g : κ)
    (hinfo : (∑ t : Fin n, if query t = g then θ^2 else 0) ≤ 1/32)
    (x : (Fin n → Bool) → ℝ) (s : κ → Bool) :
    θ^2/2 ≤ (hiddenRisk n θ hθ query g x s+hiddenRisk n θ hθ query g x (flipSign g s))/2 := by
  have ha := hidden_sign_prefix_affinity n θ hθ s g query
  have hh := affinity_risk_half
    (productWeights (fun t => signObservation θ hθ s (query t)))
    (productWeights (fun t => signObservation θ hθ (flipSign g s) (query t)))
    (signedMean θ (s g)) x (by linarith)
  rw [signedMean_sq] at hh
  unfold hiddenRisk finiteExpectation
  simp only [flipSign, Function.update_self, signedMean_not, sub_neg_eq_add]
  rw [Finset.sum_add_distrib] at hh
  exact hh

theorem hidden_sign_estimation_risk {κ : Type*} [Fintype κ] [DecidableEq κ] (n : ℕ)
    (θ : ℝ) (hθ : |θ| ≤ 1) (query : Fin n → κ) (g : κ)
    (hinfo : (∑ t : Fin n, if query t = g then θ^2 else 0) ≤ 1/32)
    (x : (Fin n → Bool) → ℝ) :
    θ^2/2 ≤ finiteExpectation (uniformFinite (κ → Bool)) (hiddenRisk n θ hθ query g x) := by
  let R := hiddenRisk n θ hθ query g x
  let p := uniformFinite (κ → Bool)
  have hp := finiteExpectation_mono p (fun _ => θ^2/2)
    (fun s => (R s+R (flipSign g s))/2)
    (fun s => hidden_sign_pair_risk n θ hθ query g hinfo x s)
  rw [finiteExpectation_const] at hp
  let e : (κ → Bool) ≃ (κ → Bool) := (flipSign_involutive g).toPerm
  have he : finiteExpectation p (fun s => R (flipSign g s)) = finiteExpectation p R :=
    uniformFinite_equiv e R
  have hh : finiteExpectation p (fun s => (R s+R (flipSign g s))/2) = finiteExpectation p R := by
    unfold finiteExpectation at he ⊢
    simp_rw [← mul_div_assoc, mul_add]
    rw [← Finset.sum_div, Finset.sum_add_distrib, he]
    ring
  rwa [hh] at hp

end Paper254
#print axioms Paper254.hidden_sign_estimation_risk
