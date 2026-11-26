import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Group.Basic

/-! Partial formal audit. These are local lemmas, NOT a formalization of the
paper's main regret theorem. Analytic/probabilistic interfaces remain explicit
hypotheses where indicated. No custom axioms or admitted proofs. -/
namespace Audit254

-- B.1: scalar coefficient in the Hessian comparison.
theorem surrogate_curvature (x : ℝ) (hl : -(1/4 : ℝ) ≤ x)
    (hu : x ≤ 1/4) : (1/2 : ℝ) * (1+x)^2 ≤ 1 := by
  nlinarith [sq_nonneg (x+1/4), mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ x+1/4)]

-- B.5: numerical bound after Gaussian integration; log estimate is an interface.
theorem gaussian_mix_sign (s q ell : ℝ) (hs : 0 ≤ s)
    (hq : q ≤ 25/16) (hlog : s/(1+s) ≤ ell) :
    -ell/2 + s*q/(4*(1+s)) ≤ -7*s/(64*(1+s)) := by
  have hd : 0 < 1+s := by linarith
  have h1 := (div_le_iff₀ hd).mp hlog
  apply (le_div_iff₀ (by positivity : 0 < 64*(1+s))).mpr
  have he : (-ell/2+s*q/(4*(1+s)))*(64*(1+s)) = -32*ell*(1+s)+16*s*q := by
    field_simp
    ring
  rw [he]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hq)]

-- B.6: combine mix loss, exponential identity, and projection monotonicity.
theorem one_step_interface (lam r mix avg F R Fnext : ℝ)
    (hl : 0 < lam) (hm : r ≤ mix-avg)
    (hi : lam*(mix-avg)=F-R) (hp : Fnext ≤ R) :
    lam*r ≤ F-Fnext := by nlinarith

-- B.7: triangle inequality interface for an augmented-vector embedding.
theorem root_movement_embedding {E : Type*} [SeminormedAddCommGroup E]
    (u v : E) (a : ℝ) (h : ‖v-u‖ ≤ a) : ‖v‖ ≤ ‖u‖+a := by
  calc
    ‖v‖ = ‖u+(v-u)‖ := by congr 1; abel
    _ ≤ ‖u‖+‖v-u‖ := norm_add_le _ _
    _ ≤ ‖u‖+a := by linarith

-- B.8: the manuscript's nontrivial 'same nonnegative scalar' step.
theorem sqrt_shift (f g c a : ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hc : 0 ≤ c) (ha : 0 ≤ a)
    (h : Real.sqrt f ≤ Real.sqrt g+a) :
    Real.sqrt (f+c) ≤ Real.sqrt (g+c)+a := by
  have sf := Real.sq_sqrt hf
  have sg := Real.sq_sqrt hg
  have sfc := Real.sq_sqrt (by linarith : 0 ≤ f+c)
  have sgc := Real.sq_sqrt (by linarith : 0 ≤ g+c)
  have ng := Real.sqrt_nonneg g
  have nf := Real.sqrt_nonneg f
  have ngc := Real.sqrt_nonneg (g+c)
  have nfc := Real.sqrt_nonneg (f+c)
  have mono : Real.sqrt g ≤ Real.sqrt (g+c) := Real.sqrt_le_sqrt (by linarith)
  have hsq : f ≤ (Real.sqrt g+a)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (by positivity : 0 ≤ Real.sqrt g+a+Real.sqrt f)]
  have hsq2 : f+c ≤ (Real.sqrt (g+c)+a)^2 := by
    nlinarith [mul_nonneg ha (sub_nonneg.mpr mono)]
  nlinarith [sq_nonneg (Real.sqrt (f+c)-(Real.sqrt (g+c)+a))]

theorem shifted_energy_step (lam r S H F Fnext : ℝ)
    (h : lam*r ≤ F-Fnext) :
    Fnext+lam*(S+r+H) ≤ F+lam*(S+H) := by nlinarith

-- B.8: sum an arbitrary root-potential recurrence, including empty prefix.
theorem telescope (x a : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, x (k+1) ≤ x k+a k) :
    x n ≤ x 0+∑ k ∈ Finset.range n, a k := by
  induction n with
  | zero => simp
  | succ n ih =>
    have prev := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have last := h n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ]
    linarith

-- B.8: drop the nonnegative terminal KL term.
theorem drawdown_terminal (lam S H F M : ℝ) (hl : 0 < lam)
    (hf : 0 ≤ F) (h : F+lam*(S+H) ≤ M) : S ≤ M/lam-H := by
  have hh : lam*(S+H) ≤ M := by linarith
  have : S+H ≤ M/lam := (le_div_iff₀ hl).mpr (by nlinarith)
  linarith

-- B.8: combine shift stability with the actual one-step energy inequality.
theorem shifted_root_step (f g c a E : ℝ) (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hm : Real.sqrt f ≤ Real.sqrt g+a) (he : g+c ≤ E) :
    Real.sqrt (f+c) ≤ Real.sqrt E+a := by
  have h1 := sqrt_shift f g c a hf hg hc ha hm
  have h2 := Real.sqrt_le_sqrt he
  linarith

-- B.15: subtracting the local numerical error recovers the exact inequality.
theorem error_adjustment (lam r eps F Fnext : ℝ) (hl : 0 < lam)
    (h : lam*r ≤ F-Fnext+eps) :
    lam*(r-eps/lam) ≤ F-Fnext := by
  have he : lam*(eps/lam)=eps := by field_simp
  nlinarith

-- B.9: conservative coefficient bound valid for L >= 1.
theorem good_node_coefficient (L : ℝ) (hL : 1 ≤ L) :
    (2/(512*L)+1/(512*L)^2)*(1+128*L) ≤ 1 := by
  have hp : 0 < L := by linarith
  field_simp
  nlinarith [sq_nonneg (L-1)]

-- B.9: tree counting inequality is an EXPLICIT unformalized combinatorial input.
theorem recursion_cancellation (H L ng nb : ℝ) (hH : 0 ≤ H)
    (hL : 0 < L) (hb : 0 ≤ nb) (hc : ng ≤ L*(2*nb+1)) :
    H/(64*L)*ng - 127*H/128*nb ≤ H/64 := by
  have hm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ H/(64*L))
  have he : H/(64*L)*(L*(2*nb+1))=H/64*(2*nb+1) := by
    field_simp
  rw [he] at hm
  nlinarith [mul_nonneg hH hb]

-- B.10: scalar consequence of the disjoint triggering-jump accounting.
theorem partition_count (M P V : ℝ) (hv : 0 < V)
    (h : (M-1)*V ≤ P) : M ≤ 1+P/V := by
  have := (le_div_iff₀ hv).mpr h
  linarith

-- B.11: algebra assembling interval overhead and smoothing error.
theorem fixed_scale_assembly (R M H P V smooth : ℝ)
    (hh : 0 ≤ H) (hm : M ≤ 1+P/V) (hr : R ≤ M*H/64+smooth) :
    R ≤ H/64*(1+P/V)+smooth := by
  nlinarith [mul_le_mul_of_nonneg_right hm hh]

-- B.12: exact balancing identity, with an explicitly positive chosen scale.
theorem balance_scale (B P C tau : ℝ) (ht : 0 < tau)
    (hbal : B*P=C*tau^3) : B*P/tau+C*tau^2=2*C*tau^2 := by
  rw [hbal]
  field_simp
  ring

-- C.2: expected square loss for a two-point label with mean mu.
theorem square_risk (w mu : ℝ) :
    ((1+mu)/2)*(((w-1)^2-(mu-1)^2)/2) +
    ((1-mu)/2)*(((w+1)^2-(mu+1)^2)/2) = (w-mu)^2/2 := by ring

-- C.4: scalar coefficient ensuring dimension-independent curvature.
theorem lower_curvature (z : ℝ) (hl : -(3/2 : ℝ) ≤ z)
    (hu : z ≤ 3/2) : (4/9 : ℝ)*z^2 ≤ 1 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ z+3/2)]

-- C.2: path budget of the proposed block comparator (given per-jump bound).
theorem block_path_budget (P K : ℝ) (hp : 0 ≤ P) (hk : 1 ≤ K) :
    2*(P/(4*K))*(K-1) ≤ P := by
  have hkp : 0 < K := by linarith
  apply (le_of_mul_le_mul_right ?_ hkp)
  field_simp
  nlinarith

-- C.3: information budget in the static construction.
theorem static_information (d : ℝ) (hd : 0 < d) :
    d*(1/(8*Real.sqrt d))^2=1/64 := by
  have hs := Real.sq_sqrt (le_of_lt hd)
  have hp := Real.sqrt_pos.mpr hd
  field_simp
  nlinarith

end Audit254

#print axioms Audit254.sqrt_shift
#print axioms Audit254.telescope
#print axioms Audit254.recursion_cancellation
#print axioms Audit254.square_risk
#print axioms Audit254.surrogate_curvature
#print axioms Audit254.gaussian_mix_sign
#print axioms Audit254.one_step_interface
#print axioms Audit254.root_movement_embedding
#print axioms Audit254.shifted_energy_step
#print axioms Audit254.drawdown_terminal
#print axioms Audit254.shifted_root_step
#print axioms Audit254.error_adjustment
#print axioms Audit254.good_node_coefficient
#print axioms Audit254.partition_count
#print axioms Audit254.fixed_scale_assembly
#print axioms Audit254.balance_scale
#print axioms Audit254.lower_curvature
#print axioms Audit254.block_path_budget
#print axioms Audit254.static_information
