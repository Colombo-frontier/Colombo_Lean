import Bilevel.ZeroChainPotential
import Bilevel.ZeroChainProfiles

/-! Every fixed derivative order of the paper's actual Gaussian primitive
is globally bounded. The polynomial-times-Gaussian recurrence is proved;
no finite-order bound is assumed. -/
noncomputable section
open Polynomial
namespace Bilevel.PolishedGaussianAllDerivatives
open ZeroChainPotential

def kernelJet (p : ℝ[X]) (t : ℝ) : ℝ := p.eval t*kernel t

theorem kernelJet_bounded_positive (p : ℝ[X]) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ t : ℝ,0 < t → |kernelJet p t| ≤ K := by
  obtain ⟨K,hK,hb⟩ := ZeroChainGate.jet_bounded (p.comp (C (Real.sqrt 2)*X))
  refine ⟨K,hK,?_⟩
  intro t ht
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsq : (Real.sqrt (2 : ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt (2 : ℝ)/t)⁻¹=t/Real.sqrt 2 := by rw [inv_div]
  have hm : Real.sqrt (2 : ℝ)*(t/Real.sqrt 2)=t := by field_simp
  have hex : -(t/Real.sqrt (2 : ℝ))^2= -t^2/2 := by rw [div_pow,hsq]; ring
  have he : ZeroChainGate.jet (p.comp (C (Real.sqrt 2)*X)) (Real.sqrt 2/t)=kernelJet p t := by
    rw [ZeroChainGate.jet,ZeroChainGate.gate_pos_formula (div_pos hs ht),hi]
    simp only [Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,hm,hex]
    rfl
  rw [← he]
  exact hb _

theorem kernelJet_bounded (p : ℝ[X]) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ t : ℝ,|kernelJet p t| ≤ K := by
  obtain ⟨A,hA,ha⟩ := kernelJet_bounded_positive p
  obtain ⟨B,hB,hb⟩ := kernelJet_bounded_positive (p.comp (-X))
  refine ⟨A+B+|p.eval 0|,by positivity,?_⟩
  intro t
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h := hb (-t) (by linarith : 0 < -t)
    have he : kernelJet (p.comp (-X)) (-t)=kernelJet p t := by
      simp [kernelJet,Polynomial.eval_comp,kernel]
    rw [he] at h
    linarith [abs_nonneg (p.eval 0)]
  · simp only [kernelJet,kernel,zero_pow (by decide : (2 : ℕ) ≠ 0),neg_zero,
      zero_div,Real.exp_zero,mul_one]
    linarith
  · exact (ha t ht).trans (by linarith [abs_nonneg (p.eval 0)])

def slopeJet (p : ℝ[X]) (t : ℝ) : ℝ := p.eval t*phiSlope t

def next (p : ℝ[X]) : ℝ[X] := p.derivative-X*p

theorem slopeJet_hasDerivAt (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (slopeJet p) (slopeJet (next p) t) t := by
  have h := (p.hasDerivAt t).mul (phiSlope_hasDerivAt t)
  convert h using 1
  simp only [slopeJet,next,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X]
  ring

def polynomialJet : ℕ → ℝ[X]
  | 0 => 1
  | n+1 => next (polynomialJet n)

theorem slope_iteratedDeriv (n : ℕ) :
    iteratedDeriv n phiSlope=slopeJet (polynomialJet n) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    funext t
    simp [polynomialJet,slopeJet]
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext t
    exact (slopeJet_hasDerivAt (polynomialJet n) t).deriv

theorem slopeJet_bounded (p : ℝ[X]) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ t : ℝ,|slopeJet p t| ≤ K := by
  obtain ⟨K,hK,hb⟩ := kernelJet_bounded p
  refine ⟨Real.sqrt (Real.exp 1)*K,by positivity,?_⟩
  intro t
  have he : slopeJet p t=Real.sqrt (Real.exp 1)*kernelJet p t := by
    dsimp [slopeJet,phiSlope,kernelJet]
    ring
  rw [he,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hb t) (Real.sqrt_nonneg _)

theorem phi_derivative_bounded (n : ℕ) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ t : ℝ,|iteratedDeriv n phi t| ≤ K := by
  cases n with
  | zero =>
    refine ⟨Real.sqrt (Real.exp 1)*Real.sqrt (2*Real.pi),by positivity,?_⟩
    intro t
    simpa only [iteratedDeriv_zero,abs_of_nonneg (phi_nonneg t)] using phi_bounded t
  | succ n =>
    rw [iteratedDeriv_succ',show deriv phi=phiSlope from funext phi_deriv,slope_iteratedDeriv]
    exact slopeJet_bounded _

/-- The complete source statement, with the order quantified before the
bound and the point. These are the original Psi and Gaussian Phi. -/
theorem source_profiles_all_fixed_orders_bounded (n : ℕ) :
    ∃ K : ℝ,0 ≤ K ∧ ∀ t : ℝ,
      |iteratedDeriv n ZeroChainProfiles.psi t| ≤ K ∧ |iteratedDeriv n phi t| ≤ K := by
  obtain ⟨A,hA,ha⟩ := ZeroChainProfiles.psi_derivative_bounded n
  obtain ⟨B,hB,hb⟩ := phi_derivative_bounded n
  refine ⟨A+B,by positivity,?_⟩
  intro t
  exact ⟨(ha t).trans (by linarith),(hb t).trans (by linarith)⟩

end Bilevel.PolishedGaussianAllDerivatives
