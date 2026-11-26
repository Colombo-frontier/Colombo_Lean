import RationalSparseOnline254
import RationalPredictionCost254
import RationalTaylorHeight254

open scoped BigOperators
namespace Paper254

def rationalNormSquare {d : ℕ} (g : Fin d→ℚ) : ℚ := ∑ j,g j^2

theorem rationalNormSquare_cast {d : ℕ} (g : Fin d→ℚ) :
    (rationalNormSquare g:ℝ)=‖WithLp.toLp 2 (fun j=>(g j:ℝ))‖^2 := by
  simp only [rationalNormSquare,Rat.cast_sum,Rat.cast_pow,EuclideanSpace.norm_sq_eq]
  change (∑ j,(g j:ℝ)^2)=∑ j,|(g j:ℝ)|^2
  simp only [sq_abs]

/-- The only test is a rational squared-norm comparison. No decision
procedure for the admissible loss class is used. -/
def rationalGradientGuard {d : ℕ} (G : ℚ) (g : Fin d→ℚ) : Fin d→ℚ :=
  if rationalNormSquare g≤G^2 then g else 0

def boundedRationalLossOracle {d : ℕ} (G : ℚ) (oracle : RationalLossGradientOracle d) :
    RationalLossGradientOracle d := fun f w=>
  let response:=Vector.ofFn (oracle f w)
  rationalGradientGuard G (fun j=>response.get j)

theorem rationalGradientGuard_eq {d : ℕ} (G : ℚ) (g : Fin d→ℚ) (hG : 0≤(G:ℝ))
    (hg : ‖WithLp.toLp 2 (fun j=>(g j:ℝ))‖≤G) : rationalGradientGuard G g=g := by
  have hh : rationalNormSquare g≤G^2 := by
    have hr : (rationalNormSquare g:ℝ)≤(G:ℝ)^2 := by
      rw [rationalNormSquare_cast]
      exact pow_le_pow_left₀ (norm_nonneg _) hg 2
    exact_mod_cast hr
  simp [rationalGradientGuard,hh]

theorem rationalGradientGuard_bound {d : ℕ} (G : ℚ) (g : Fin d→ℚ) (hG : 0≤(G:ℝ)) :
    ‖WithLp.toLp 2 (fun j=>(rationalGradientGuard G g j:ℝ))‖≤G := by
  by_cases hh : rationalNormSquare g≤G^2
  · have hr : (rationalNormSquare g:ℝ)≤(G:ℝ)^2 := by exact_mod_cast hh
    rw [rationalNormSquare_cast] at hr
    simp only [rationalGradientGuard,if_pos hh]
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun j=>(g j:ℝ)))]
  · simp only [rationalGradientGuard,if_neg hh]
    have hz : WithLp.toLp 2 (fun j:Fin d=>((0:Fin d→ℚ) j:ℝ))=(0:Space d) := by
      ext j
      simp
    rw [hz]
    simpa using hG

theorem boundedRationalLossOracle_eq {d : ℕ} (G : ℚ) (oracle : RationalLossGradientOracle d)
    (hG : 0≤(G:ℝ)) (f : Loss d) (w : Fin d→ℚ)
    (hg : ‖WithLp.toLp 2 (fun j=>(oracle f w j:ℝ))‖≤G) :
    boundedRationalLossOracle G oracle f w=oracle f w := by
  have he : (fun j=>(Vector.ofFn (oracle f w)).get j)=oracle f w := by funext j; simp [Vector.get]
  simp only [boundedRationalLossOracle,he]
  exact rationalGradientGuard_eq G _ hG hg

theorem boundedRationalLossOracle_compatible {d : ℕ} {D : ℝ} (W : Domain d D)
    (G : ℚ) (hG : 0≤(G:ℝ)) (oracle : RationalLossGradientOracle d) (f : Loss d)
    (hexact : RationalLossCompatible W oracle f)
    (hbound : ∀ w,WithLp.toLp 2 (fun j=>(w j:ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j=>(oracle f w j:ℝ))‖≤G) :
    RationalLossCompatible W (boundedRationalLossOracle G oracle) f := by
  intro w hw
  rw [boundedRationalLossOracle_eq G oracle hG f w (hbound w hw)]
  exact hexact w hw

/-- Total boundedness and compatibility of the zero padding loss require
no exact-rational oracle for the class of all real-valued losses. -/
theorem boundedRationalLossOracle_spec {d : ℕ} {D eta : ℝ} (W : Domain d D)
    (G : ℚ) (hG : 0≤(G:ℝ)) (oracle : RationalLossGradientOracle d)
    (hzero : RationalLossCompatible W oracle (fun _=>0)) :
    RationalLossGradientOracleSpec W (G:ℝ) eta (boundedRationalLossOracle G oracle) := by
  constructor
  · intro f w hw
    exact rationalGradientGuard_bound G _ hG
  · intro w hw
    have he : (fun j=>(Vector.ofFn (oracle (fun _=>0) w)).get j)=oracle (fun _=>0) w := by
      funext j
      simp [Vector.get]
    simp only [boundedRationalLossOracle,he,rationalGradientGuard]
    split_ifs with hh
    · exact hzero w hw
    · have hz : WithLp.toLp 2 (fun j:Fin d=>((0:Fin d→ℚ) j:ℝ))=(0:Space d) := by
        ext j
        simp
      rw [hz]
      exact hasGradientWithinAt_const (c:=(0:ℝ)) (s:=W.carrier)
        (x:=WithLp.toLp 2 (fun j=>(w j:ℝ)))

theorem rationalGradientGuard_height {d : ℕ} (G : ℚ) (g : Fin d→ℚ) (b : ℕ)
    (hg : ∀ j,RationalHeight (g j) b) (j : Fin d) :
    RationalHeight (rationalGradientGuard G g j) b := by
  by_cases hh : rationalNormSquare g≤G^2
  · simpa [rationalGradientGuard,hh] using hg j
  · simpa [rationalGradientGuard,hh] using RationalHeight.zero.mono (Nat.zero_le b)

theorem boundedRationalLossOracle_height {d : ℕ} (G : ℚ) (oracle : RationalLossGradientOracle d)
    (f : Loss d) (w : Fin d→ℚ) (b : ℕ) (hg : ∀ j,RationalHeight (oracle f w j) b)
    (j : Fin d) : RationalHeight (boundedRationalLossOracle G oracle f w j) b := by
  apply rationalGradientGuard_height
  intro i
  simpa [Vector.get] using hg i

end Paper254
#print axioms Paper254.boundedRationalLossOracle_spec
#print axioms Paper254.boundedRationalLossOracle_height
