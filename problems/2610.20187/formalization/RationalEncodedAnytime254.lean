import RationalAnytime254
import RationalEncodedInput254

noncomputable section
namespace Paper254

section Encoded
variable {d : ℕ} (hd : 0 < d)
variable (D G H lam : ℚ) (eta : ℝ) (W : Domain d (D : ℝ))
variable (hD : 0 < (D : ℝ)) (hG : 0 < (G : ℝ)) (heta : 0 < eta)
variable (hH : (H : ℝ)=(D : ℝ)^2) (hlam : 2*(lam : ℝ)=curvature (D : ℝ) (G : ℝ) eta)
variable (b z : ℕ) (hDb : RationalHeight D b) (hGb : RationalHeight G b)
variable (hHb : RationalHeight H b) (hlb : RationalHeight lam b)
variable (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
variable (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)

def encodedRationalFamily : (N : ℕ) → ExplicitRationalSparseInput d N (D : ℝ) (G : ℝ) eta W :=
  fun N => encodedRationalSparseInput hd D G H lam eta W hD hG heta hH hlam
    b (z+Nat.log 2 N+1) hDb hGb hHb hlb oracle hspec w0 hw0

theorem encodedRationalFamily_budget (delta : ℝ) (hdelta : ((2 : ℝ)^z)⁻¹≤delta) :
    let I := encodedRationalFamily hd D G H lam eta W hD hG heta hH hlam b z hDb hGb hHb hlb oracle hspec w0 hw0
    ∀ j : ℕ, ((2 : ℝ)^(I (2^j)).s)⁻¹≤
      ((I (2^j)).lam : ℝ)*(delta/(2 : ℝ)^(j+1))/(2*(2^j : ℕ)) := by
  intro I j
  have he : ((2 : ℝ)^(z+Nat.log 2 (2^j)+1))⁻¹≤delta/(2 : ℝ)^(j+1) := by
    rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ)) j]
    have hx : ((2 : ℝ)^(z+j+1))⁻¹=((2 : ℝ)^z)⁻¹/(2 : ℝ)^(j+1) := by
      rw [show z+j+1=z+(j+1) by omega,pow_add]
      field_simp
    rw [hx]
    exact div_le_div_of_nonneg_right hdelta (by positivity)
  exact encodedRationalSparseInput_budget hd (by positivity) D G H lam eta W hD hG heta hH hlam
    b (z+Nat.log 2 (2^j)+1) hDb hGb hHb hlb oracle hspec w0 hw0 (delta/(2 : ℝ)^(j+1)) he

/-- Explicit binary-precision tuning and the list learner form an anytime
algorithm. Numerical error remains at most delta over all completed and
partial doubling epochs, without knowing the terminal horizon. -/
theorem encoded_rational_anytime (roundCost projectionCost gradientCost : ℕ)
    (gradientOracle : RationalLossGradientOracle d)
    (hgradient : RationalLossGradientOracleSpec W (G : ℝ) eta gradientOracle)
    (delta : ℝ) (hdelta : ((2 : ℝ)^z)⁻¹≤delta)
    (T : ℕ) (hT : 0 < T) (f : Fin T → Loss d)
    (hf : ∀ t, AdmissibleLoss W (G : ℝ) eta (f t))
    (hcompatible : ∀ t, RationalLossCompatible W gradientOracle (f t)) (u : Fin T → W.carrier)
    (tau : ℝ) (htau : 0 < tau) (hhi : tau≤(D : ℝ)) :
    let I := encodedRationalFamily hd D G H lam eta W hD hG heta hH hlam b z hDb hGb hHb hlb oracle hspec w0 hw0
    regret (anytimeRestriction (doublingLearner
      (rationalDoublingFamily I roundCost projectionCost gradientCost gradientOracle hgradient)) T) f u≤
      2048*((epochCount T : ℝ)*(d+1 : ℝ)*logFactor T^2/curvature (D : ℝ) (G : ℝ) eta+
        Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature (D : ℝ) (G : ℝ) eta*tau)*pathLength u+
          curvature (D : ℝ) (G : ℝ) eta*(G : ℝ)^2*(2*T*tau^2+2*(D : ℝ)^2))+delta := by
  intro I
  have hdeltapos : 0 < delta := (by positivity : 0 < ((2 : ℝ)^z)⁻¹).trans_le hdelta
  exact rational_anytime_clipped I roundCost projectionCost gradientCost gradientOracle hgradient hT delta hdeltapos
    (encodedRationalFamily_budget hd D G H lam eta W hD hG heta hH hlam b z hDb hGb hHb hlb oracle hspec w0 hw0 delta hdelta)
    f hf hcompatible u tau htau hhi

end Encoded
end Paper254
#print axioms Paper254.encodedRationalFamily_budget
#print axioms Paper254.encoded_rational_anytime
