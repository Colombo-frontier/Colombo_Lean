import RationalWorkingBounds254
import RationalExplicitOnline254

noncomputable section
namespace Paper254

/-- The numerical exponents are explicit polynomials of input encoding
length, dimension and logarithmic horizon, rather than unbounded choices. -/
def encodedRationalSparseInput {d T : ℕ} (hd : 0<d)
    (D G H lam : ℚ) (eta : ℝ) (W : Domain d (D:ℝ))
    (hD : 0<(D:ℝ)) (hG : 0<(G:ℝ)) (heta : 0<eta)
    (hH : (H:ℝ)=(D:ℝ)^2) (hlam : 2*(lam:ℝ)=curvature (D:ℝ) (G:ℝ) eta)
    (b z : ℕ) (hDb : RationalHeight D b) (hGb : RationalHeight G b)
    (hHb : RationalHeight H b) (hlb : RationalHeight lam b)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier) :
    ExplicitRationalSparseInput d T (D:ℝ) (G:ℝ) eta W := by
  let v := workingMagnitude d T b
  have hv := workingMagnitude_basic d T b
  have hHpos : 0<(H:ℝ) := by rw [hH]; positivity
  have hlpos : 0<(lam:ℝ) := by
    have hh := curvature_pos (D:ℝ) (G:ℝ) eta hD hG heta
    linarith
  have hp : (2:ℝ)^b≤(2:ℝ)^v := pow_le_pow_right₀ (by norm_num) hv.2.1
  exact {
    dimension_pos := hd
    diameter_pos := hD
    gradient_pos := hG
    curvature_pos := heta
    s := b+z+Nat.log 2 T+2
    v := v
    v_pos := hv.1
    dimension_bound := hv.2.2.1
    diameter_bound := (le_abs_self _).trans (hDb.real_abs.trans hp)
    oracle := oracle
    oracle_spec := hspec
    hi := H
    hi_eq := hH
    hi_bound := (le_abs_self _).trans (hHb.real_abs.trans hp)
    scale_inverse_bound := fun k=>(capped_variance_magnitude d T b H hHpos hHb k).1
    gap_inverse_bound := fun k=>(capped_variance_magnitude d T b H hHpos hHb k).2
    lam := lam
    lam_eq := hlam
    gradient_bound := (le_abs_self _).trans (hGb.real_abs.trans hp)
    lam_bound := (le_abs_self _).trans (hlb.real_abs.trans hp)
    live_bound := hv.2.2.2
    initial_mean := w0
    initial_feasible := hw0 }

theorem encodedRationalSparseInput_budget {d T : ℕ} (hd : 0<d) (hT : 0<T)
    (D G H lam : ℚ) (eta : ℝ) (W : Domain d (D:ℝ))
    (hD : 0<(D:ℝ)) (hG : 0<(G:ℝ)) (heta : 0<eta)
    (hH : (H:ℝ)=(D:ℝ)^2) (hlam : 2*(lam:ℝ)=curvature (D:ℝ) (G:ℝ) eta)
    (b z : ℕ) (hDb : RationalHeight D b) (hGb : RationalHeight G b)
    (hHb : RationalHeight H b) (hlb : RationalHeight lam b)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (delta : ℝ) (hdelta : ((2:ℝ)^z)⁻¹≤delta) :
    let I := encodedRationalSparseInput (T:=T) hd D G H lam eta W hD hG heta hH hlam b z hDb hGb hHb hlb
      oracle hspec w0 hw0
    ((2:ℝ)^I.s)⁻¹≤(I.lam:ℝ)*delta/(2*T) := by
  have hlpos : 0<(lam:ℝ) := by
    have hh := curvature_pos (D:ℝ) (G:ℝ) eta hD hG heta
    linarith
  exact working_error_budget T b z (lam:ℝ) delta hT (hlb.positive_lower hlpos) hdelta

end Paper254
#print axioms Paper254.encodedRationalSparseInput_budget
