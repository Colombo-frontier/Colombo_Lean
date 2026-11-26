import RationalSparseConstruction254
import PolynomialErrorPrecision254

noncomputable section
namespace Paper254

def explicitSparseHistoryPrecision (d s v : ℕ) : ℕ := 2*s+4*((5*d+60)*v)+4

def explicitRationalSparseConstruction {d T K : ℕ} (hd : 0 < d)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (s v p : ℕ) (hv : 1≤v) (hdv : (d : ℝ)≤(2 : ℝ)^v) (hDv : D≤(2 : ℝ)^v)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhiv : (hi : ℝ)≤(2 : ℝ)^v)
    (lo : Fin (K+1) → ℚ) (hlo : ∀ k, 0 < (lo k : ℝ)) (hgap : ∀ k, (lo k : ℝ)<(hi : ℝ))
    (hlov : ∀ k, (lo k : ℝ)≤(2 : ℝ)^v) (hliv : ∀ k, (lo k : ℝ)⁻¹≤(2 : ℝ)^v)
    (hgapv : ∀ k, ((hi : ℝ)-(lo k : ℝ))⁻¹≤(2 : ℝ)^v)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (hGv : G≤(2 : ℝ)^v) (hlamv : (lam : ℝ)≤(2 : ℝ)^v)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (query : ℕ → RationalGradientQuery d)
    (hquery : ∀ t w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j => (query t w j : ℝ))‖≤G) :
    RationalSparseConstruction d T K D G eta W := by
  let r := explicitSparseHistoryPrecision d s v
  have hlam0 : 0≤(lam : ℝ) := by
    have hc := curvature_pos D G eta hD hG heta
    linarith
  exact {
    dimension_pos := hd
    diameter_pos := hD
    gradient_pos := hG
    curvature_pos := heta
    oracle := oracle
    oracle_spec := hspec
    hi := hi
    hi_eq := hhi
    lo := lo
    lo_pos := hlo
    lo_le_hi := fun k => (hgap k).le
    cfg := fun k => uniformHistoryParameters v v r r (lo k) hi
    guards := fun k => (explicit_history_precision_and_guards d s v hd hv D G (lam : ℝ)
      (lo k) hi hD.le hG.le hlam0 (hlo k) (hgap k) hdv hDv (hlov k) (hliv k) hhiv hGv hlamv
      (hgapv k)).1
    margin := fun _ => ((2 : ℝ)^(r+2))⁻¹
    margin_nonneg := fun _ => by positivity
    lower_error := fun k => by
      dsimp [uniformHistoryParameters]
      push_cast
      rw [add_sub_cancel_left,abs_of_pos (by positivity)]
    upper_error := fun k => by
      dsimp [uniformHistoryParameters]
      push_cast
      rw [sub_sub_cancel_left,abs_neg,abs_of_pos (by positivity)]
    lam := lam
    lam_eq := hlam
    master_precision := p
    initial_mean := w0
    initial_feasible := hw0
    query := query
    query_bound := hquery }

theorem explicitRationalSparseConstruction_error {d T K : ℕ} (hd : 0 < d)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (s v p : ℕ) (hv : 1≤v) (hdv : (d : ℝ)≤(2 : ℝ)^v) (hDv : D≤(2 : ℝ)^v)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhiv : (hi : ℝ)≤(2 : ℝ)^v)
    (lo : Fin (K+1) → ℚ) (hlo : ∀ k, 0 < (lo k : ℝ)) (hgap : ∀ k, (lo k : ℝ)<(hi : ℝ))
    (hlov : ∀ k, (lo k : ℝ)≤(2 : ℝ)^v) (hliv : ∀ k, (lo k : ℝ)⁻¹≤(2 : ℝ)^v)
    (hgapv : ∀ k, ((hi : ℝ)-(lo k : ℝ))⁻¹≤(2 : ℝ)^v)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (hGv : G≤(2 : ℝ)^v) (hlamv : (lam : ℝ)≤(2 : ℝ)^v)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (query : ℕ → RationalGradientQuery d)
    (hquery : ∀ t w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j => (query t w j : ℝ))‖≤G) (k : Fin (K+1)) :
    (explicitRationalSparseConstruction (T := T) hd W hD hG heta s v p hv hdv hDv oracle hspec
      hi hhi hhiv lo hlo hgap hlov hliv hgapv lam hlam hGv hlamv w0 hw0 query hquery).localError k≤
        ((2 : ℝ)^s)⁻¹ := by
  have hlam0 : 0≤(lam : ℝ) := by
    have hc := curvature_pos D G eta hD hG heta
    linarith
  exact (explicit_history_precision_and_guards d s v hd hv D G (lam : ℝ) (lo k) hi
    hD.le hG.le hlam0 (hlo k) (hgap k) hdv hDv (hlov k) (hliv k) hhiv hGv hlamv (hgapv k)).2

end Paper254
#print axioms Paper254.explicitRationalSparseConstruction_error
