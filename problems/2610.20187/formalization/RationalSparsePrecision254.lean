import RationalSparseConstruction254
import RationalScalePrecision254

noncomputable section
namespace Paper254

/-- Data-independent precision choices instantiate the actual rational learner. -/
theorem exists_rational_sparse_construction {d T K : ℕ} (hd : 0<d)
    {D G eta : ℝ} (W : Domain d D) (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (a b : ℕ) (hdim : (d:ℝ)≤(2:ℝ)^a)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi:ℝ)=D^2) (hhib : (hi:ℝ)≤(2:ℝ)^b)
    (lo : Fin (K+1)→ℚ) (hlo : ∀ k,0<(lo k:ℝ)) (hgap : ∀ k,(lo k:ℝ)<(hi:ℝ))
    (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta) (p : ℕ)
    (w0 : Fin d→ℚ) (hw0 : WithLp.toLp 2 (fun j=>(w0 j:ℝ))∈W.carrier)
    (query : ℕ→RationalGradientQuery d)
    (hquery : ∀ t w,WithLp.toLp 2 (fun j=>(w j:ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j=>(query t w j:ℝ))‖≤G)
    (eps : ℝ) (heps : 0<eps) :
    ∃ C : RationalSparseConstruction d T K D G eta W,
      C.lo=lo ∧ C.hi=hi ∧ C.lam=lam ∧ C.master_precision=p ∧
      C.oracle=oracle ∧ C.initial_mean=w0 ∧ C.query=query ∧ ∀ k,C.localError k≤eps := by
  obtain ⟨cfg,margin,hguard,hm,hl,hu,he⟩ := exists_rational_scale_precision hd a b hdim
    D G (lam:ℝ) lo hi hlo hgap hhib eps heps
  let C : RationalSparseConstruction d T K D G eta W := {
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
    lo_le_hi := fun k=>(hgap k).le
    cfg := cfg
    guards := hguard
    margin := margin
    margin_nonneg := hm
    lower_error := hl
    upper_error := hu
    lam := lam
    lam_eq := hlam
    master_precision := p
    initial_mean := w0
    initial_feasible := hw0
    query := query
    query_bound := hquery }
  exact ⟨C,rfl,rfl,rfl,rfl,rfl,rfl,rfl,he⟩

end Paper254
#print axioms Paper254.exists_rational_sparse_construction
