import RationalSparseClipped254
import RationalSparsePrecision254

noncomputable section
namespace Paper254

/-- The precision choices precede all comparator paths and all rounds.
This theorem constructs the learner and derives its clipped regret bound;
the input conditions contain no potential or regret inequality. -/
theorem exists_rational_sparse_clipped {d T : ℕ} (hd : 0 < d) (hT : 2 ≤ T)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (a b : ℕ) (hdim : (d : ℝ)≤(2 : ℝ)^a)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhib : (hi : ℝ)≤(2 : ℝ)^b)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (query : ℕ → RationalGradientQuery d)
    (hquery : ∀ t w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j => (query t w j : ℝ))‖≤G)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : RationalSparseConstruction d T (scaleCount T) D G eta W,
      C.oracle=oracle ∧ C.initial_mean=w0 ∧ C.query=query ∧ C.lam=lam ∧
      ∀ f : ℕ → Loss d, (∀ t < T, ExpConcaveOn eta W.carrier (f t)) →
        (∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
          W.carrier (C.playedPoint t).val) →
        ∀ u : ℕ → W.carrier, ∀ tau : ℝ, D/T≤tau → tau≤D →
          C.cumulativeRegret f u≤2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
            Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*
              intervalCharge (C.movementLength u) 0 (T-1)+curvature D G eta*G^2*T*tau^2)+delta := by
  have hlam0 : 0 < (lam : ℝ) := by
    have h := curvature_pos D G eta hD hG heta
    linarith
  let eps := min ((lam : ℝ)*delta/(2*T)) 1
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  obtain ⟨p,hp,_hinflate,_hbirth⟩ := exists_standardMasterPrecision T (scaleCount T) eps heps
  let lo : Fin (scaleCount T+1) → ℚ := fun k => rationalCappedVariance hi k.val
  have hlo : ∀ k, 0 < (lo k : ℝ) := fun k => (rationalCappedVariance_range D hD hi hhi k.val).1
  have hgap : ∀ k, (lo k : ℝ)<(hi : ℝ) := fun k => (rationalCappedVariance_range D hD hi hhi k.val).2
  obtain ⟨C,hCl,hCh,hClam,hCp,hCo,hCw,hCq,hCe⟩ := exists_rational_sparse_construction
    (T := T) hd W hD hG heta a b hdim oracle hspec hi hhi hhib lo hlo hgap lam hlam p
    w0 hw0 query hquery eps heps
  have hgrid : ∀ k, C.lo k=rationalCappedVariance C.hi k.val := by
    intro k
    rw [hCl,hCh]
  have hmaster : C.masterError≤eps := by
    simpa only [RationalSparseConstruction.masterError,hCp] using hp
  have hmaster1 : C.masterError≤1 := hmaster.trans (min_le_right _ _)
  have hloc : ∀ k, C.localError k≤(C.lam : ℝ)*delta/(2*T) := by
    intro k
    rw [hClam]
    exact (hCe k).trans (min_le_left _ _)
  have hmasterBudget : C.masterError≤(C.lam : ℝ)*delta/(2*T) := by
    rw [hClam]
    exact hmaster.trans (min_le_left _ _)
  refine ⟨C,hCo,hCw,hCq,hClam,?_⟩
  intro f hf hder u tau htau htaumax
  exact C.loss_clipped hT f hf hder hgrid hmaster1 delta hloc hmasterBudget u tau htau htaumax

end Paper254
#print axioms Paper254.exists_rational_sparse_clipped
