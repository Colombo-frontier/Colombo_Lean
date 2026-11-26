import RationalSparseMain254

noncomputable section
namespace Paper254

structure RationalSparseTuning {d T : ℕ} {D G eta : ℝ} {W : Domain d D}
    (C : RationalSparseConstruction d T (scaleCount T) D G eta W) (delta : ℝ) : Prop where
  grid : ∀ k, C.lo k=rationalCappedVariance C.hi k.val
  master_small : C.masterError≤1
  local_error : ∀ k, C.localError k≤(C.lam : ℝ)*delta/(2*T)
  master_error : C.masterError≤(C.lam : ℝ)*delta/(2*T)

/-- Tuning of the empty trajectory; the loss oracle can later be substituted
without changing a precision, covariance threshold, or master parameter. -/
theorem exists_rational_sparse_tuning {d T : ℕ} (hd : 0 < d) (hT : 0 < T)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (a b : ℕ) (hdim : (d : ℝ)≤(2 : ℝ)^a)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhib : (hi : ℝ)≤(2 : ℝ)^b)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : RationalSparseConstruction d T (scaleCount T) D G eta W,
      C.oracle=oracle ∧ C.initial_mean=w0 ∧ C.hi=hi ∧ C.lam=lam ∧ RationalSparseTuning C delta := by
  have hlam0 : 0 < (lam : ℝ) := by
    have h := curvature_pos D G eta hD hG heta
    linarith
  let eps := min ((lam : ℝ)*delta/(2*T)) 1
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  obtain ⟨p,hp,_hinflate,_hbirth⟩ := exists_standardMasterPrecision T (scaleCount T) eps heps
  let lo : Fin (scaleCount T+1) → ℚ := fun k => rationalCappedVariance hi k.val
  have hlo : ∀ k, 0 < (lo k : ℝ) := fun k => (rationalCappedVariance_range D hD hi hhi k.val).1
  have hgap : ∀ k, (lo k : ℝ)<(hi : ℝ) := fun k => (rationalCappedVariance_range D hD hi hhi k.val).2
  obtain ⟨C,hCl,hCh,hClam,hCp,hCo,hCw,_hCq,hCe⟩ := exists_rational_sparse_construction
    (T := T) hd W hD hG heta a b hdim oracle hspec hi hhi hhib lo hlo hgap lam hlam p
    w0 hw0 (fun _ _ _ => 0) (by
      intro t w hw
      have hz : WithLp.toLp 2 (fun j : Fin d => ((0 : ℚ) : ℝ))=(0 : Space d) := by ext j; simp
      change ‖WithLp.toLp 2 (fun j : Fin d => ((0 : ℚ) : ℝ))‖≤G
      rw [hz,norm_zero]
      exact hG.le) eps heps
  have hmaster : C.masterError≤eps := by
    simpa only [RationalSparseConstruction.masterError,hCp] using hp
  refine ⟨C,hCo,hCw,hCh,hClam,?_⟩
  constructor
  · intro k
    rw [hCl,hCh]
  · exact hmaster.trans (min_le_right _ _)
  · intro k
    rw [hClam]
    exact (hCe k).trans (min_le_left _ _)
  · rw [hClam]
    exact hmaster.trans (min_le_left _ _)

end Paper254
#print axioms Paper254.exists_rational_sparse_tuning
