import CompactSparse254

noncomputable section
namespace Paper254

/-- Loss-independent update after receiving one vector from the gradient
oracle. Every history and the master use this same vector. -/
def SparseMasterState.stepWithGradient {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hG : 0<G) (hη : 0<η) (hD : 0<D)
    (q : Fin (K+1) → ℝ) (hq : ∀ k,0<q k) (t : Fin T) (g : Space d) : SparseMasterState W T K := by
  classical
  let γ := curvature D G η
  let lam := γ/2
  have hlam : 0≤lam := (div_pos (curvature_pos D G η hD hG hη) (by norm_num)).le
  let w := S.prediction
  let P := fun e : HistoryExpert T K=>if e ∈ liveExperts T K (t.val+1) then
    (S.histories e).historyUpdate W lam (q e.2) hlam (hq e.2) g w.val else S.histories e
  have hP : ∀ e,WithLp.toLp 2 (P e).mean ∈ W.carrier := by
    intro e
    dsimp [P]
    split_ifs
    · exact PrecisionGaussian.historyUpdate_feasible _ W _ _ _ _ _ _
    · exact S.feasible e
  let raw := S.weights.exponential lam (fun e=>coordinateSurrogate γ g w.val (S.histories e).mean)
  let fresh : Fin (T+1) := ⟨t.val+1,by omega⟩
  let α := 1/(t.val+2 : ℝ)
  have ha : 0<α := by dsimp [α]; positivity
  have hb : α≤1 := by
    dsimp [α]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg t.val (α := ℝ)]
  let p := raw.pruneShare (birthPrior T K fresh) α ha hb (liveExperts T K (t.val+2))
    (fun e he=>birthPrior_live fresh e he)
  exact ⟨P,hP,p⟩

theorem one_gradient_suffices {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0<D) (hG : 0<G) (hη : 0<η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k,0<q k) (t : Fin T) (f : Loss d) :
    S.step hD hG hη q hq t f=
      S.stepWithGradient hG hη hD q hq t (selectedGradient W G f S.prediction) := rfl

/-- No function values or gradients at other predictions are needed by
the curved branch once its one actual-prediction gradient is supplied. -/
theorem sparse_update_depends_only_on_actual_gradient {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0<D) (hG : 0<G) (hη : 0<η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k,0<q k) (t : Fin T) (f h : Loss d)
    (he : selectedGradient W G f S.prediction=selectedGradient W G h S.prediction) :
    S.step hD hG hη q hq t f=S.step hD hG hη q hq t h := by
  rw [one_gradient_suffices,one_gradient_suffices,he]

end Paper254
#print axioms Paper254.one_gradient_suffices
#print axioms Paper254.sparse_update_depends_only_on_actual_gradient
