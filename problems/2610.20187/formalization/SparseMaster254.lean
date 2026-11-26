import MasterWeights254
import GaussianOCO254
import GradientSupport254
import ScheduleCount254

noncomputable section
open scoped BigOperators
namespace Paper254

abbrev HistoryExpert (T K : ℕ) := Fin (T+1) × Fin (K+1)

def expertBirth {T K : ℕ} (e : HistoryExpert T K) : ℕ := e.1.val+1

def liveExperts (T K t : ℕ) : Finset (HistoryExpert T K) := by
  classical
  exact Finset.univ.filter (fun e => HistoryActive t (expertBirth e))

theorem mem_liveExperts {T K t : ℕ} (e : HistoryExpert T K) :
    e ∈ liveExperts T K t ↔ HistoryActive t (expertBirth e) := by
  classical
  simp [liveExperts]

def birthPrior (T K : ℕ) (i : Fin (T+1)) : ProbabilityWeights (HistoryExpert T K) := by
  classical
  refine ⟨fun e => if e.1 = i then 1/(K+1 : ℝ) else 0, ?_, ?_⟩
  · intro e
    dsimp only
    split_ifs <;> positivity
  · rw [Fintype.sum_prod_type]
    simp [show (K : ℝ)+1 ≠ 0 by positivity]

theorem birthPrior_positive {T K : ℕ} (i : Fin (T+1)) (e : HistoryExpert T K)
    (h : 0 < (birthPrior T K i).weight e) : e.1 = i := by
  classical
  by_contra he
  simp [birthPrior, he] at h

theorem birthPrior_live {T K : ℕ} (i : Fin (T+1)) (e : HistoryExpert T K)
    (h : 0 < (birthPrior T K i).weight e) : e ∈ liveExperts T K (i.val+1) := by
  apply (mem_liveExperts e).mpr
  have he := birthPrior_positive i e h
  simp only [expertBirth, he]
  exact historyActive_birth _ (by omega)

structure SparseMasterState {d : ℕ} {D : ℝ} (W : Domain d D) (T K : ℕ) where
  histories : HistoryExpert T K → PrecisionGaussian d
  feasible : ∀ e, WithLp.toLp 2 (histories e).mean ∈ W.carrier
  weights : ProbabilityWeights (HistoryExpert T K)

def SparseMasterState.prediction {d T K : ℕ} {D : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) : W.carrier :=
  weightedPrediction S.weights.weight
    (fun e => ⟨WithLp.toLp 2 (S.histories e).mean, S.feasible e⟩)
    S.weights.nonneg S.weights.total

def initialSparseState {d : ℕ} {D : ℝ} (W : Domain d D) (hD : 0 < D)
    (w0 : W.carrier) (T K : ℕ) : SparseMasterState W T K :=
  ⟨fun _ => isotropicGaussian w0.val D hD, fun _ => w0.property, birthPrior T K ⟨0, by omega⟩⟩

def SparseMasterState.step {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (t : Fin T) (f : Loss d) : SparseMasterState W T K := by
  classical
  let γ := curvature D G η
  let lam := γ/2
  have hlam : 0 ≤ lam := (div_pos (curvature_pos D G η hD hG hη) (by norm_num)).le
  let w := S.prediction
  let g := selectedGradient W G f w
  let P := fun e : HistoryExpert T K =>
    if e ∈ liveExperts T K (t.val+1) then
      (S.histories e).historyUpdate W lam (q e.2) hlam (hq e.2) g w.val else S.histories e
  have hP : ∀ e, WithLp.toLp 2 (P e).mean ∈ W.carrier := by
    intro e
    dsimp [P]
    split_ifs
    · exact PrecisionGaussian.historyUpdate_feasible _ W _ _ _ _ _ _
    · exact S.feasible e
  let raw := S.weights.exponential lam
    (fun e => coordinateSurrogate γ g w.val (S.histories e).mean)
  let fresh : Fin (T+1) := ⟨t.val+1, by omega⟩
  let α := 1/(t.val+2 : ℝ)
  have ha : 0 < α := by dsimp [α]; positivity
  have hb : α ≤ 1 := by
    dsimp [α]
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg t.val (α := ℝ)]
  let p := raw.pruneShare (birthPrior T K fresh) α ha hb (liveExperts T K (t.val+2))
    (fun e he => birthPrior_live fresh e he)
  exact ⟨P, hP, p⟩

def sparseTrajectory {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f : ℕ → Loss d) :
    ℕ → SparseMasterState W T K
  | 0 => initialSparseState W hD w0 T K
  | n+1 => if h : n < T then
      (sparseTrajectory W hD hG hη w0 q hq f n).step hD hG hη q hq ⟨n,h⟩ (f n)
    else sparseTrajectory W hD hG hη w0 q hq f n

theorem sparseTrajectory_causal {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) (f h : ℕ → Loss d) (n : ℕ)
    (heq : ∀ t < n, f t = h t) :
    sparseTrajectory (T := T) W hD hG hη w0 q hq f n =
      sparseTrajectory (T := T) W hD hG hη w0 q hq h n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := ih (fun t ht => heq t (by omega))
    simp only [sparseTrajectory]
    split_ifs with hn
    · rw [hs, heq n (by omega)]
    · exact hs

def sparseOnlineLearner {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k, 0 < q k) : OnlineLearner W T := by
  classical
  intro t pastLosses
  let f : ℕ → Loss d := fun n => if hn : n < t.val then pastLosses ⟨n,hn⟩ else fun _ => 0
  exact (sparseTrajectory (T := T) W hD hG hη w0 q hq f t.val).prediction

end Paper254
#print axioms Paper254.sparseTrajectory_causal
#check Paper254.sparseOnlineLearner
