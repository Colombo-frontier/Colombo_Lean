import SparseErasure254
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

noncomputable section
open scoped BigOperators
namespace Paper254

@[ext] theorem ProbabilityWeights.ext {ι : Type*} [Fintype ι] (p q : ProbabilityWeights ι)
    (h : ∀ e,p.weight e=q.weight e) : p=q := by
  cases p; cases q
  congr
  funext e
  exact h e

structure CompactSparseState {d : ℕ} {D : ℝ} (W : Domain d D) (T K t : ℕ) where
  histories : (liveExperts T K t) → PrecisionGaussian d
  feasible : ∀ e,WithLp.toLp 2 (histories e).mean ∈ W.carrier
  weights : ProbabilityWeights (liveExperts T K t)

@[ext] theorem CompactSparseState.ext {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S R : CompactSparseState W T K t)
    (hh : ∀ e,S.histories e=R.histories e)
    (hw : ∀ e,S.weights.weight e=R.weights.weight e) : S=R := by
  have hweights : S.weights=R.weights := ProbabilityWeights.ext _ _ hw
  have hhistories : S.histories=R.histories := funext hh
  cases S; cases R
  simp_all

def SparseMasterState.restrict {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K)
    (hz : ∀ e,e ∉ liveExperts T K t → S.weights.weight e=0) : CompactSparseState W T K t := by
  classical
  refine ⟨fun e=>S.histories e.val,fun e=>S.feasible e.val,
    ⟨fun e=>S.weights.weight e.val,fun e=>S.weights.nonneg e.val,?_⟩⟩
  rw [Finset.sum_coe_sort]
  calc
    _ = ∑ e,S.weights.weight e := Finset.sum_subset (Finset.subset_univ _)
      (fun e _ he=>hz e he)
    _ = 1 := S.weights.total

def CompactSparseState.expand {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S : CompactSparseState W T K t) (hD : 0 < D) (w0 : W.carrier) : SparseMasterState W T K := by
  classical
  let hs := fun e : HistoryExpert T K => if he : e ∈ liveExperts T K t then
    S.histories ⟨e,he⟩ else isotropicGaussian w0.val D hD
  let p := fun e : HistoryExpert T K => if he : e ∈ liveExperts T K t then S.weights.weight ⟨e,he⟩ else 0
  refine ⟨hs,?_,⟨p,?_,?_⟩⟩
  · intro e
    dsimp [hs]
    split_ifs with he
    · exact S.feasible ⟨e,he⟩
    · exact w0.property
  · intro e
    dsimp [p]
    split_ifs with he
    · exact S.weights.nonneg ⟨e,he⟩
    · rfl
  · dsimp [p]
    rw [← Finset.sum_attach_eq_sum_dite]
    exact S.weights.total

theorem restrict_expand_weights {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (w0 : W.carrier)
    (hz : ∀ e,e ∉ liveExperts T K t → S.weights.weight e=0) (e : HistoryExpert T K) :
    ((S.restrict hz).expand hD w0).weights.weight e=S.weights.weight e := by
  classical
  by_cases he : e ∈ liveExperts T K t
  · simp [SparseMasterState.restrict,CompactSparseState.expand,he]
  · simp [CompactSparseState.expand,he,hz e he]

theorem restrict_expand_histories {d T K t : ℕ} {D : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (w0 : W.carrier)
    (hz : ∀ e,e ∉ liveExperts T K t → S.weights.weight e=0)
    (e : HistoryExpert T K) (he : e ∈ liveExperts T K t) :
    ((S.restrict hz).expand hD w0).histories e=S.histories e := by
  classical
  simp [SparseMasterState.restrict,CompactSparseState.expand,he]

theorem SparseMasterState.step_support {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (S : SparseMasterState W T K) (hD : 0 < D) (hG : 0 < G) (hη : 0 < η)
    (q : Fin (K+1) → ℝ) (hq : ∀ k,0<q k) (t : Fin T) (f : Loss d)
    (e : HistoryExpert T K) (he : e ∉ liveExperts T K (t.val+2)) :
    (S.step hD hG hη q hq t f).weights.weight e=0 := by
  classical
  simp [SparseMasterState.step,ProbabilityWeights.pruneShare,
    ProbabilityWeights.prunedMixtureMass,he]

def CompactSparseState.step {d T K : ℕ} {D G η : ℝ} {W : Domain d D}
    (t : Fin T) (S : CompactSparseState W T K (t.val+1))
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k,0<q k) (f : Loss d) :
    CompactSparseState W T K (t.val+2) :=
  ((S.expand hD w0).step hD hG hη q hq t f).restrict
    ((S.expand hD w0).step_support hD hG hη q hq t f)

/-- The stored state contains only live histories. Expanding it is a
mathematical view; the next compact state depends on no deleted data. -/
theorem compact_step_agrees_with_actual {d T K : ℕ} {D G η : ℝ} (W : Domain d D)
    (hD : 0 < D) (hG : 0 < G) (hη : 0 < η) (w0 : W.carrier)
    (q : Fin (K+1) → ℝ) (hq : ∀ k,0<q k) (f : ℕ → Loss d) (t : Fin T) :
    let S := sparseTrajectory (T := T) W hD hG hη w0 q hq f t.val
    let hz := sparseTrajectory_support W hD hG hη w0 q hq f t.val (Nat.le_of_lt t.isLt)
    (S.step hD hG hη q hq t (f t.val)).restrict (S.step_support hD hG hη q hq t (f t.val)) =
      (S.restrict hz).step t hD hG hη w0 q hq (f t.val) := by
  classical
  dsimp only
  let S := sparseTrajectory (T := T) W hD hG hη w0 q hq f t.val
  let hz := sparseTrajectory_support W hD hG hη w0 q hq f t.val (Nat.le_of_lt t.isLt)
  let R := (S.restrict hz).expand hD w0
  have hw : ∀ e,S.weights.weight e=R.weights.weight e := fun e=>(restrict_expand_weights S hD w0 hz e).symm
  have hh : ∀ e,e ∈ liveExperts T K (t.val+1) → S.histories e=R.histories e :=
    fun e he=>(restrict_expand_histories S hD w0 hz e he).symm
  have hp := S.prediction_eq_of_live R hw hz hh
  have hraw := S.rawWeights_eq_of_live (G := G) (η := η) R (f t.val) hw hz hh
  apply CompactSparseState.ext
  · intro e
    change (S.step hD hG hη q hq t (f t.val)).histories e.val =
      (R.step hD hG hη q hq t (f t.val)).histories e.val
    rw [SparseMasterState.step_histories,SparseMasterState.step_histories]
    by_cases he : e.val ∈ liveExperts T K (t.val+1)
    · rw [if_pos he,if_pos he,hh e.val he,hp]
    · rw [if_neg he,if_neg he]
      have hb := (next_live_or_birth e.val e.property).resolve_left he
      have hinit := sparseHistory_before_birth W hD hG hη w0 q hq f e.val t.val (by omega)
      change S.histories e.val=_ at hinit
      rw [hinit]
      simp [R,CompactSparseState.expand,he]
  · intro e
    change (S.step hD hG hη q hq t (f t.val)).weights.weight e.val =
      (R.step hD hG hη q hq t (f t.val)).weights.weight e.val
    have hraw' : S.rawWeights (G := G) (η := η) (f t.val)=R.rawWeights (G := G) (η := η) (f t.val) :=
      ProbabilityWeights.ext _ _ hraw
    let fresh : Fin (T+1) := ⟨t.val+1,by omega⟩
    have ha : 0 < 1/(t.val+2 : ℝ) := by positivity
    have hb : 1/(t.val+2 : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg t.val (α := ℝ)]
    have hprior : ∀ j,0 < (birthPrior T K fresh).weight j → j ∈ liveExperts T K (t.val+2) :=
      fun j hj=>birthPrior_live fresh j hj
    have hpw := congrArg (fun p : ProbabilityWeights (HistoryExpert T K)=>
      (p.pruneShare (birthPrior T K fresh) (1/(t.val+2 : ℝ)) ha hb
        (liveExperts T K (t.val+2)) hprior).weight e.val) hraw'
    exact hpw

end Paper254
#print axioms Paper254.compact_step_agrees_with_actual
