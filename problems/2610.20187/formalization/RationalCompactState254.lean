import RationalSparseConstruction254
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open scoped BigOperators
namespace Paper254

structure CompactRationalSparseData (d n : ℕ) (live : Finset (Fin n)) where
  histories : live → RationalHistoryData d
  weights : live → ℚ

namespace CompactRationalSparseData
variable {d n : ℕ} {live : Finset (Fin n)}

@[ext] theorem ext (S R : CompactRationalSparseData d n live)
    (hh : ∀ e,S.histories e=R.histories e) (hw : ∀ e,S.weights e=R.weights e) : S=R := by
  cases S
  cases R
  congr 1 <;> funext e
  · exact hh e
  · exact hw e

def restrict (S : RationalSparseData d n) (live : Finset (Fin n)) : CompactRationalSparseData d n live :=
  ⟨fun e => S.histories e.val, fun e => S.weights e.val⟩

def weightView (S : CompactRationalSparseData d n live) (e : Fin n) : ℚ :=
  if he : e∈live then S.weights ⟨e,he⟩ else 0

def prediction (S : CompactRationalSparseData d n live) : Fin d → ℚ :=
  fun j => ∑ e : live,S.weights e*(S.histories e).mean j

/-- A semantic view with one shared initial state for omitted keys. -/
def ambient (S : CompactRationalSparseData d n live) (initial : RationalHistoryData d) : RationalSparseData d n where
  histories e := if he : e∈live then S.histories ⟨e,he⟩ else initial
  weights := S.weightView

theorem weightView_support (S : CompactRationalSparseData d n live) :
    ∀ e,e∉live → S.weightView e=0 := by intro e he; simp [weightView,he]

theorem restrict_ambient (S : CompactRationalSparseData d n live) (initial : RationalHistoryData d) :
    restrict (S.ambient initial) live=S := by
  apply ext <;> intro e <;> simp [restrict,ambient,weightView,e.property]

theorem restrict_weightView (S : RationalSparseData d n)
    (hs : ∀ e,e∉live → S.weights e=0) : (restrict S live).weightView=S.weights := by
  funext e
  by_cases he : e∈live <;> simp [weightView,restrict,he,hs e]

theorem restrict_prediction (S : RationalSparseData d n)
    (hs : ∀ e,e∉live → S.weights e=0) : (restrict S live).prediction=rationalSparsePrediction S := by
  funext j
  unfold prediction
  simp only [restrict]
  change (∑ e : live,(fun x : Fin n => S.weights x*(S.histories x).mean j) e.val)=_
  rw [Finset.sum_coe_sort live (fun x => S.weights x*(S.histories x).mean j)]
  exact Finset.sum_subset (Finset.subset_univ _) (by intro e he hn; simp [hs e hn])

theorem ambient_prediction (S : CompactRationalSparseData d n live) (initial : RationalHistoryData d) :
    rationalSparsePrediction (S.ambient initial)=S.prediction := by
  have hh := restrict_prediction (S.ambient initial) S.weightView_support
  rw [restrict_ambient] at hh
  exact hh.symm

def exponents (S : CompactRationalSparseData d n live) (lam : ℚ) (g : Fin d → ℚ) (e : Fin n) : ℚ :=
  if he : e∈live then -lam*rationalCoordinateSurrogate lam g S.prediction (S.histories ⟨e,he⟩).mean else 0

/-- Every stored history is produced by one update of a surviving key or
by initialization of a newborn key. No discarded history is accessed. -/
def step (S : CompactRationalSparseData d n live) (oracle : RationalProjectionProcedure d)
    (cfg : Fin n → RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (next : Finset (Fin n)) (prior : Fin n → ℚ) (alpha : ℚ)
    (initialHistory : RationalHistoryData d) (g : Fin d → ℚ) : CompactRationalSparseData d n next where
  histories e := if he : e.val∈live then
    rationalHistoryStep oracle (cfg e.val) (S.histories ⟨e.val,he⟩) lam g S.prediction
    else initialHistory
  weights e := rationalMasterUpdate p live next S.weightView (S.exponents lam g) prior alpha e.val

end CompactRationalSparseData
end Paper254
#print axioms Paper254.CompactRationalSparseData.restrict_prediction
