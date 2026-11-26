import RationalHistoryInit254
import RationalMasterRegret254
import GaussianOCO254

open scoped BigOperators
open Matrix
namespace Paper254

structure RationalSparseData (d n : ℕ) where
  histories : Fin n→RationalHistoryData d
  weights : Fin n→ℚ

def rationalSparsePrediction {d n : ℕ} (S : RationalSparseData d n) : Fin d→ℚ :=
  fun j=>∑ e,S.weights e*(S.histories e).mean j

structure RationalSparseInvariant {d n : ℕ} {D : ℝ} (W : Domain d D)
    (lo : Fin n→ℝ) (hi : ℝ) (live : Finset (Fin n)) (S : RationalSparseData d n) : Prop where
  histories : ∀ e,RationalHistoryInvariant W (lo e) hi (S.histories e)
  nonneg : ∀ e,0≤S.weights e
  total : ∑ e,S.weights e=1
  support : ∀ e,e∉live → S.weights e=0

theorem rationalSparsePrediction_eq {d n : ℕ} (S : RationalSparseData d n) :
    WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ))=
      ∑ e,(S.weights e:ℝ) • WithLp.toLp 2 (fun j=>((S.histories e).mean j:ℝ)) := by
  ext j
  have hs (s : Finset (Fin n)) :
      (∑ e∈s,(S.weights e:ℝ) • WithLp.toLp 2 (fun k=>((S.histories e).mean k:ℝ))) j=
        ∑ e∈s,(S.weights e:ℝ)*((S.histories e).mean j:ℝ) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert e s he ih => simp [he,ih]
  simpa [rationalSparsePrediction] using (hs Finset.univ).symm

theorem RationalSparseInvariant.prediction_feasible {d n : ℕ} {D : ℝ} {W : Domain d D}
    {lo : Fin n→ℝ} {hi : ℝ} {live : Finset (Fin n)} {S : RationalSparseData d n}
    (h : RationalSparseInvariant W lo hi live S) :
    WithLp.toLp 2 (fun j=>(rationalSparsePrediction S j:ℝ))∈W.carrier := by
  rw [rationalSparsePrediction_eq]
  apply W.convex.sum_mem
  · intro e _
    exact Rat.cast_nonneg.mpr (h.nonneg e)
  · exact_mod_cast h.total
  · intro e _
    exact (h.histories e).feasible

def rationalCoordinateSurrogate {d : ℕ} (lam : ℚ) (g w x : Fin d→ℚ) : ℚ :=
  let z := g ⬝ᵥ (x-w)
  z+lam*z^2

theorem rationalCoordinateSurrogate_cast {d : ℕ} (lam : ℚ) (g w x : Fin d→ℚ) :
    (rationalCoordinateSurrogate lam g w x:ℝ)=coordinateSurrogate (2*(lam:ℝ))
      (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ)) (fun j=>(x j:ℝ)) := by
  simp [rationalCoordinateSurrogate,coordinateSurrogate,dotProduct]

theorem rationalExponent_bound {d : ℕ} (lam : ℚ) (g w x : Fin d→ℚ)
    (h : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(x j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4) :
    |((-lam*rationalCoordinateSurrogate lam g w x:ℚ):ℝ)|≤1/2 := by
  rw [Rat.cast_mul,Rat.cast_neg,rationalCoordinateSurrogate_cast]
  let a : ℝ := (lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(x j:ℝ))-(fun j=>(w j:ℝ))))
  have ha : -(1/8:ℝ)≤a ∧ a≤1/8 := by
    have hh := abs_le.mp h
    dsimp [a]
    constructor <;> nlinarith [hh.1,hh.2]
  have he : -(lam:ℝ)*coordinateSurrogate (2*(lam:ℝ))
      (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ)) (fun j=>(x j:ℝ))= -a-a^2 := by
    dsimp [a,coordinateSurrogate]
    ring
  rw [he]
  have hs : a^2≤1/64 := by nlinarith [mul_nonneg (by linarith : 0≤a+1/8) (by linarith : 0≤1/8-a)]
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg a],by nlinarith [sq_nonneg a]⟩

def rationalSparseExponents {d n : ℕ} (lam : ℚ) (S : RationalSparseData d n)
    (g : Fin d→ℚ) : Fin n→ℚ :=
  fun e=> -lam*rationalCoordinateSurrogate lam g (rationalSparsePrediction S) (S.histories e).mean

theorem rationalSparseExponents_bound {d n : ℕ} {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta) (lo : Fin n→ℝ) (hi : ℝ)
    (live : Finset (Fin n)) (S : RationalSparseData d n) (hS : RationalSparseInvariant W lo hi live S)
    (lam : ℚ) (hlam : 2*(lam:ℝ)=curvature D G eta) (g : Fin d→ℚ)
    (hg : ‖WithLp.toLp 2 (fun j=>(g j:ℝ))‖≤G) :
    ∀ e,|(rationalSparseExponents lam S g e:ℝ)|≤1/2 := by
  intro e
  apply rationalExponent_bound
  rw [hlam]
  exact coordinate_curvature_bound W hD hG heta _ hg
    ⟨_,(hS.histories e).feasible⟩ ⟨_,hS.prediction_feasible⟩

def rationalSparseStep {d n : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha : ℚ)
    (S : RationalSparseData d n) (g : Fin d→ℚ) : RationalSparseData d n :=
  { histories := fun e=>if e∈live then rationalHistoryStep oracle (cfg e) (S.histories e)
      lam g (rationalSparsePrediction S) else S.histories e
    weights := rationalMasterUpdate p live next S.weights (rationalSparseExponents lam S g) prior alpha }

theorem rationalSparseStep_preserves {d n : ℕ} (hd : 0<d) {D G eta : ℝ} (W : Domain d D)
    (hD : 0<D) (hG : 0<G) (heta : 0<eta)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : Fin n→RationalHistoryParameters) (p : ℕ) (lam : ℚ)
    (hlam : 2*(lam:ℝ)=curvature D G eta) (lo : Fin n→ℝ) (hi : ℝ)
    (hlo : ∀ e,0<lo e) (hhi : 0<hi) (hguard : ∀ e,UniformHistoryGuards d (cfg e) (lo e) hi)
    (live next : Finset (Fin n)) (prior : Fin n→ℚ) (alpha : ℚ)
    (hp : ∀ e,0≤prior e) (hp1 : ∑ e,prior e=1) (ha : 0<alpha) (ha1 : alpha≤1)
    (hprior : ∀ e,0<prior e → e∈next)
    (S : RationalSparseData d n) (hS : RationalSparseInvariant W lo hi live S) (g : Fin d→ℚ)
    (hg : ‖WithLp.toLp 2 (fun j=>(g j:ℝ))‖≤G) :
    RationalSparseInvariant W lo hi next (rationalSparseStep oracle cfg p lam live next prior alpha S g) := by
  have hw := rationalMasterUpdate_spec p live next S.weights (rationalSparseExponents lam S g) prior alpha
    hS.nonneg hS.total hS.support (rationalSparseExponents_bound W hD hG heta lo hi live S hS lam hlam g hg)
    hp hp1 ha ha1 hprior
  constructor
  · intro e
    change RationalHistoryInvariant W (lo e) hi (if e∈live then _ else _)
    split_ifs
    · exact rationalHistoryStep_preserves hd W oracle hspec (cfg e) (lo e) hi (hlo e) hhi
        (hguard e) (S.histories e) (hS.histories e) lam g (rationalSparsePrediction S)
    · exact hS.histories e
  · exact hw.2.1
  · exact hw.1
  · exact hw.2.2.1

end Paper254
#print axioms Paper254.rationalSparseStep_preserves
