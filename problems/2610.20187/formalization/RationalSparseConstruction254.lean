import RationalSparseBirth254
import StandardRationalSchedule254
import RationalPotential254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Numerical input conditions for the executable rational learner.  All
fields concern the domain, oracle, precision, or loss-query interface. -/
structure RationalSparseConstruction (d T K : ℕ) (D G eta : ℝ) (W : Domain d D) where
  dimension_pos : 0 < d
  diameter_pos : 0 < D
  gradient_pos : 0 < G
  curvature_pos : 0 < eta
  oracle : RationalProjectionProcedure d
  oracle_spec : RationalProjectionSpec W oracle
  hi : ℚ
  hi_eq : (hi : ℝ) = D^2
  lo : Fin (K+1) → ℚ
  lo_pos : ∀ k, 0 < (lo k : ℝ)
  lo_le_hi : ∀ k, (lo k : ℝ) ≤ (hi : ℝ)
  cfg : Fin (K+1) → RationalHistoryParameters
  guards : ∀ k, UniformHistoryGuards d (cfg k) (lo k : ℝ) (hi : ℝ)
  margin : Fin (K+1) → ℝ
  margin_nonneg : ∀ k, 0 ≤ margin k
  lower_error : ∀ k, |((cfg k).lowerThreshold : ℝ)-(lo k : ℝ)| ≤ margin k
  upper_error : ∀ k, |((cfg k).upperThreshold : ℝ)-(hi : ℝ)| ≤ margin k
  lam : ℚ
  lam_eq : 2*(lam : ℝ) = curvature D G eta
  master_precision : ℕ
  initial_mean : Fin d → ℚ
  initial_feasible : WithLp.toLp 2 (fun j => (initial_mean j : ℝ)) ∈ W.carrier
  query : ℕ → RationalGradientQuery d
  query_bound : ∀ t w, WithLp.toLp 2 (fun j => (w j : ℝ)) ∈ W.carrier →
    ‖WithLp.toLp 2 (fun j => (query t w j : ℝ))‖ ≤ G

namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def allCfg (e : Fin ((T+1)*(K+1))) := C.cfg ((numberedExpertEquiv T K).symm e).2
def allLo (e : Fin ((T+1)*(K+1))) : ℝ := C.lo ((numberedExpertEquiv T K).symm e).2
def initial := initialRationalSparse C.initial_mean C.hi (numberedBirthPrior T K 0)
def run := rationalSparseRun C.oracle C.allCfg C.master_precision C.lam
  (standardRationalSchedule T K) C.initial C.query
def prediction (t : ℕ) := rationalSparsePrediction (C.run t)
def gradient (t : ℕ) := C.query t (C.prediction t)

theorem hi_pos : 0 < (C.hi : ℝ) := by rw [C.hi_eq]; exact sq_pos_of_pos C.diameter_pos
theorem lam_pos : 0 < (C.lam : ℝ) := by
  have h := Paper254.curvature_pos D G eta C.diameter_pos C.gradient_pos C.curvature_pos
  linarith [C.lam_eq]

theorem initial_invariant : RationalSparseInvariant W C.allLo (C.hi : ℝ)
    ((standardRationalSchedule T K).live 0) C.initial := by
  apply initialRationalSparse_invariant W C.initial_mean C.initial_feasible C.hi C.hi_pos
    (fun e => C.lo ((numberedExpertEquiv T K).symm e).2)
    (fun e => C.lo_le_hi _) _ _ (numberedBirthPrior_nonneg T K 0)
    (numberedBirthPrior_total T K 0)
  intro e he
  by_contra hn
  have hp : 0 < numberedBirthPrior T K 0 e :=
    lt_of_le_of_ne (numberedBirthPrior_nonneg T K 0 e) (Ne.symm hn)
  have hl := numberedBirthPrior_live T K 0 e hp
  apply he
  change e ∈ Finset.map _ (shortLiveExperts T K (min 0 T+1))
  apply Finset.mem_map.mpr
  exact ⟨(numberedExpertEquiv T K).symm e, by simpa using hl,
    (numberedExpertEquiv T K).apply_symm_apply e⟩

theorem invariant (t : ℕ) : RationalSparseInvariant W C.allLo (C.hi : ℝ)
    ((standardRationalSchedule T K).live t) (C.run t) :=
  rationalSparseRun_invariant C.dimension_pos W C.diameter_pos C.gradient_pos C.curvature_pos
    C.oracle C.oracle_spec C.allCfg C.master_precision C.lam C.lam_eq C.allLo (C.hi : ℝ)
    (fun e => C.lo_pos _) C.hi_pos (fun e => C.guards _) _ (standardRationalSchedule_spec T K)
    C.initial C.initial_invariant C.query C.query_bound t

theorem prediction_feasible (t : ℕ) :
    WithLp.toLp 2 (fun j => (C.prediction t j : ℝ)) ∈ W.carrier :=
  (C.invariant t).prediction_feasible

theorem gradient_bound (t : ℕ) : ‖WithLp.toLp 2 (fun j => (C.gradient t j : ℝ))‖ ≤ G :=
  C.query_bound t _ (C.prediction_feasible t)

def expert (_ : RationalSparseConstruction d T K D G eta W) (i : ℕ) (k : Fin (K+1)) : Fin ((T+1)*(K+1)) :=
  numberedExpertEquiv T K (⟨min i T, by omega⟩, k)

@[simp] theorem expert_cfg (i : ℕ) (k : Fin (K+1)) : C.allCfg (C.expert i k) = C.cfg k := by
  simp [allCfg, expert]
@[simp] theorem expert_lo (i : ℕ) (k : Fin (K+1)) : C.allLo (C.expert i k) = (C.lo k : ℝ) := by
  simp [allLo, expert]

theorem history_invariant (i t : ℕ) (k : Fin (K+1)) :
    RationalHistoryInvariant W (C.lo k : ℝ) (C.hi : ℝ) ((C.run t).histories (C.expert i k)) := by
  simpa using (C.invariant t).histories (C.expert i k)

def gaussian (i t : ℕ) (k : Fin (K+1)) : PrecisionGaussian d :=
  ((C.run t).histories (C.expert i k)).gaussian (C.history_invariant i t k).covariance_pos

theorem expert_live (i t : ℕ) (k : Fin (K+1)) (hi : i ≤ T) (ht : t ≤ T)
    (hactive : HistoryActive (t+1) (i+1)) :
    C.expert i k ∈ (standardRationalSchedule T K).live t := by
  apply (standardRationalSchedule_live ht _).mpr
  simpa [expertBirth, Nat.min_eq_left hi] using hactive

theorem birth (i : ℕ) (k : Fin (K+1)) (hi : i < T) (u : W.carrier) :
    (C.gaussian i i k).potential (C.lo k : ℝ) u.val ≤ birthBudget d D (C.lo k : ℝ) := by
  have hu : (C.run i).histories (C.expert i k) = rationalHistoryInitial C.initial_mean C.hi := by
    apply rationalSparseRun_unborn
    intro t ht he
    have ha := (standardRationalSchedule_live (by omega : t ≤ T) _).mp he
    have hb : i+1 ≤ t+1 := by
      simpa [expert, expertBirth, Nat.min_eq_left (by omega : i ≤ T)] using ha.2.1
    omega
  have hc := (C.history_invariant i i k).covariance_pos
  unfold gaussian
  simp only [hu] at hc ⊢
  exact rationalHistoryInitial_birth W C.diameter_pos C.initial_mean C.initial_feasible C.hi
    C.hi_eq hc _ (C.lo_pos k) u

def localError (k : Fin (K+1)) : ℝ := actualHistoryLocalError d D (C.lo k : ℝ) (C.hi : ℝ)
  G (C.lam : ℝ) (C.cfg k) (C.margin k)

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.invariant
#print axioms Paper254.RationalSparseConstruction.birth
