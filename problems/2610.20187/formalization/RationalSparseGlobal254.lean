import RationalSparseLocal254
import StandardRationalPrefix254
import RobustGlobal254
import SparseFixedScale254

noncomputable section
open scoped BigOperators
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def masterBudget : ℝ := Real.log ((T : ℝ)/standardBirthMass T K C.master_precision)/(C.lam : ℝ)
def masterError : ℝ := standardMasterError T K C.master_precision

theorem prefix_bound (u : ℕ → W.carrier) (k : Fin (K+1)) (i n : ℕ)
    (hn : 0 < n) (hend : i+n ≤ T) (halive : HistoryActive (i+n) (i+1)) :
    intervalCharge (C.regretCharge u k) i n ≤ intervalCharge (C.historyCharge u k i) i n+
      C.masterBudget+intervalCharge (fun _ => C.masterError) i n/(C.lam : ℝ) := by
  have hp := standardRationalRun_prefix W C.diameter_pos C.gradient_pos C.curvature_pos
    C.oracle C.allCfg C.master_precision C.lam C.lam_eq C.allLo (C.hi : ℝ) C.initial rfl
    C.query C.invariant C.query_bound i (n-1) (by omega) k
    (by simpa only [show i+(n-1)+1=i+n by omega] using halive)
  have hn' : n-1+1=n := by omega
  rw [hn'] at hp
  have he : intervalCharge (C.regretCharge u k) i n-intervalCharge (C.historyCharge u k i) i n=
      cumulative (fun j => rationalSparseDifference C.lam (C.run (i+j)) (C.gradient (i+j))
        (C.expert i k)) n := by
    simp only [intervalCharge, cumulative, ←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j hj => C.regretCharge_sub_historyCharge u k i (i+j))
  have hindex : C.expert i k=numberedExpertEquiv T K (⟨i,by omega⟩,k) := by
    simp [expert, Nat.min_eq_left (by omega : i ≤ T)]
  rw [hindex] at he
  change cumulative (fun j => rationalSparseDifference C.lam (C.run (i+j)) (C.gradient (i+j))
    (numberedExpertEquiv T K (⟨i,by omega⟩,k))) n ≤ C.masterBudget+
      ((n-1 : ℕ)+1 : ℝ)*C.masterError/(C.lam : ℝ) at hp
  have hnreal : ((n-1 : ℕ) : ℝ)+1=n := by
    exact_mod_cast hn'
  rw [hnreal] at hp
  have hc : intervalCharge (fun _ => C.masterError) i n=(n : ℝ)*C.masterError := by
    simp [intervalCharge]
  rw [hc]
  linarith [hp]

/-- Actual rational states instantiate every local condition of the
history theorem: positivity, birth, update, movement, and master prefixes. -/
def historySystem (u : ℕ → W.carrier) (k : Fin (K+1)) :
    InexactHistorySystem T (C.regretCharge u k) (C.movementLength u)
      (fun _ => C.localError k) (fun _ => C.masterError) (C.lam : ℝ)
      C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lo k : ℝ) where
  charge := C.historyCharge u k
  pre := C.prePotential u k
  post := C.postPotential u k
  pre_nonneg i t := (C.gaussian i t k).potential_nonneg _ (C.lo_pos k) _
  post_nonneg i t := (C.gaussian i (t+1) k).potential_nonneg _ (C.lo_pos k) _
  birth i hi := C.birth i k hi (u i)
  step i t hit ht ha := C.local_step u k i t hit ht ha
  movement i t _ _ _ := C.potential_movement u k i t
  prefix_bound i n hn hend ha := C.prefix_bound u k i n hn hend ha

theorem masterBudget_nonneg (hT : 0 < T) : 0 ≤ C.masterBudget := by
  apply div_nonneg _ C.lam_pos.le
  apply Real.log_nonneg
  have hq := standardBirthMass_pos T K C.master_precision
  have hq1 : standardBirthMass T K C.master_precision ≤ 1 :=
    (standardBirthMass_le T K C.master_precision).trans
      ((div_le_one (by positivity : 0 < (K+1 : ℝ))).mpr (by linarith [Nat.cast_nonneg K (α := ℝ)]))
  exact (le_div_iff₀ hq).mpr (by
    have ht : (1 : ℝ) ≤ T := by exact_mod_cast hT
    simpa only [one_mul] using hq1.trans ht)

/-- Global fixed-scale comparison of the computed rational learner,
with all numerical errors charged exactly once. -/
theorem fixed_scale (hT : 0 < T) (u : ℕ → W.carrier) (k : Fin (K+1))
    (L : ℕ) (hL : 1 ≤ L) (hpow : T < 2^L) :
    intervalCharge (C.regretCharge u k) 0 T ≤
      restartThreshold L C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lam : ℝ)/64*
        (1+intervalCharge (C.movementLength u) 0 (T-1)/
          variationThreshold L C.masterBudget (birthBudget d D (C.lo k : ℝ)) (C.lam : ℝ) (C.lo k : ℝ))+
        T*(C.localError k+C.masterError)/(C.lam : ℝ) := by
  have hf := (C.historySystem u k).fixed_scale C.lam_pos (C.masterBudget_nonneg hT)
    (birthBudget_positive d D _ C.diameter_pos (C.lo_pos k)) (C.lo_pos k)
    (fun _ => norm_nonneg _) L hL hpow
  simpa [totalLocalError,intervalCharge,mul_add] using hf

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.historySystem
#print axioms Paper254.RationalSparseConstruction.fixed_scale
