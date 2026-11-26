import GradientHessian.ClockedOracleExpansionRun
import GradientHessian.ClockedOracleExpansionCounts
import GradientHessian.NalenDifferenceBatch
import GradientHessian.NalenPolicyCounts
import GradientHessian.NalenApproximateTrajectory

/-! A literal ordinary-only NALEN machine. Each virtual snapshot is
implemented by d+1 actual ordinary queries, and exact execution equality
connects its output to the proved approximate-Hessian trajectory. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen MeasureTheory
open scoped ENNReal

def ordinaryProgram (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) :=
  (program d hD η m q N).expand (differenceBatch d ((m:ℝ)*D))

def ordinaryPolicy (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) :=
  (ordinaryProgram d hD η m q N).policy

def ordinaryAlgorithm (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) : Algorithm d where
  Seed := PUnit
  State := ℕ × (Data (Point d) × (Fin (d+1) → OrdinaryReply d))
  seedSpace := inferInstance
  stateSpace := inferInstance
  seedLaw := Measure.dirac PUnit.unit
  probability := inferInstance
  policy := ordinaryPolicy d hD η m q N

theorem ordinaryPolicy_terminates (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ)
    (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    (ordinaryPolicy d hD η m q N).Terminates ordinary rich :=
  (ordinaryProgram d hD η m q N).terminates ordinary rich

theorem ordinaryPolicy_output (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ)
    (f : Point d → ℝ) (seed : PUnit) :
    (ordinaryPolicy d hD η m q N).output
      ((ordinaryPolicy d hD η m q N).run (ordinaryOracle f) (richOracle f)
        ((1+4*N)*(d+2)) seed)=
      (policy d hD η m q N).output ((policy d hD η m q N).run
        (ordinaryOracle f) (differenceRich ((m:ℝ)*D) f) (1+4*N) seed) :=
  (program d hD η m q N).expanded_output (differenceBatch d ((m:ℝ)*D))
    (ordinaryOracle f) (richOracle f) seed

theorem ordinaryPolicy_exact_caps (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) (hm : 0<m)
    (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    (ordinaryPolicy d hD η m q N).HasCaps ordinary rich
      (1+2*N+N/q+(d+1)*((N+m-1)/m)) 0 := by
  have h := (program d hD η m q N).expanded_caps (differenceBatch d ((m:ℝ)*D)) ordinary rich
  change (ordinaryPolicy d hD η m q N).HasCaps ordinary rich
    ((∑ k ∈ Finset.range (1+4*N),if kind m q k=1 then 1 else 0)+
      (d+1)*(∑ k ∈ Finset.range (1+4*N),if kind m q k=2 then 1 else 0)) 0 at h
  rwa [ordinary_schedule_count,rich_schedule_count m q N hm] at h

theorem ordinaryPolicy_source_caps {d : ℕ} (hd : 1≤d) {D : ℝ} (hD : 0≤D) (η : ℝ) (q N : ℕ)
    (ordinary : Point d → OrdinaryReply d) (rich : Point d → RichReply d) :
    (ordinaryPolicy d hD η d q N).HasCaps ordinary rich
      (3*N+1+2*d*((N+d-1)/d)) 0 := by
  intro seed n
  obtain ⟨ho,hr⟩ := ordinaryPolicy_exact_caps d hD η d q N (by omega) ordinary rich seed n
  refine ⟨ho.trans ?_,hr⟩
  have hdiv := Nat.div_le_self N q
  have hmul := Nat.mul_le_mul_right ((N+d-1)/d) (show d+1≤2*d by omega)
  omega

theorem ordinaryPolicy_stationary {d q K N : ℕ} {T : ℝ}
    (hd : 1≤d) (hq : 1≤q) (hK : 1≤K) (hdq : d≤q^3) (hKq : K*q≤N) (hTK : 256*T≤(K:ℝ))
    (f : Point d → ℝ) (hf : Admissible T f) (seed : PUnit) :
    ‖gradient f ((ordinaryPolicy d (stepRadius_pos hq).le (stepSize d q) d q N).output
      ((ordinaryPolicy d (stepRadius_pos hq).le (stepSize d q) d q N).run
        (ordinaryOracle f) (richOracle f) ((1+4*N)*(d+2)) seed))‖≤1 := by
  rw [ordinaryPolicy_output]
  apply virtual_tuned_output_stationary d q f (differenceRich ((d:ℝ)*stepRadius q) f)
    hf hd hq K N hK hdq hKq hTK
  · exact differenceRich_symmetric _ f
  · intro z
    exact differenceRich_error (by omega) (mul_pos (by exact_mod_cast (show 0<d by omega)) (stepRadius_pos hq))
      hf.smooth hf.hessianLip z

theorem ordinaryAlgorithm_guarantees {d q K N : ℕ} {T : ℝ}
    (hd : 1≤d) (hq : 1≤q) (hK : 1≤K) (hdq : d≤q^3) (hKq : K*q≤N) (hTK : 256*T≤(K:ℝ)) :
    (ordinaryAlgorithm d (stepRadius_pos hq).le (stepSize d q) d q N).Guarantees T
      (3*N+1+2*d*((N+d-1)/d)) 0 := by
  intro f hf
  refine ⟨?_,?_,?_⟩
  · exact (ordinaryPolicy d (stepRadius_pos hq).le (stepSize d q) d q N).terminatesAlmostSurely_of_terminates
      (ordinaryOracle f) (richOracle f) (Measure.dirac PUnit.unit)
      (ordinaryPolicy_terminates d (stepRadius_pos hq).le (stepSize d q) d q N _ _)
  · exact ordinaryPolicy_source_caps hd (stepRadius_pos hq).le (stepSize d q) q N _ _
  · have hs : (ordinaryPolicy d (stepRadius_pos hq).le (stepSize d q) d q N).success
        (ordinaryOracle f) (richOracle f) (stationary f)=Set.univ := by
      apply Set.eq_univ_of_forall
      intro seed
      refine ⟨(1+4*N)*(d+2),?_,?_⟩
      · exact (ordinaryProgram d (stepRadius_pos hq).le (stepSize d q) d q N).halt _ _ seed
      · exact (stationary_iff_gradient f _).2 (ordinaryPolicy_stationary hd hq hK hdq hKq hTK f hf seed)
    change (2/3:ℝ≥0∞)≤(Measure.dirac PUnit.unit)
      ((ordinaryPolicy d (stepRadius_pos hq).le (stepSize d q) d q N).success
        (ordinaryOracle f) (richOracle f) (stationary f))
    rw [hs]
    simp only [MeasureTheory.measure_univ]
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).2 (by norm_num)

end GradientHessian.NalenPolicy
