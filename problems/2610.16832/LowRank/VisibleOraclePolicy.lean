import LowRank.FactorReply
import LowRank.FactorProcess

/-! A finite measurable oracle policy whose only inputs are its seed, past
actual ambient replies, and the visible factors reconstructed from them. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section
universe u

def OracleHistory (d : ℕ) : ℕ → Type u → Type u
  | 0, S => S
  | n + 1, S => OracleHistory d n (S × (Fin d → ℝ))

instance oracleHistoryMeasurable (d n : ℕ) (S : Type u) [MeasurableSpace S] :
    MeasurableSpace (OracleHistory d n S) := by
  induction n generalizing S with
  | zero => exact inferInstanceAs (MeasurableSpace S)
  | succ n ih => exact ih (S × (Fin d → ℝ))

def VisibleOraclePolicy (d r : ℕ) : (n q : ℕ) → (S : Type u) → [MeasurableSpace S] → Type u
  | 0, _, _, _ => PUnit
  | n + 1, q, S, _ =>
      {u : S × VisibleFactorData d q (r + n + 1) → Fin (r + n + 1) → ℝ // Measurable u} ×
        VisibleOraclePolicy d r n (q + 1) (S × (Fin d → ℝ))

def VisibleOraclePolicy.IsUnit (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    VisibleOraclePolicy d r n q S → Prop
  | 0, _, _, _, _ => True
  | n + 1, _, _, _, policy =>
      (∀ p, ‖(basisCoordinates (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ)).symm
        (policy.1.1 p)‖ = 1) ∧ VisibleOraclePolicy.IsUnit d r n _ policy.2

def ambientQuery {d q r : ℕ} (vis : VisibleFactorData d q r) (u : Fin r → ℝ) : Fin d → ℝ :=
  vis.2 *ᵥ Sum.elim 0 u

theorem measurable_visibleFactorData (d t q r s : ℕ) :
    Measurable (visibleFactorData (d := d) (t := t) (q := q) (r := r) (s := s)) :=
  measurable_fst.prodMk measurable_snd.fst

theorem measurable_ambientQuery {S : Type*} [MeasurableSpace S] {d q r : ℕ}
    (vis : S → VisibleFactorData d q r) (u : S → Fin r → ℝ)
    (hv : Measurable vis) (hu : Measurable u) : Measurable (fun x => ambientQuery (vis x) (u x)) := by
  have hz : Measurable (fun x => Sum.elim (0 : Fin q → ℝ) (u x)) := by
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl i => exact measurable_const
    | inr i => exact (measurable_pi_apply i).comp hu
  unfold ambientQuery
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

def visibleOracleStep {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d q r : ℕ} (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : S × VisibleFactorData d q (r + 1) → Fin (r + 1) → ℝ)
    (W : Matrix (Fin d) (Fin d) ℝ) (p : S × VisibleFactorData d q (r + 1)) :
    (S × (Fin d → ℝ)) × VisibleFactorData d (q + 1) r :=
  let reply := W *ᵥ ambientQuery p.2 (u p)
  ((p.1, reply), recoverVisibleFactorData b (u p) p.2 reply)

theorem measurable_visibleOracleStep {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace S]
    {d q r : ℕ} (b : OrthonormalBasis (Fin (r + 1)) ℝ E)
    (u : S × VisibleFactorData d q (r + 1) → Fin (r + 1) → ℝ) (hu : Measurable u) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × (S × VisibleFactorData d q (r + 1)) =>
      visibleOracleStep b u p.1 p.2) := by
  have hq : Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × (S × VisibleFactorData d q (r + 1)) =>
      ambientQuery p.2.2 (u p.2)) :=
    measurable_ambientQuery _ _ measurable_snd.snd (hu.comp measurable_snd)
  have hr : Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × (S × VisibleFactorData d q (r + 1)) =>
      p.1 *ᵥ ambientQuery p.2.2 (u p.2)) := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  exact (measurable_snd.fst.prodMk hr).prodMk
    (measurable_recoverVisibleFactorData b _ _ _ (hu.comp measurable_snd) measurable_snd.snd hr)

def runVisibleOracle (d r : ℕ) : (n q : ℕ) → {S : Type u} → [MeasurableSpace S] →
    VisibleOraclePolicy d r n q S → Matrix (Fin d) (Fin d) ℝ →
    S × VisibleFactorData d q (r + n) →
    OracleHistory d n S × VisibleFactorData d (factorCount n q) r
  | 0, _, _, _, _, _, p => p
  | n + 1, q, _, _, policy, W, p => runVisibleOracle d r n (q + 1) policy.2 W
      (visibleOracleStep (EuclideanSpace.basisFun (Fin (r + n + 1)) ℝ) policy.1.1 W p)

theorem measurable_runVisibleOracle (d r n q : ℕ) {S : Type u} [MeasurableSpace S]
    (policy : VisibleOraclePolicy d r n q S) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℝ × (S × VisibleFactorData d q (r + n)) =>
      runVisibleOracle d r n q policy p.1 p.2) := by
  induction n generalizing q S with
  | zero => exact measurable_snd
  | succ n ih =>
    exact (ih (q + 1) policy.2).comp (measurable_fst.prodMk
      (measurable_visibleOracleStep _ policy.1.1 policy.1.2))

end
end LowRank
