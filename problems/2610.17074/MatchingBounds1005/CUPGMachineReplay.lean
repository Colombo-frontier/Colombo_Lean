import MatchingBounds1005.CUPGMachine
import MatchingBounds1005.CUPGOracleArray

/-! Exact execution inside a physical accelerated phase. -/
noncomputable section
namespace MatchingBounds1005.CUPG

theorem upperMachine_prefix {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N k : ℕ) (start : Model.Space d) (best : Model.Space d × ℝ)
    (hbase : (upperMachine q α τ L ε N).run f (k * phaseLength N) = ((start, fun _ => 0), best))
    (r : ℕ) (hr : r ≤ 9 * N + 2) :
    (upperMachine q α τ L ε N).run f (k * phaseLength N + r) =
      ((start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f r), best) := by
  induction r with
  | zero => simpa only [Nat.add_zero, arrayRun] using hbase
  | succ r ih =>
    have hrbody : r < 9 * N + 2 := by omega
    have hrlen : r < phaseLength N := by unfold phaseLength; omega
    have hrlen' : r + 1 < phaseLength N := by unfold phaseLength; omega
    have hmod : (k * phaseLength N + r) % phaseLength N = r := by
      simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hrlen]
    have hmod' : (k * phaseLength N + r + 1) % phaseLength N = r + 1 := by
      rw [Nat.add_assoc]
      simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hrlen']
    have hne : (k * phaseLength N + r + 1) % phaseLength N ≠ 0 := by rw [hmod']; omega
    have he : k * phaseLength N + (r + 1) = (k * phaseLength N + r) + 1 := by omega
    rw [he, RandomizedFO2003.Model.DeterministicMachine.run, ih (by omega)]
    change machineStep q α τ L ε N (k * phaseLength N + r)
      (((start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f r), best),
        Model.oracle f (machineQuery q α τ L ε N (k * phaseLength N + r)
          ((start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f r), best))) = _
    simp only [machineStep, if_neg hne, machineQuery, hmod, rawOrderedPhaseQuery,
      if_pos hrbody, machinePush, Prod.fst, Prod.snd]
    rfl

def computedPhase {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ) (N : ℕ)
    (start : Model.Space d) : Model.Space d :=
  rawOrderedCandidate q α τ L ε N
    (start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f (9 * N + 2))

theorem upperMachine_finish {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N k : ℕ) (start : Model.Space d) (best : Model.Space d × ℝ)
    (hbase : (upperMachine q α τ L ε N).run f (k * phaseLength N) = ((start, fun _ => 0), best)) :
    let x := computedPhase f q α τ L ε N start
    (upperMachine q α τ L ε N).run f ((k + 1) * phaseLength N) =
      ((x, fun _ => 0), if k = 0 then (x, ‖gradient f x‖) else chooseLowerReply (x, ‖gradient f x‖) best) := by
  have hlen : 0 < phaseLength N := by unfold phaseLength; omega
  have hb : 9 * N + 2 < phaseLength N := by unfold phaseLength; omega
  have he : (k + 1) * phaseLength N = (k * phaseLength N + (9 * N + 2)) + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    unfold phaseLength
    omega
  have hmod : (k * phaseLength N + (9 * N + 2)) % phaseLength N = 9 * N + 2 := by
    simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt hb]
  have hend : (k * phaseLength N + (9 * N + 2) + 1) % phaseLength N = 0 := by
    rw [← he]
    exact Nat.mul_mod_left _ _
  have hfirst : k * phaseLength N + (9 * N + 2) + 1 = phaseLength N ↔ k = 0 := by
    constructor
    · intro hh
      by_contra hk
      have hkm : 0 < k * phaseLength N := Nat.mul_pos (by omega) hlen
      unfold phaseLength at hh hkm
      omega
    · intro hk; subst k; simp [phaseLength]
  rw [he, RandomizedFO2003.Model.DeterministicMachine.run,
    upperMachine_prefix f q α τ L ε N k start best hbase (9 * N + 2) le_rfl]
  change machineStep q α τ L ε N (k * phaseLength N + (9 * N + 2))
    (((start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f (9 * N + 2)), best),
      Model.oracle f (machineQuery q α τ L ε N (k * phaseLength N + (9 * N + 2))
        ((start, arrayRun (fun t a => rawBodyQuery q α τ L ε N t (start, a)) f (9 * N + 2)), best))) = _
  simp only [machineStep, if_pos hend, machineQuery, hmod, rawOrderedPhaseQuery,
    lt_self_iff_false, ↓reduceIte, machineFinish, hfirst, Prod.fst, Prod.snd]
  rfl

def computedEpoch {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ) (N : ℕ) : ℕ → Model.Space d
  | 0 => 0
  | k + 1 => computedPhase f q α τ L ε N (computedEpoch f q α τ L ε N k)

def computedBest {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ) (N : ℕ) : ℕ → Model.Space d × ℝ
  | 0 => (0, 0)
  | k + 1 =>
    let x := computedEpoch f q α τ L ε N (k + 1)
    if k = 0 then (x, ‖gradient f x‖) else
      chooseLowerReply (x, ‖gradient f x‖) (computedBest f q α τ L ε N k)

theorem upperMachine_epochs {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ) (N k : ℕ) :
    (upperMachine q α τ L ε N).run f (k * phaseLength N) =
      ((computedEpoch f q α τ L ε N k, fun _ => 0), computedBest f q α τ L ε N k) := by
  induction k with
  | zero => simp only [Nat.zero_mul, RandomizedFO2003.Model.DeterministicMachine.run,
      upperMachine, computedEpoch, computedBest]
  | succ k ih => exact upperMachine_finish f q α τ L ε N k _ _ ih

theorem chooseLowerReply_snd {E : Type*} (a b : E × ℝ) :
    (chooseLowerReply a b).2 = min a.2 b.2 := by
  unfold chooseLowerReply
  split_ifs with h
  · exact (min_eq_left h).symm
  · exact (min_eq_right (le_of_not_ge h)).symm

theorem computedBest_valid {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N k : ℕ) (hk : 0 < k) :
    (computedBest f q α τ L ε N k).2 = ‖gradient f (computedBest f q α τ L ε N k).1‖ := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [computedBest]
    split_ifs with hzero
    · rfl
    · unfold chooseLowerReply
      split_ifs
      · rfl
      · exact ih (by omega)

theorem computedBest_le_epoch {d : ℕ} (f : Model.Space d → ℝ) (q α τ L ε : ℝ)
    (N k : ℕ) : ∀ j < k,
    (computedBest f q α τ L ε N k).2 ≤ ‖gradient f (computedEpoch f q α τ L ε N (j + 1))‖ := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    by_cases hk : k = 0
    · subst k
      have hj0 : j = 0 := by omega
      subst j
      simp only [computedBest, ↓reduceIte, le_refl]
    · simp only [computedBest, if_neg hk, chooseLowerReply_snd]
      by_cases hjk : j = k
      · subst j; exact min_le_left _ _
      · exact (min_le_right _ _).trans (ih j (by omega))

end MatchingBounds1005.CUPG
