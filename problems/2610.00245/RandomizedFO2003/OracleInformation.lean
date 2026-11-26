import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A concrete information audit of the oracle-domination paragraph.
This refutes universal reconstruction of the hidden readout from the listed data at
one query. It does NOT refute the paper's minimax theorem or an almost-sure claim. -/

namespace RandomizedFO2003.OracleInformation

abbrev V := Fin 3 → ℝ

def dot (x y : V) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2
def swap (x : V) : V := ![x 0, x 2, x 1]
def diagonal (x : V) : V := ![x 0, 2 * x 1, 3 * x 2]
noncomputable def u : V := fun _ => (Real.sqrt 3)⁻¹
def query (t : ℝ) : V := ![t, 0, 0]

/-- 18 times the degree-zero least-squares residual for spectrum (1,2,3),
with equal weights: 18*(1/lambda - 11/18) = (7,-2,-5). -/
def residual (x : V) : V := ![7 * x 0, -2 * x 1, -5 * x 2]

noncomputable def readout (U : V → V) : V :=
  fun i => U (residual u) i / Real.sqrt 26

/-- U is either identity or swap, so U-transpose = U.
The spectrum and marked latent unit vector are identical in the two instances.
The remaining observations are b=Uu, U-transpose*x, and Ax=U*Lambda*U-transpose*x. -/
noncomputable def observations (U : V → V) (x : V) : V × V × V :=
  (U u, U x, U (diagonal (U x)))

theorem swap_involution (x : V) : swap (swap x) = x := by
  ext i
  fin_cases i <;> simp [swap]

theorem swap_orthogonal (x y : V) : dot (swap x) (swap y) = dot x y := by
  simp [dot, swap]
  ring

theorem u_unit : dot u u = 1 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  dsimp [dot, u]
  field_simp
  nlinarith

theorem swap_u : swap u = u := by
  ext i
  fin_cases i <;> simp [swap, u]

theorem observations_equal (t : ℝ) :
    observations id (query t) = observations swap (query t) := by
  simp [observations, swap_u, query, swap, diagonal]
  exact swap_u.symm

theorem readouts_distinct : readout id ≠ readout swap := by
  intro h
  have hi := congrFun h (1 : Fin 3)
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h26 : Real.sqrt 26 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  simp [readout, residual, swap, u] at hi
  field_simp at hi
  norm_num at hi

theorem readout_dot_query_equal (t : ℝ) :
    dot (readout id) (query t) = dot (readout swap) (query t) := by
  simp [dot, readout, residual, swap, query]

theorem no_readout_reconstructor :
    ¬ ∃ reconstruct : (V × V × V) → V,
      ∀ U ∈ ({id, swap} : Set (V → V)),
        reconstruct (observations U (query 1)) = readout U := by
  rintro ⟨reconstruct, h⟩
  have hi := h id (by simp)
  have hs := h swap (by simp)
  apply readouts_distinct
  rw [← hi, ← hs, observations_equal]

theorem swap_linear (c : ℝ) (x y : V) :
    swap (c • x + y) = c • swap x + swap y := by
  ext i
  fin_cases i <;> simp [swap]

theorem residual_orthogonal_to_constant : dot u (residual u) = 0 := by
  simp [dot, residual, u]
  ring

theorem readout_id_unit : dot (readout id) (readout id) = 1 := by
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h26 : Real.sqrt 26 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs26 : Real.sqrt 26 ^ 2 = 26 := Real.sq_sqrt (by norm_num)
  simp [dot, readout, residual, u]
  field_simp
  nlinarith [sq_nonneg (Real.sqrt 3 * Real.sqrt 26)]

theorem readout_swap : readout swap = swap (readout id) := by
  ext i
  fin_cases i <;> simp [readout, swap]

theorem readout_swap_unit : dot (readout swap) (readout swap) = 1 := by
  rw [readout_swap, swap_orthogonal, readout_id_unit]

/-- The block gradient on the identity region of the radial squash.
c is the incoming coefficient; w is the nonzero outgoing coefficient. -/
noncomputable def blockGradient (U : V → V) (x : V) (c w : ℝ) : V :=
  fun i => U (diagonal (U x)) i - c * U u i - w * readout U i

theorem block_gradients_distinct (t c w : ℝ) (hw : w ≠ 0) :
    blockGradient id (query t) c w ≠ blockGradient swap (query t) c w := by
  intro heq
  apply readouts_distinct
  have hbase : diagonal (query t) = swap (diagonal (swap (query t))) := by
    simp [query, diagonal, swap]
  ext i
  have hi := congrFun heq i
  dsimp [blockGradient] at hi
  rw [← hbase, swap_u] at hi
  exact mul_left_cancel₀ hw (by linarith)

theorem no_gradient_reconstructor (c w : ℝ) (hw : w ≠ 0) :
    ¬ ∃ reconstruct : (V × V × V) → V,
      ∀ U ∈ ({id, swap} : Set (V → V)),
        reconstruct (observations U (query 1)) = blockGradient U (query 1) c w := by
  rintro ⟨reconstruct, h⟩
  have hi := h id (by simp)
  have hs := h swap (by simp)
  apply block_gradients_distinct 1 c w hw
  rw [← hi, ← hs, observations_equal]

end RandomizedFO2003.OracleInformation
