import NCConcave16991.OracleProgramLibrary
import NCConcave16991.OracleProgramTransform
import NCConcave16991.InnerExecutable

/-!
# Actual component-query primitives for the persistent estimator

The constructors depend on known feasible points and private seeds, and receive
value/full-gradient answers through the oracle interface. No unknown Problem
occurs in the constructors; it appears only in their execution-correctness lemmas.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.PersistentProgram

variable {n dx dy : ℕ} {D : ℝ} (K : KnownDualDomain dy D)

abbrev Feasible := productDomain dx K

def jointQuery (a : Fin n × (productDomain dx K)) : OracleQuery n dx K :=
  (a.1, (a.2 : JointSpace dx dy).fst, ⟨(a.2 : JointSpace dx dy).snd, a.2.property⟩)

theorem jointQuery_measurable [MeasurableSpace (Fin n)] : Measurable (jointQuery K (n := n) (dx := dx)) := by
  have hz : Measurable (fun a : Fin n × (productDomain dx K) => (a.2 : JointSpace dx dy)) :=
    measurable_subtype_coe.comp measurable_snd
  have hx := (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.measurable.comp hz
  have hy := (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.measurable.comp hz
  exact measurable_fst.prodMk (hx.prodMk hy.subtype_mk)

def signedAnswer (r : OracleAnswer dx dy) : JointSpace dx dy :=
  jointPoint r.2.1 (-r.2.2)

theorem signedAnswer_measurable : Measurable (signedAnswer (dx := dx) (dy := dy)) :=
  (WithLp.prod_continuous_toLp 2 (PrimalSpace dx) (DualSpace dy)).measurable.comp
    ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd).neg)

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace (Fin n)]

/-- Two actual component queries, returning the signed gradients at both points. -/
def signedPair (index : Ω → Fin n) (hi : Measurable index)
    (current anchor : Ω → (productDomain dx K)) (hc : Measurable current) (ha : Measurable anchor) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy)
      (JointSpace dx dy × JointSpace dx dy) Ω 2 :=
  OracleProgram.map
    (OracleProgram.twoQueries
      (fun seed => jointQuery K (index seed, current seed))
      ((jointQuery_measurable K).comp (hi.prodMk hc))
      (fun seed _ => jointQuery K (index seed, anchor seed))
      (((jointQuery_measurable K).comp (hi.prodMk ha)).comp measurable_fst))
    (fun r => (signedAnswer r.1, signedAnswer r.2))
    ((signedAnswer_measurable.comp measurable_fst).prodMk
      (signedAnswer_measurable.comp measurable_snd))

/-- One actual full pass computes the exact signed anchor-gradient average. -/
def fullSignedPass (point : Ω → (productDomain dx K)) (hp : Measurable point) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (JointSpace dx dy) Ω n :=
  OracleProgram.map
    (OracleProgram.fullPass (fun seed i => jointQuery K (i, point seed))
      (fun _ => (jointQuery_measurable K).comp (measurable_const.prodMk hp)))
    (fun replies => (n : ℝ)⁻¹ • ∑ i, signedAnswer (replies i))
    ((measurable_const : Measurable (fun _ : Fin n → OracleAnswer dx dy => (n : ℝ)⁻¹)).smul
      (Finset.measurable_sum _ (fun i _ => signedAnswer_measurable.comp (measurable_pi_apply i))))

variable {b : ℕ}

def batchQuery (index : Ω → Fin b → Fin n) (current anchor : Ω → (productDomain dx K))
    (seed : Ω) (j : Fin (2 * b)) : OracleQuery n dx K :=
  if hj : j.val < b then jointQuery K (index seed ⟨j.val, hj⟩, current seed)
  else jointQuery K (index seed ⟨j.val - b, by omega⟩, anchor seed)

theorem batchQuery_measurable (index : Ω → Fin b → Fin n)
    (hi : ∀ j, Measurable (fun seed => index seed j))
    (current anchor : Ω → (productDomain dx K)) (hc : Measurable current) (ha : Measurable anchor)
    (j : Fin (2 * b)) : Measurable (fun seed => batchQuery K index current anchor seed j) := by
  by_cases hj : j.val < b
  · simpa only [batchQuery, hj, dite_true, Function.comp_def] using
      (jointQuery_measurable K).comp ((hi ⟨j.val, hj⟩).prodMk hc)
  · simpa only [batchQuery, hj, dite_false, Function.comp_def] using
      (jointQuery_measurable K).comp ((hi ⟨j.val - b, by omega⟩).prodMk ha)

def signedDifferenceBatch (index : Ω → Fin b → Fin n)
    (hi : ∀ j, Measurable (fun seed => index seed j))
    (current anchor : Ω → (productDomain dx K)) (hc : Measurable current) (ha : Measurable anchor) :
    OracleProgram.Fixed (OracleQuery n dx K) (OracleAnswer dx dy) (JointSpace dx dy) Ω (2 * b) :=
  OracleProgram.map
    (OracleProgram.fullPass (batchQuery K index current anchor)
      (batchQuery_measurable K index hi current anchor hc ha))
    (fun replies => (b : ℝ)⁻¹ • ∑ j : Fin b,
      (signedAnswer (replies ⟨j.val, by omega⟩) - signedAnswer (replies ⟨b + j.val, by omega⟩)))
    ((measurable_const : Measurable (fun _ : Fin (2 * b) → OracleAnswer dx dy => (b : ℝ)⁻¹)).smul
      (Finset.measurable_sum Finset.univ (fun (j : Fin b) _ => by
        change Measurable
          ((fun replies : Fin (2 * b) → OracleAnswer dx dy => signedAnswer (replies ⟨j.val, by omega⟩)) -
            (fun replies : Fin (2 * b) → OracleAnswer dx dy => signedAnswer (replies ⟨b + j.val, by omega⟩)))
        exact
          ((signedAnswer_measurable (dx := dx) (dy := dy)).comp
            (measurable_pi_apply (⟨j.val, by omega⟩ : Fin (2 * b)))).sub
          ((signedAnswer_measurable (dx := dx) (dy := dy)).comp
            (measurable_pi_apply (⟨b + j.val, by omega⟩ : Fin (2 * b)))))))

theorem batchQuery_first (index : Ω → Fin b → Fin n) (current anchor : Ω → (productDomain dx K))
    (seed : Ω) (j : Fin b) :
    batchQuery K index current anchor seed ⟨j.val, by omega⟩ = jointQuery K (index seed j, current seed) := by
  simp only [batchQuery, j.isLt, dite_true]

theorem batchQuery_second (index : Ω → Fin b → Fin n) (current anchor : Ω → (productDomain dx K))
    (seed : Ω) (j : Fin b) :
    batchQuery K index current anchor seed ⟨b + j.val, by omega⟩ = jointQuery K (index seed j, anchor seed) := by
  have hn : ¬b + j.val < b := by omega
  simp only [batchQuery, hn, dite_false]
  apply congrArg (fun i : Fin b => jointQuery K (index seed i, anchor seed))
  apply Fin.ext
  change b + j.val - b = j.val
  omega

variable {p : ProblemParameters} {K' : KnownDualDomain dy p.diameter} [MeasurableSpace (Fin p.n)]

theorem signedAnswer_oracleResponse (P : Problem p dx dy K') (i : Fin p.n)
    (z : productDomain dx K') :
    signedAnswer (oracleResponse P (jointQuery K' (i, z))) = signedComponentGradient P i z := rfl

theorem eval_signedPair (P : Problem p dx dy K')
    (index : Ω → Fin p.n) (hi : Measurable index)
    (current anchor : Ω → (productDomain dx K')) (hc : Measurable current) (ha : Measurable anchor)
    (seed : Ω) :
    OracleProgram.eval (signedPair K' index hi current anchor hc ha) (oracleResponse P) seed =
      (signedComponentGradient P (index seed) (current seed),
        signedComponentGradient P (index seed) (anchor seed)) := by
  simp only [signedPair, OracleProgram.eval_map]
  have ht := OracleProgram.eval_twoQueries
    (fun seed => jointQuery K' (index seed, current seed))
    ((jointQuery_measurable K').comp (hi.prodMk hc))
    (fun seed _ => jointQuery K' (index seed, anchor seed))
    (((jointQuery_measurable K').comp (hi.prodMk ha)).comp measurable_fst) (oracleResponse P) seed
  exact congrArg (fun r : OracleAnswer dx dy × OracleAnswer dx dy =>
    (signedAnswer r.1, signedAnswer r.2)) ht

theorem eval_fullSignedPass (P : Problem p dx dy K')
    (point : Ω → (productDomain dx K')) (hp : Measurable point) (seed : Ω) :
    OracleProgram.eval (fullSignedPass K' point hp) (oracleResponse P) seed =
      averageMap (signedComponentGradient P) (point seed) := by
  simp only [fullSignedPass, OracleProgram.eval_map, OracleProgram.eval_fullPass,
    signedAnswer_oracleResponse, averageMap]

theorem eval_signedDifferenceBatch (P : Problem p dx dy K')
    (index : Ω → Fin b → Fin p.n) (hi : ∀ j, Measurable (fun seed => index seed j))
    (current anchor : Ω → (productDomain dx K')) (hc : Measurable current) (ha : Measurable anchor)
    (seed : Ω) :
    OracleProgram.eval (signedDifferenceBatch K' index hi current anchor hc ha) (oracleResponse P) seed =
      minibatchMean (fun i => signedComponentGradient P i (current seed) -
        signedComponentGradient P i (anchor seed)) (index seed) := by
  simp only [signedDifferenceBatch, OracleProgram.eval_map, OracleProgram.eval_fullPass,
    batchQuery_first, batchQuery_second, signedAnswer_oracleResponse, minibatchMean]

end NCConcave16991.PersistentProgram
