import Geode.PartialOracle
import Mathlib.Logic.Equiv.List

/-! Exact transport of the complete oracle model across point and reply
equivalences, preserving query order, stopping, exhaustion, and internal stalls. -/
namespace Geode.OracleReplay

variable {P Q R S : Type*} (eP : P ≃ Q) (eR : R ≃ S)

def historyEquiv : History P R ≃ History Q S := Equiv.listEquivOfEquiv (eP.prodCongr eR)

@[simp] theorem historyEquiv_symm : historyEquiv eP.symm eR.symm = (historyEquiv eP eR).symm := rfl

@[simp] theorem historyEquiv_nil : historyEquiv eP eR [] = [] := rfl

@[simp] theorem historyEquiv_append_entry (h : History P R) (p : P) (r : R) :
    historyEquiv eP eR (h ++ [(p, r)]) = historyEquiv eP eR h ++ [(eP p, eR r)] := by
  simp [historyEquiv, Equiv.listEquivOfEquiv]

def decisionMap : Decision P → Decision Q
  | .stop x => .stop (eP x)
  | .query x => .query (eP x)

@[simp] theorem decisionMap_symm (d : Decision P) :
    decisionMap eP.symm (decisionMap eP d) = d := by cases d <;> simp [decisionMap]

def resultEquiv : RunResult P R ≃ RunResult Q S where
  toFun
    | .finished h x => .finished (historyEquiv eP eR h) (eP x)
    | .exhausted h x => .exhausted (historyEquiv eP eR h) (eP x)
  invFun
    | .finished h x => .finished ((historyEquiv eP eR).symm h) (eP.symm x)
    | .exhausted h x => .exhausted ((historyEquiv eP eR).symm h) (eP.symm x)
  left_inv r := by cases r <;> simp
  right_inv r := by cases r <;> simp

def conjugateAlgorithm (A : StoppingAlgorithm P R) : StoppingAlgorithm Q S where
  decide h := decisionMap eP (A.decide ((historyEquiv eP eR).symm h))

@[simp] theorem conjugateAlgorithm_symm (A : StoppingAlgorithm P R) :
    conjugateAlgorithm eP.symm eR.symm (conjugateAlgorithm eP eR A) = A := by
  cases A with
  | mk d =>
    dsimp only [conjugateAlgorithm]
    congr 1
    funext h
    simp [conjugateAlgorithm]

def conjugateOracle (O : P → R) : Q → S := fun q => eR (O (eP.symm q))

@[simp] theorem conjugateOracle_symm (O : P → R) :
    conjugateOracle eP.symm eR.symm (conjugateOracle eP eR O) = O := by
  funext x
  simp [conjugateOracle]

theorem run_conjugate (A : StoppingAlgorithm P R) (O : P → R) (N : ℕ) (h : History P R) :
    run (conjugateAlgorithm eP eR A) (fixedResponder (conjugateOracle eP eR O)) N
      (historyEquiv eP eR h) = resultEquiv eP eR (run A (fixedResponder O) N h) := by
  induction N generalizing h with
  | zero =>
    cases hd : A.decide h <;>
      simp [run, conjugateAlgorithm, hd, decisionMap, resultEquiv]
  | succ n ih =>
    cases hd : A.decide h with
    | stop x => simp [run, conjugateAlgorithm, hd, decisionMap, resultEquiv]
    | query x =>
      simp only [run, conjugateAlgorithm, Equiv.symm_apply_apply, hd, decisionMap,
        fixedResponder, conjugateOracle, Equiv.symm_apply_apply]
      rw [← historyEquiv_append_entry]
      exact ih _

theorem conjugate_finished (A : StoppingAlgorithm P R) (O : P → R) (N : ℕ)
    (h h' : History P R) (x : P) (hf : run A (fixedResponder O) N h = .finished h' x) :
    run (conjugateAlgorithm eP eR A) (fixedResponder (conjugateOracle eP eR O)) N
      (historyEquiv eP eR h) = .finished (historyEquiv eP eR h') (eP x) := by
  rw [run_conjugate, hf]
  rfl

def partialResultEquiv : PartialRunResult P R ≃ PartialRunResult Q S where
  toFun
    | .finished h x => .finished (historyEquiv eP eR h) (eP x)
    | .exhausted h x => .exhausted (historyEquiv eP eR h) (eP x)
    | .stalled h => .stalled (historyEquiv eP eR h)
  invFun
    | .finished h x => .finished ((historyEquiv eP eR).symm h) (eP.symm x)
    | .exhausted h x => .exhausted ((historyEquiv eP eR).symm h) (eP.symm x)
    | .stalled h => .stalled ((historyEquiv eP eR).symm h)
  left_inv r := by cases r <;> simp
  right_inv r := by cases r <;> simp

def conjugatePartialAlgorithm (A : PartialStoppingAlgorithm P R) : PartialStoppingAlgorithm Q S where
  decide h := (A.decide ((historyEquiv eP eR).symm h)).map (decisionMap eP)

@[simp] theorem conjugatePartialAlgorithm_symm (A : PartialStoppingAlgorithm P R) :
    conjugatePartialAlgorithm eP.symm eR.symm (conjugatePartialAlgorithm eP eR A) = A := by
  cases A with
  | mk d =>
    dsimp only [conjugatePartialAlgorithm]
    congr 1
    funext h
    simp only [conjugatePartialAlgorithm, historyEquiv_symm, Equiv.symm_symm,
      Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    cases hd : d h with
    | none => simp [hd]
    | some x => simp [hd, decisionMap_symm]

theorem partialRun_conjugate (A : PartialStoppingAlgorithm P R) (O : P → R)
    (N : ℕ) (h : History P R) :
    partialRun (conjugatePartialAlgorithm eP eR A)
      (fixedResponder (conjugateOracle eP eR O)) N (historyEquiv eP eR h) =
        partialResultEquiv eP eR (partialRun A (fixedResponder O) N h) := by
  induction N generalizing h with
  | zero =>
    cases hd : A.decide h with
    | none => simp [partialRun, conjugatePartialAlgorithm, hd, partialResultEquiv]
    | some d => cases d <;>
        simp [partialRun, conjugatePartialAlgorithm, hd, decisionMap, partialResultEquiv]
  | succ n ih =>
    cases hd : A.decide h with
    | none => simp [partialRun, conjugatePartialAlgorithm, hd, partialResultEquiv]
    | some d =>
      cases d with
      | stop x => simp [partialRun, conjugatePartialAlgorithm, hd, decisionMap, partialResultEquiv]
      | query x =>
        simp only [partialRun, conjugatePartialAlgorithm, Equiv.symm_apply_apply, hd,
          Option.map, decisionMap, fixedResponder, conjugateOracle, Equiv.symm_apply_apply]
        rw [← historyEquiv_append_entry]
        exact ih _

theorem conjugate_partial_finished (A : PartialStoppingAlgorithm P R) (O : P → R) (N : ℕ)
    (h h' : History P R) (x : P) (hf : partialRun A (fixedResponder O) N h = .finished h' x) :
    partialRun (conjugatePartialAlgorithm eP eR A) (fixedResponder (conjugateOracle eP eR O)) N
      (historyEquiv eP eR h) = .finished (historyEquiv eP eR h') (eP x) := by
  rw [partialRun_conjugate, hf]
  rfl

end Geode.OracleReplay
