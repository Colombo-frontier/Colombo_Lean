import NCConcave16991.MixedHaarProgramSampler
import NCConcave16991.MixedHaarTapeMarginal
import NCConcave16991.OracleProgramState

/-! # The stateful stream interpreter is the literal Gaussian tape evaluator -/

noncomputable section

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

variable {A R X Ω S W Z O : Type} [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] {T : ℕ}

def tapeFreshList : (N : ℕ) → RevealTape W Z N → List W
  | 0,_ => []
  | N + 1,p => p.1 :: tapeFreshList N p.2

def tapeFinalNoise : (N : ℕ) → RevealTape W Z N → Z
  | 0,p => p
  | N + 1,p => tapeFinalNoise N p.2

def streamOracle (reveal : S → A → W → S × R) (default : W) :
    S × List W → A → (S × List W) × R
  | (s,[]),q => let sr := reveal s q default; ((sr.1,[]),sr.2)
  | (s,w :: ws),q => let sr := reveal s q w; ((sr.1,ws),sr.2)

theorem gaussianEvalFrom_eq_evalStateFrom (P : OracleProgram.Fixed A R X Ω T)
    (reveal : S → A → W → S × R) (complete : S → Z → O) (default : W) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (s : S) (replies : Fin t → R) (p : RevealTape W Z k) :
    programGaussianEvalFrom P reveal complete seed k t ht s replies p =
      let r := OracleProgram.evalStateFrom P (streamOracle reveal default) seed k t ht replies (s,tapeFreshList k p)
      (r.1,complete r.2.1 (tapeFinalNoise k p)) := by
  induction k generalizing t s with
  | zero => rfl
  | succ k ih =>
      exact ih (t + 1) (by omega)
        (reveal s (P.ask ⟨t,by omega⟩ seed replies) p.1).1
        (Fin.snoc replies (reveal s (P.ask ⟨t,by omega⟩ seed replies) p.1).2) p.2

theorem gaussianEval_eq_evalState (P : OracleProgram.Fixed A R X Ω T)
    (reveal : S → A → W → S × R) (complete : S → Z → O) (default : W) (seed : Ω)
    (s : S) (p : RevealTape W Z T) :
    programGaussianEval P reveal complete seed s p =
      let r := OracleProgram.evalState P (streamOracle reveal default) seed (s,tapeFreshList T p)
      (r.1,complete r.2.1 (tapeFinalNoise T p)) :=
  gaussianEvalFrom_eq_evalStateFrom P reveal complete default seed T 0 (by omega) s Fin.elim0 p

theorem mem_tapeFreshList_iff (N : ℕ) (p : RevealTape W Z N) (w : W) :
    w ∈ tapeFreshList N p ↔ ∃ i : Fin N, tapeFresh N p i = w := by
  induction N with
  | zero => simp [tapeFreshList]
  | succ N ih =>
      simp only [tapeFreshList,List.mem_cons]
      constructor
      · rintro (hw | hw)
        · exact ⟨0,by simpa only [tapeFresh,Fin.cons_zero] using hw.symm⟩
        · obtain ⟨i,hi⟩ := (ih p.2).mp hw
          exact ⟨i.succ,by simpa only [tapeFresh,Fin.cons_succ] using hi⟩
      · rintro ⟨i,hi⟩
        cases i using Fin.cases with
        | zero => exact Or.inl (by simpa only [tapeFresh,Fin.cons_zero] using hi.symm)
        | succ i => exact Or.inr ((ih p.2).mpr ⟨i,by simpa only [tapeFresh,Fin.cons_succ] using hi⟩)

end NCConcave16991.MixedHaar
