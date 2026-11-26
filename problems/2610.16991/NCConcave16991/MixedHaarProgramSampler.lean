import NCConcave16991.MixedHaarAdaptiveLaw
import NCConcave16991.OracleProgram

/-! # The literal Gaussian reply-driven evaluation of a fixed mixed program -/

noncomputable section

namespace NCConcave16991.MixedHaar

variable {A R X Ω S W Z O : Type} [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] {T : ℕ}

def programGaussianEvalFrom (P : OracleProgram.Fixed A R X Ω T)
    (reveal : S → A → W → S × R) (complete : S → Z → O) (seed : Ω) :
    (k t : ℕ) → (ht : t + k = T) → S → (Fin t → R) → RevealTape W Z k → X × O
  | 0,t,ht,s,replies,z =>
      (P.finish seed (fun i ↦ replies (Fin.cast ht.symm i)),complete s z)
  | k + 1,t,ht,s,replies,p =>
      let sr := reveal s (P.ask ⟨t,by omega⟩ seed replies) p.1
      programGaussianEvalFrom P reveal complete seed k (t + 1) (by omega) sr.1 (Fin.snoc replies sr.2) p.2

def programGaussianEval (P : OracleProgram.Fixed A R X Ω T)
    (reveal : S → A → W → S × R) (complete : S → Z → O)
    (seed : Ω) (s : S) (p : RevealTape W Z T) : X × O :=
  programGaussianEvalFrom P reveal complete seed T 0 (by omega) s Fin.elim0 p

abbrev ProgramSampleInput (Ω S R W Z : Type) (k t : ℕ) :=
  Ω × (S × ((Fin t → R) × RevealTape W Z k))

def programNextInput (P : OracleProgram.Fixed A R X Ω T)
    (reveal : S → A → W → S × R) (k t : ℕ) (ht : t + (k + 1) = T) :
    ProgramSampleInput Ω S R W Z (k + 1) t → ProgramSampleInput Ω S R W Z k (t + 1) :=
  fun p ↦
    let q := P.ask ⟨t,by omega⟩ p.1 p.2.2.1
    let sr := reveal p.2.1 q p.2.2.2.1
    (p.1,(sr.1,(Fin.snoc p.2.2.1 sr.2,p.2.2.2.2)))

def programGaussianGoodFrom (P : OracleProgram.Fixed A R X Ω T)
    (reveal : S → A → W → S × R) (G : S → A → W → Prop) (seed : Ω) :
    (k t : ℕ) → (ht : t + k = T) → S → (Fin t → R) → RevealTape W Z k → Prop
  | 0,_,_,_,_,_ => True
  | k + 1,t,ht,s,replies,p =>
      let q := P.ask ⟨t,by omega⟩ seed replies
      let sr := reveal s q p.1
      G s q p.1 ∧ programGaussianGoodFrom P reveal G seed k (t + 1) (by omega) sr.1 (Fin.snoc replies sr.2) p.2

end NCConcave16991.MixedHaar
