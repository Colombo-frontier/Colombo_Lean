import SampleReuse.CurvatureFirstProgram

/-! Actual pre-sign inspection of the persistent scalar-loss tape.  Decisions
use the gradient/Hessian packets, and the current private sign is supplied
only after the direction has been selected. -/

open MeasureTheory SecondOrder
open scoped Classical

namespace SampleReuse
noncomputable section

def checkpointPacket {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H d B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (sample : Ω → Point d → E)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d)
    (tape : SampleTape H Ω) : E :=
  if k = 0 then batchMeanTape (fun z => sample z x) (reserve k) tape else
    batchMeanTape (fun z => sample z x - sample z (cache (ancestorParent k)).1)
      (fun i : Fin (checkpointBatchSize (B := B) scale σ L k cache x) => reserve k (prefixHandles hB _ i)) tape

theorem checkpointProgram_run {Ω E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H d B : ℕ} (hB : 0 < B) (scale σ L : ℝ) (q₀ : PersistentQuery H d)
    (F : Ω → Point d → ℝ) (sample : Ω → Point d → E) (flag : Bool) (project : PersistentReply d → E)
    (hfield : ∀ (tape : SampleTape H Ω) (r : Fin H) (x : Point d),
      project (persistentReply F tape (flag, r, x)) = sample (tape r) x)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d)
    (tape : SampleTape H Ω) :
    OracleProgram.run q₀ (fun q tape => persistentReply F tape q) (fun _ => tape)
      (checkpointProgram hB scale σ L flag project reserve k cache x)
      (checkpointCalls (B := B) scale σ L k cache x) =
      .done (checkpointPacket hB scale σ L sample reserve k cache x tape) := by
  unfold checkpointProgram checkpointCalls checkpointPacket
  split_ifs
  · exact fieldRootProgram_run q₀ F sample flag project hfield _ _ tape
  · exact fieldChordProgram_run q₀ F sample flag project hfield _ _ _ tape

inductive CurvatureFirstAction (d : ℕ)
  | success
  | gradient (g : Point d)
  | curvature (v : Point d)

structure CurvatureFirstInspection (d : ℕ) where
  cache : OptimizerCache d
  action : CurvatureFirstAction d
  gradientCalls : ℕ
  hessianCalls : ℕ

def curvatureFirstInspect {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d) :
    CurvatureFirstInspection d :=
  let packetH := checkpointPacket hBH scaleH P.hessianNoise P.hessianLip (fun z => hessian (F z))
    (hessianReserve T Bg BH) t s.2.2.2 s.1 tape
  let H := checkpointValue t s.2.2.2 packetH
  let cacheH := installCheckpoint t s.2.2.2 s.1 packetH
  let replyH := sourceCurvatureSelector (3*γ/4) H
  let cH := checkpointCalls (B := BH) scaleH P.hessianNoise P.hessianLip t s.2.2.2 s.1
  if curvatureTag replyH then
    ⟨(s.1, s.2.1, s.2.2.1, cacheH), .curvature (curvatureVector replyH), 0, cH⟩
  else
    let packetG := checkpointPacket hBg scaleG P.gradientNoise P.gradientLip (fun z => gradient (F z))
      (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1 tape
    let g := checkpointValue s.2.1 s.2.2.1 packetG
    let cacheG := installCheckpoint s.2.1 s.2.2.1 s.1 packetG
    ⟨(s.1, s.2.1 + 1, cacheG, cacheH),
      if ‖g‖ ≤ 3*ε/4 then .success else .gradient g,
      checkpointCalls (B := Bg) scaleG P.gradientNoise P.gradientLip s.2.1 s.2.2.1 s.1, cH⟩

def curvatureFirstAdvance {d : ℕ} (P : Parameters) (ε γ : ℝ) (b : Bool)
    (r : CurvatureFirstInspection d) : Option (OptimizerCache d) :=
  match r.action with
  | .success => none
  | .gradient g => some (gradientMove P ε r.cache.1 g, r.cache.2)
  | .curvature v => some (curvatureNext (γ/P.hessianLip) r.cache.1 v b, r.cache.2)

def curvatureFirstExecute {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) :
    ℕ → ℕ → OptimizerCache d → Option (Point d)
  | 0, _, _ => none
  | m+1, t, s =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    match curvatureFirstAdvance P ε γ (signs t) r with
    | none => some s.1
    | some s' => curvatureFirstExecute hBg hBH P ε γ scaleG scaleH F tape signs m (t+1) s'

def curvatureFirstCallTime {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (signs : ℕ → Bool) :
    ℕ → ℕ → OptimizerCache d → ℕ
  | 0, _, _ => 0
  | m+1, t, s =>
    let r := curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s
    r.hessianCalls+r.gradientCalls +
    match curvatureFirstAdvance P ε γ (signs t) r with
    | none => 0
    | some s' => curvatureFirstCallTime hBg hBH P ε γ scaleG scaleH F tape signs m (t+1) s'

theorem curvatureFirstInspect_point {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d) :
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.1 = s.1 := by
  dsimp only [curvatureFirstInspect]
  split_ifs <;> rfl

theorem curvatureFirstInspect_gradientIndex {Ω : Type*} {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (F : Ω → Point d → ℝ)
    (tape : SampleTape ((T+1)*Bg+(T+1)*BH) Ω) (t : ℕ) (s : OptimizerCache d) :
    s.2.1 ≤ (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.2.1 ∧
    (curvatureFirstInspect hBg hBH P ε γ scaleG scaleH F tape t s).cache.2.1 ≤ s.2.1+1 := by
  dsimp only [curvatureFirstInspect]
  split_ifs <;> simp

end
end SampleReuse
