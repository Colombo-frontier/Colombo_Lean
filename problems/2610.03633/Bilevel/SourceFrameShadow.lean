import Bilevel.SourceFrameShadowBase

noncomputable section
open MeasureTheory
universe u
namespace Bilevel.SourceFrameActions
open EuclideanGaussian ProjectionPosterior TransportControllerMachine
variable {H : Memory.{u}} {d T B : ℕ}

theorem observeRun_shadow_congr (L : Rules H d T) : ∀ n t (s z : State H d T)
    (U : Frame d T), shadow s=shadow z →
    shadow (observeRun L n t s U)=shadow (observeRun L n t z U) := by
  intro n
  induction n with
  | zero => intros; assumption
  | succ n ih =>
    intro t s z U hs
    exact ih (t+1) _ _ U (observeStep_shadow_congr L t s z U hs)



theorem batch_shadow_one (L : Rules H d T) (hB : 0<B)
    (queries : ℕ → H → Fin B → Space d) (hq : ∀ t k, Measurable (fun h => queries t h k))
    (t : ℕ) (s : State H d T) (U : Frame d T) :
    shadow (observeRun (batchRules L hB queries hq) B (t*B) s U)=shadow (observeStep L t s U) := by
  apply Prod.ext
  · change (observeRun _ _ _ _ _).1=(observeStep _ _ _ _).1
    rw [observeRun_memory,batch_run_one,observeStep_memory]
  · exact batch_known_one L hB queries hq t s U

theorem batch_shadow_blocks (L : Rules H d T) (hB : 0<B)
    (queries : ℕ → H → Fin B → Space d) (hq : ∀ t k, Measurable (fun h => queries t h k)) :
    ∀ n t (s : State H d T) (U : Frame d T),
    shadow (observeRun (batchRules L hB queries hq) (n*B) (t*B) s U)=
      shadow (observeRun L n t s U) := by
  intro n
  induction n with
  | zero => intros; simp only [Nat.zero_mul,observeRun]
  | succ n ih =>
    intro t s U
    rw [Nat.succ_mul,Nat.add_comm (n*B) B,observeRun_add]
    have ht : t*B+B=(t+1)*B := by ring
    rw [ht,ih,observeRun]
    exact observeRun_shadow_congr L n (t+1) _ _ U (batch_shadow_one L hB queries hq t s U)

end Bilevel.SourceFrameActions


