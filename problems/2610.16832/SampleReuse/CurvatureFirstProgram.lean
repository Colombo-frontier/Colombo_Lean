import SampleReuse.SourceRayleighSelection
import SampleReuse.TreeProgramMeasurable

/-! A concrete curvature-first reply-only controller with separate persistent
gradient/Hessian caches. This uses the documented equivalent Borel Rayleigh
witness selector; it does not claim to compute a minimum eigenvector. -/

open MeasureTheory SecondOrder
open scoped BigOperators Classical

namespace SampleReuse
noncomputable section

def gradientReserve (T Bg BH k : ℕ) (i : Fin Bg) : Fin ((T + 1) * Bg + (T + 1) * BH) :=
  Fin.castAdd ((T + 1) * BH) (treeBlockHandle T Bg k i)

def hessianReserve (T Bg BH k : ℕ) (i : Fin BH) : Fin ((T + 1) * Bg + (T + 1) * BH) :=
  Fin.natAdd ((T + 1) * Bg) (treeBlockHandle T BH k i)

theorem gradientReserve_injective (T Bg BH k : ℕ) : Function.Injective (gradientReserve T Bg BH k) := by
  intro i j hij
  apply treeBlockHandle_injective T Bg k
  apply Fin.ext
  have he := congrArg (fun r : Fin ((T + 1) * Bg + (T + 1) * BH) => r.val) hij
  exact he

theorem hessianReserve_injective (T Bg BH k : ℕ) : Function.Injective (hessianReserve T Bg BH k) := by
  intro i j hij
  apply treeBlockHandle_injective T BH k
  apply Fin.ext
  have he := congrArg (fun r : Fin ((T + 1) * Bg + (T + 1) * BH) => r.val) hij
  change (T + 1) * Bg + (treeBlockHandle T BH k i).val =
    (T + 1) * Bg + (treeBlockHandle T BH k j).val at he
  exact Nat.add_left_cancel he

theorem gradient_hessian_reserves_disjoint (T Bg BH kg kH : ℕ) (i : Fin Bg) (j : Fin BH) :
    gradientReserve T Bg BH kg i ≠ hessianReserve T Bg BH kH j := by
  intro he
  have hev := congrArg Fin.val he
  have hg := (treeBlockHandle T Bg kg i).isLt
  change (treeBlockHandle T Bg kg i).val = (T + 1) * Bg + (treeBlockHandle T BH kH j).val at hev
  omega

def checkpointBatchSize {E : Type*} {d B : ℕ} (scale σ L : ℝ)
    (k : ℕ) (cache : TreeCache d E) (x : Point d) : ℕ :=
  if k = 0 then B else chordBatchSize scale σ L x (cache (ancestorParent k)).1

def checkpointCalls {E : Type*} {d B : ℕ} (scale σ L : ℝ)
    (k : ℕ) (cache : TreeCache d E) (x : Point d) : ℕ :=
  if k = 0 then B else 2 * checkpointBatchSize (B := B) scale σ L k cache x

def checkpointProgram {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {H d B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d) :
    OracleProgram (PersistentQuery H d) (PersistentReply d) E :=
  if k = 0 then fieldRootProgram flag project (reserve k) x else
    fieldChordProgram flag project
      (fun i : Fin (checkpointBatchSize (B := B) scale σ L k cache x) => reserve k (prefixHandles hB _ i))
      x (cache (ancestorParent k)).1

def installCheckpoint {E : Type*} [Add E] {d : ℕ} (k : ℕ) (cache : TreeCache d E)
    (x : Point d) (packet : E) : TreeCache d E :=
  Function.update cache k (x, if k = 0 then packet else (cache (ancestorParent k)).2 + packet)

def checkpointValue {E : Type*} [Add E] {d : ℕ} (k : ℕ) (cache : TreeCache d E) (packet : E) : E :=
  if k = 0 then packet else (cache (ancestorParent k)).2 + packet

theorem checkpointProgram_exact {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {H d B : ℕ}
    (hB : 0 < B) (scale σ L : ℝ) (flag : Bool) (project : PersistentReply d → E)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d) :
    OracleProgram.UsesExactly (checkpointCalls (B := B) scale σ L k cache x)
      (checkpointProgram hB scale σ L flag project reserve k cache x) := by
  unfold checkpointCalls checkpointProgram
  split_ifs
  · exact fieldRootProgram_exact _ _ _ _
  · exact fieldChordProgram_exact _ _ _ _ _

theorem checkpointProgram_usesAtMost {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H d B : ℕ} (hB : 0 < B) {scale σ L : ℝ} (hs : 0 ≤ scale)
    (hcap : B = batchSize scale (σ^2)) (flag : Bool) (project : PersistentReply d → E)
    (reserve : ℕ → Fin B → Fin H) (k : ℕ) (cache : TreeCache d E) (x : Point d) :
    OracleProgram.UsesAtMost (2 * B) (checkpointProgram hB scale σ L flag project reserve k cache x) := by
  apply OracleProgram.usesAtMost_mono (checkpointProgram_exact hB scale σ L flag project reserve k cache x).usesAtMost
  unfold checkpointCalls checkpointBatchSize
  split_ifs
  · omega
  · apply Nat.mul_le_mul_left
    rw [hcap]
    exact chordBatchSize_le_capacity hs _ _ _ _

/-- Current point, gradient checkpoint index, gradient cache, Hessian cache.
The Hessian checkpoint index is the current outer iteration. -/
abbrev OptimizerCache (d : ℕ) :=
  Point d × (ℕ × (TreeCache d (Point d) × TreeCache d (Point d →L[ℝ] Point d)))

def optimizerInitial {d : ℕ} (x₀ : Point d) : OptimizerCache d :=
  (x₀, 0, (fun _ => (0, 0)), (fun _ => (0, 0)))

def gradientMove {d : ℕ} (P : Parameters) (ε : ℝ) (x g : Point d) : Point d :=
  x + (-(ε / (4 * P.gradientLip))) • ((‖g‖⁻¹ : ℝ) • g)

def curvatureFirstProgram {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (signs : ℕ → Bool) :
    ℕ → ℕ → OptimizerCache d →
      OracleProgram (PersistentQuery ((T + 1) * Bg + (T + 1) * BH) d) (PersistentReply d) (Option (Point d))
  | 0, _, _ => .done none
  | m + 1, t, s =>
    OracleProgram.bind
      (checkpointProgram hBH scaleH P.hessianNoise P.hessianLip false Prod.snd
        (hessianReserve T Bg BH) t s.2.2.2 s.1)
      (fun packetH =>
        let H := checkpointValue t s.2.2.2 packetH
        let cacheH := installCheckpoint t s.2.2.2 s.1 packetH
        let replyH := sourceCurvatureSelector (3 * γ / 4) H
        if curvatureTag replyH then
          curvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m (t + 1)
            (curvatureNext (γ / P.hessianLip) s.1 (curvatureVector replyH) (signs t),
              s.2.1, s.2.2.1, cacheH)
        else
          OracleProgram.bind
            (checkpointProgram hBg scaleG P.gradientNoise P.gradientLip true Prod.fst
              (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1)
            (fun packetG =>
              let g := checkpointValue s.2.1 s.2.2.1 packetG
              let cacheG := installCheckpoint s.2.1 s.2.2.1 s.1 packetG
              if ‖g‖ ≤ 3 * ε / 4 then .done (some s.1) else
                curvatureFirstProgram hBg hBH P ε γ scaleG scaleH signs m (t + 1)
                  (gradientMove P ε s.1 g, s.2.1 + 1, cacheG, cacheH)))

theorem curvatureFirstProgram_usesAtMost {d T Bg BH : ℕ} (hBg : 0 < Bg) (hBH : 0 < BH)
    (P : Parameters) (ε γ scaleG scaleH : ℝ) (signs : ℕ → Bool)
    (hsg : 0 ≤ scaleG) (hsh : 0 ≤ scaleH)
    (hcg : Bg = batchSize scaleG (P.gradientNoise^2))
    (hch : BH = batchSize scaleH (P.hessianNoise^2))
    (m t : ℕ) (s : OptimizerCache d) :
    OracleProgram.UsesAtMost (m * (2 * BH + 2 * Bg))
      (curvatureFirstProgram (T := T) hBg hBH P ε γ scaleG scaleH signs m t s) := by
  induction m generalizing t s with
  | zero => simp only [curvatureFirstProgram, OracleProgram.UsesAtMost]
  | succ m ih =>
    have hpH := checkpointProgram_usesAtMost hBH (L := P.hessianLip) hsh hch false Prod.snd (hessianReserve T Bg BH) t s.2.2.2 s.1
    have hpG := checkpointProgram_usesAtMost hBg (L := P.gradientLip) hsg hcg true Prod.fst (gradientReserve T Bg BH) s.2.1 s.2.2.1 s.1
    unfold curvatureFirstProgram
    rw [show (m + 1) * (2 * BH + 2 * Bg) = 2 * BH + (2 * Bg + m * (2 * BH + 2 * Bg)) by ring]
    apply OracleProgram.usesAtMost_bind hpH
    intro packetH
    dsimp only
    split_ifs
    · exact OracleProgram.usesAtMost_mono (ih (t + 1) _) (by omega)
    · apply OracleProgram.usesAtMost_bind hpG
      intro packetG
      dsimp only
      split_ifs
      · simp only [OracleProgram.UsesAtMost]
      · exact ih (t + 1) _

end
end SampleReuse
