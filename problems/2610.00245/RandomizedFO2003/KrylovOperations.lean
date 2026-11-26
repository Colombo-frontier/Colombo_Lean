import RandomizedFO2003.KrylovCalculus
import RandomizedFO2003.PaddedExposure

namespace RandomizedFO2003.Rotations

/-- The response labels explicitly separate matrix actions from an authorized
marked-vector reveal. An unauthorized reveal must request zero. -/
inductive LatentOperation where
  | query
  | matrix
  | mark (authorized : Bool)
  deriving DecidableEq

def LatentOperation.kind : LatentOperation → ExposureKind
  | .query => .query
  | .matrix | .mark _ => .response

/-- The number of marked powers available after this operation. Matrix actions
cannot start the marked branch before a first authorized reveal. -/
def LatentOperation.nextDepth : LatentOperation → ℕ → ℕ
  | .query, m => m
  | .matrix, 0 => 0
  | .matrix, m + 1 => m + 2
  | .mark false, m => m
  | .mark true, m => max m 1

theorem LatentOperation.depth_le_next (op : LatentOperation) (m : ℕ) :
    m ≤ op.nextDepth m := by
  cases op with
  | query => exact le_rfl
  | matrix => cases m <;> simp [nextDepth]
  | mark b => cases b <;> simp [nextDepth]

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def LatentOperation.Legal (A : Module.End ℝ E) (u : E) (W : Submodule ℝ E)
    (x : E) : LatentOperation → Prop
  | .query => True
  | .matrix => x ∈ W.map A
  | .mark false => x = 0
  | .mark true => x ∈ Submodule.span ℝ {u}

theorem LatentOperation.step_bound (op : LatentOperation) (A : Module.End ℝ E)
    (u : E) (m : ℕ) (W N : Submodule ℝ E) (x auxiliary g : E)
    (hW : W ≤ powerKrylovSpace A u m ⊔ N) (hN : N.map A ≤ N)
    (ha : auxiliary ∈ N) (hg : g ∈ N) (hx : op.Legal A u W x) :
    W ⊔ op.kind.latentAddition x auxiliary g ≤ powerKrylovSpace A u (op.nextDepth m) ⊔ N := by
  have hmono := sup_le_sup_right (powerKrylovSpace_mono A u (op.depth_le_next m)) N
  refine sup_le (hW.trans hmono) ?_
  cases op with
  | query =>
    change Submodule.span ℝ {g} ≤ powerKrylovSpace A u m ⊔ N
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (Submodule.mem_sup_right hg)
  | matrix =>
    have hmap : (powerKrylovSpace A u m ⊔ N).map A ≤
        powerKrylovSpace A u (LatentOperation.matrix.nextDepth m) ⊔ N := by
      cases m with
      | zero => simpa [nextDepth] using hN
      | succ m => exact map_krylov_sup_le A u (m + 1) N hN
    have hx' := hmap ((Submodule.map_mono hW) hx)
    change Submodule.span ℝ {x, auxiliary} ≤ _
    apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact hx'
    · exact Submodule.mem_sup_right (Set.mem_singleton_iff.mp hv ▸ ha)
  | mark b =>
    have hx' : x ∈ powerKrylovSpace A u ((LatentOperation.mark b).nextDepth m) ⊔ N := by
      cases b with
      | false => exact hx ▸ Submodule.zero_mem _
      | true =>
        apply Submodule.mem_sup_left
        exact ((Submodule.span_singleton_le_iff_mem _ _).mpr
          (self_mem_powerKrylovSpace A u (show 0 < max m 1 by omega))) hx
    change Submodule.span ℝ {x, auxiliary} ≤ _
    apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · exact hx'
    · exact Submodule.mem_sup_right (Set.mem_singleton_iff.mp hv ▸ ha)

end RandomizedFO2003.Rotations
