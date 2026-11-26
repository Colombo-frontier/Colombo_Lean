import Bilevel.ChiSourcePointwiseReply
import Bilevel.ChiCanonicalProjection
import Bilevel.NearIdentityConfinement
import Bilevel.ChiPrefixFrame

/-! A single useful frame embedded in the already verified finite source
protocol. Every child has one column and is ignored by the actual reply;
these independent auxiliary frames strengthen only the observation genie.
The useful prefix advances exactly once per successful live coin. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped RealInnerProductSpace
namespace Bilevel.SingleFrameSource
open ChiHierarchyIndex ChiHierarchyExecution ChiHierarchyHaar ChiTreeProgress

def counts (n : ℕ) (j : ℕ) : ℕ := if j=0 then n else 0

theorem capacity_eq (n : ℕ) : capacity (counts n) 1 0=n+1 := by
  simp [capacity,counts]

theorem retained_macro (n q : ℕ) : retained (counts n) 0 q (Sum.inl ())=min (n+1) q := by
  simp [retained,counter,nodePrefix,parentPrefix,nodeBudget,capacity,counts]

abbrev Columns (n : ℕ) (E : Type*) := Fin (n+1) → E
abbrev Store (n : ℕ) (E : Type*) := ChiHierarchyIndex.Store (counts n) 0 E

def macroColumns {E : Type*} (n : ℕ) (s : Store n E) : Columns n E := s.2 (Sum.inl ())

theorem macroColumns_measurable {E : Type*} [MeasurableSpace E] (n : ℕ) :
    Measurable (macroColumns (E:=E) n) := (measurable_pi_apply (Sum.inl ())).comp measurable_snd

theorem actual_macro {E : Type*} [NormedAddCommGroup E] (n q : ℕ)
    (U : FiniteColumns (counts n) 0 E) (k : Fin (n+1)) (hk : k.val<q) :
    macroColumns n (actual (counts n) 0 q U) k=U (Sum.inl ()) k := by
  simp only [macroColumns,actual,ChiPrefixEvaluation.paddedPrefix,retained_macro]
  exact if_pos (lt_min k.isLt hk)

theorem coordinate_small {n D : ℕ}
    (hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D)
    (a : Orientations (counts n) 0 D) (q : ℕ)
    (W : Submodule ℝ (EuclideanGaussian.Space D))
    (R τ cap : ℝ) (hR : 0<R) (hτ : 0<τ) (hcap : 0≤cap)
    (hsmall : R*Real.sqrt cap≤τ/2)
    (hE : GenieProtocol.BoundedEnergy W (prefixSet (retained (counts n) 0 q (Sum.inl ())))
      (columns hD a (Sum.inl ())) cap)
    (u : EuclideanGaussian.Space D) (hu : u∈W) (k : Fin (n+1)) (hk : q≤k.val) :
    |WrappedChain.coordinates n R (frame hD a (Sum.inl ())) u k|<τ := by
  have hp := frame_projection_norm_bound W (retained (counts n) 0 q (Sum.inl ()))
    (columns hD a (Sum.inl ())) cap hcap hE k (by rw [retained_macro];exact (Nat.min_le_right _ _).trans hk)
  have hc := NearIdentityConfinement.undisclosed_readout_bound W R hR
    (frame hD a (Sum.inl ()) (ZeroChain.basis k)) ⟨u,hu⟩ le_rfl
  rw [ChiPrefixEvaluation.coordinates_inner]
  have hb : R*‖W.orthogonalProjection (frame hD a (Sum.inl ()) (ZeroChain.basis k))‖≤τ/2 := by
    change R*‖W.orthogonalProjection (frame hD a (Sum.inl ()) (ChiBoundedChain.basis k))‖≤τ/2
    rw [frame_basis]
    exact (mul_le_mul_of_nonneg_left hp hR.le).trans hsmall
  exact hc.trans_lt (hb.trans_lt (by linarith))

end Bilevel.SingleFrameSource
