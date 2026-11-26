import Bilevel.ChiCarrierSupportSpace
import Bilevel.ChiExtensionReassociate
import Bilevel.NearIdentityRestricted

/-! The actual closed restricted space keeps every public normal coordinate
and only the disclosed tangential coordinates. Its gradient membership is
equivalent to support of the actual tangential partial gradient. -/
noncomputable section
namespace Bilevel.ChiCarrier
open PrimitiveGeometry ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def normalKnown {m : ℕ} (W : Fin m → Submodule ℝ E) (s : ℕ) : Submodule ℝ (Full (Blocks m E) s) where
  carrier := {z | z.fst∈knownSpace W}
  zero_mem' := (knownSpace W).zero_mem
  add_mem' := fun hz hw => (knownSpace W).add_mem hz hw
  smul_mem' := fun c _ hz => (knownSpace W).smul_mem c hz

omit [CompleteSpace E] in
theorem mem_normalKnown {m s : ℕ} (W : Fin m → Submodule ℝ E) (z : Full (Blocks m E) s) :
    z∈normalKnown W s ↔ z.fst∈knownSpace W := Iff.rfl

omit [CompleteSpace E] in
theorem knownSpace_isClosed {m : ℕ} (W : Fin m → Submodule ℝ E) (hW : ∀ i,IsClosed (W i : Set E)) :
    IsClosed (knownSpace W : Set (Blocks m E)) := by
  have h : IsClosed (⋂ i : Fin m,(PiLp.proj 2 (fun _ : Fin m => E) i : Blocks m E →L[ℝ] E) ⁻¹' (W i : Set E)) :=
    isClosed_iInter (fun i => (hW i).preimage
      (PiLp.proj 2 (fun _ : Fin m => E) i : Blocks m E →L[ℝ] E).continuous)
  convert h using 1
  ext x
  simp only [Set.mem_iInter,Set.mem_preimage,Submodule.mem_carrier,PiLp.proj_apply,mem_knownSpace]
  rfl

omit [CompleteSpace E] in
theorem normalKnown_isClosed {m : ℕ} (W : Fin m → Submodule ℝ E) (hW : ∀ i,IsClosed (W i : Set E)) (s : ℕ) :
    IsClosed (normalKnown W s : Set (Full (Blocks m E) s)) := by
  let pr : Full (Blocks m E) s →L[ℝ] Blocks m E :=
    (ContinuousLinearMap.fst ℝ (Blocks m E) (Normals s)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (Blocks m E) (Normals s)).toContinuousLinearMap
  exact (knownSpace_isClosed W hW).preimage pr.continuous

theorem gradient_normalKnown_iff {m s : ℕ} (W : Fin m → Submodule ℝ E)
    {f : Full (Blocks m E) s → ℝ} (x : Blocks m E) (q : Normals s)
    (hf : DifferentiableAt ℝ f (pack x q)) :
    gradient f (pack x q)∈normalKnown W s ↔
      gradient (fun y => f (pack y q)) x∈knownSpace W := by
  have hp := hf.hasGradientAt
  change HasGradientAt f (pack ((gradient f (pack x q)).fst) ((gradient f (pack x q)).snd)) (pack x q) at hp
  rw [mem_normalKnown,(PrimitiveGeometry.partial_x hp).gradient]

end Bilevel.ChiCarrier
