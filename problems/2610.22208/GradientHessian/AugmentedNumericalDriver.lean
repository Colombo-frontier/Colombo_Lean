import GradientHessian.AugmentedNumericalRuntime
import GradientHessian.AugmentedPolicyReplay
import GradientHessian.NumericalPostprocessorMeasurability

/-! A suspended augmented controller. The left summand contains no policy
state. Initialization is a free transition performed only after the public
initial packet is available, including the first active numerical mark. -/

noncomputable section
namespace GradientHessian.AugmentedNumericalDriver
open Classical HigherHierarchy HierarchyAddresses RawHierarchy FrontierState TaskState
  GeometricRepair ControllerPolicyDriver NumericalCachedOracle NumericalCoefficientPatch

theorem measurable_prod_sum {U V W Z : Type*} [MeasurableSpace U] [MeasurableSpace V]
    [MeasurableSpace W] [MeasurableSpace Z] (f : U × (V ⊕ W) → Z)
    (hl : Measurable (fun q : U × V => f (q.1,Sum.inl q.2)))
    (hr : Measurable (fun q : U × W => f (q.1,Sum.inr q.2))) : Measurable f := by
  have h := (hl.sumElim hr).comp (MeasurableEquiv.prodSumDistrib U V W).measurable
  convert h using 1
  funext q
  rcases q with ⟨u,v|w⟩ <;> rfl

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (t : ℕ)

abbrev Cursor := PUnit ⊕ Config (t+1) (4096*J^2+1) ell S
  (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2))

def state : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t →
    State (t+1) (4096*J^2+1) ell
  | .inl _ => TaskState.initial
  | .inr q => ControllerDriverMonotonicity.stateOf q

def finished : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t → Bool
  | .inl _ => false
  | .inr q => NumericalDriverInstructions.finished q

def point : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t →
    DirectionPolicyReplay.Point d J E H t
  | .inl _ => 0
  | .inr q => NumericalDriverInstructions.point q

def product (leaf : Leaf (t+1)) (stop : State (t+1) (4096*J^2+1) ell → Bool) :
    Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t → Bool
  | .inl _ => false
  | .inr q => NumericalDriverInstructions.product leaf stop q

def normalInstruction : Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t → Bool
  | .inl _ => false
  | .inr q => NumericalPostprocessor.normalInstruction t q

variable [MeasurableSpace (DirectionPolicyReplay.Point d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Point d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)]
  [BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (leaf : Leaf (t+1))
  (policy : Machine.Policy (Seed × AugmentedPolicy.Packet d J E H t ell) S
    (DirectionPolicyReplay.Point d J E H t)
    (AugmentedPolicy.Ordinary d J E H t ell) (AugmentedPolicy.Rich d J E H t ell))

def startConfig (K : ℝ) (N : ℕ) (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J) :
    Config (t+1) (4096*J^2+1) ell S (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)) :=
  ControllerPolicyDriver.initial policy N
    (seed,AugmentedNumericalPacket.packet P B fallback t leaf K w c TaskState.initial) TaskState.initial

def advance (K : ℝ) (N : ℕ) (stop : State (t+1) (4096*J^2+1) ell → Bool)
    (seed : Seed) (w : RawLeafFactor.Rest d n r J E H t) (c : Cache d J)
    (Ay : EuclideanSpace ℝ (Fin d)) :
    Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t →
      Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t
  | .inl _ => .inr (startConfig t P B fallback leaf policy K N seed w c)
  | .inr q => .inr (AugmentedNumericalRuntime.advance P B fallback t leaf policy K stop w c Ay q)

theorem initialize_before_supply (K : ℝ) (N : ℕ) (seed : Seed)
    (x : Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hs : AugmentedDisclosure.markStop leaf j (TaskState.initial (ell := ell))=false)
    (hb : ∀ k,k<j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k) :
    startConfig t P B fallback leaf policy K N seed (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c=
      ControllerPolicyDriver.initial policy N
        (seed,AugmentedDisclosure.view K (assemble P B fallback t x) TaskState.initial) TaskState.initial := by
  unfold startConfig
  rw [AugmentedNumericalPacket.packet_before_supply P B fallback t leaf K x c j TaskState.initial hs hb ha]

theorem initialize_after_supply (K : ℝ) (N : ℕ) (seed : Seed)
    (x : Raw d n r J E H t) (c : Cache d J) (j : Fin (4096*J^2+1))
    (hb : ∀ k,k≤j → c.1 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.1 k)
    (ha : ∀ k,k<j → c.2 k=(atLeaf t ((leafEquiv t).symm leaf) (coefficients P B fallback t x)).2.2.1 k) :
    startConfig t P B fallback leaf policy K N seed (RawLeafFactor.factor t ((leafEquiv t).symm leaf) x).2 c=
      ControllerPolicyDriver.initial policy N
        (seed,AugmentedDisclosure.view K (assemble P B fallback t x) TaskState.initial) TaskState.initial := by
  unfold startConfig
  rw [AugmentedNumericalPacket.packet_before_disclosure P B fallback t leaf K x c j TaskState.initial
    (by simp [ComparisonControllerReplay.taskDisclosed,TaskState.initial]) hb ha]

theorem state_measurable : Measurable (state (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :=
  measurable_sum measurable_const NumericalDriverInstructions.stateOf_measurable

theorem finished_measurable : Measurable (finished (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :=
  measurable_sum measurable_const NumericalDriverInstructions.finished_measurable

theorem point_measurable : Measurable (point (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :=
  measurable_sum measurable_const NumericalDriverInstructions.point_measurable

theorem product_measurable (stop : State (t+1) (4096*J^2+1) ell → Bool) :
    Measurable (product (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t leaf stop) :=
  measurable_sum measurable_const (NumericalDriverInstructions.product_measurable leaf stop)

theorem normalInstruction_measurable :
    Measurable (normalInstruction (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t) :=
  measurable_sum measurable_const (NumericalPostprocessor.normalInstruction_measurable t)

theorem initialize_measurable (K : ℝ) (N : ℕ) :
    Measurable (fun q : (RawLeafFactor.Rest d n r J E H t × Cache d J) × Seed =>
      startConfig t P B fallback leaf policy K N q.2 q.1.1 q.1.2) :=
  (ControllerPolicyDriver.initial_measurable (A := Action t (4096*J^2)) policy N TaskState.initial).comp
    (measurable_snd.prodMk
      ((AugmentedNumericalPacket.packet_fixed_measurable P B fallback t leaf K TaskState.initial).comp measurable_fst))

theorem advance_measurable {K : ℝ} (hK : 0<K) (N : ℕ)
    (stop : State (t+1) (4096*J^2+1) ell → Bool) :
    Measurable (fun q : (((RawLeafFactor.Rest d n r J E H t × Cache d J) × Seed) ×
        EuclideanSpace ℝ (Fin d)) × Cursor (d := d) (J := J) (ell := ell) (E := E) (H := H) (S := S) t =>
      advance t P B fallback leaf policy K N stop q.1.1.2 q.1.1.1.1 q.1.1.1.2 q.1.2 q.2) := by
  apply measurable_prod_sum
  · exact measurable_inr.comp ((initialize_measurable t P B fallback leaf policy K N).comp
      (measurable_fst.comp measurable_fst))
  · have hm : Measurable (fun q : (((RawLeafFactor.Rest d n r J E H t × Cache d J) × Seed) ×
        EuclideanSpace ℝ (Fin d)) × Config (t+1) (4096*J^2+1) ell S
          (DirectionPolicyReplay.Point d J E H t) (Action t (4096*J^2)) =>
        ((q.1.1.1,q.1.2),q.2)) :=
      (((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
    have hstep := (AugmentedNumericalRuntime.advance_measurable P B fallback t leaf policy hK stop).comp hm
    exact measurable_inr.comp hstep

end GradientHessian.AugmentedNumericalDriver

