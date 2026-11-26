import Bilevel.TransportPhysicalObserved
import Bilevel.TransportTerminalCoordinate
import Bilevel.TransportPublicCapBounds
import Bilevel.TransportPhysicalOutput
import Bilevel.TransportAugmentedBudgetProbability

/-! Literal same-prior execution and inclusion of each queried coordinate
in its prebatch analytical space. The common auxiliary space contains all
ordinary lower points before the frozen network answers are returned. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiCarrier ChiExtensionCalibration
  EndpointTransportResponse TransportRound TransportNetwork PrimitiveGeometry PartialLegendre
  TransportAugmented ChiExtension ChiHierarchyExecution
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  (macroN J n D s : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤D)
  (hT : capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0≤D)
  (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) J+1≤D)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν : ℝ) (fine : ChiFine.Parameters)
  (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (ρ R : ℕ → ℝ) (dn : ℝ) (b : Normals s) (m δ c₀ cend : ℝ)
  [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
  [MeasurableSpace (PhysicalOutput J D)] [BorelSpace (PhysicalOutput J D)]
  [MeasurableSpace (PhysicalQuery J n D s)] [BorelSpace (PhysicalQuery J n D s)]
  (P : BorelAdaptive.Program S (PhysicalQuery J n D s) (PhysicalReply J n D s) (PhysicalOutput J D))
  (start : C → S)



theorem physicalObserved_terminal
    (hl : 0 < initial.curvature) (hw : 0 < initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hweight : ∀ j,0<weight j)
    (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km) (τ : ℝ) (hτ : 0<τ) (N : ℕ)
    (hN : N<(n+1)*capacity (sourceCounts macroN cn ratios resolutions) (J+1) 0)
    (ω : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) J n D)
    (hobs : physicalObserved macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start τ N ω) :
    let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω N
    let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll ω.2 initial Km
    M.coordinates (P.output st.1.2.2.1).fst.fst (Fin.last macroN)<M.width := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := physicalController (C:=C) macroN J n D s cn ratios resolutions hdim hAll hT initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P
  let schedule := auxiliaryRoundSchedule counts J (n+1) (Nat.succ_pos n)
  let st := physicalRun macroN J n D s cn ratios resolutions hdim hAll hT hA initial weight A Kminus ζ CR Km ν fine index radialIndex fineIndex ρ R dn b m δ c₀ cend P start ω N
  let M := sourcePhysicalMacro macroN J n D cn ratios resolutions hAll ω.2 initial Km
  let cap := sourcePublicCap macroN J initial ratios resolutions weight CR ζ Km τ
  have hc := sourcePublicCap_budgets macroN J initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ
  have hk : 0<Fintype.card (FrameIndex counts J) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  have hB : 0<Fintype.card (FrameIndex counts J)*(auxiliaryCapacity counts J+1)+(J+1) := by omega
  have hcount : schedule.count N (enumerate counts J (Sum.inl ()))≤
      (auxiliaryColumnIndex counts J (Sum.inl ()) (Fin.last macroN)).val := by
    rw [auxiliaryRoundSchedule_macro]
    exact macro_incomplete_before_transport_capacity counts J (n+1) N (Nat.succ_pos n) hN
  have hi := FrameObservedAny.terminal_inner hk schedule (enlargeBatch ctl) hT hA
    (enumerate counts J (Sum.inl ())) hB start (physicalObserverOutput counts P)
    (physicalObserverOutput_measurable counts P) cap hc.1.le ω N (hobs.2 (enumerate counts J (Sum.inl ())))
    (auxiliaryColumnIndex counts J (Sum.inl ()) (Fin.last macroN)) hcount
  rw [auxiliary_column_nested hAll hA ω.2 (Sum.inl ()) (Fin.last macroN)] at hi
  simp only [physicalObserverOutput,Equiv.symm_apply_apply,physicalFrameOutput] at hi
  have hMR : 0<M.radius := by
    change 0<Km*initial.width*Real.sqrt ((macroN:ℝ)+1)
    positivity
  have hb := terminal_coordinate_bound M hMR (P.output st.1.2.2.1).fst.fst (Fin.last macroN) cap hi
  have hbudget : M.radius*Real.sqrt cap≤M.width/8 := hc.2.2 (Sum.inl ())
  have hMw : 0<M.width := hw
  exact (le_abs_self _).trans_lt ((hb.trans hbudget).trans_lt (by linarith only [hMw]))

end Bilevel.TransportHierarchy
