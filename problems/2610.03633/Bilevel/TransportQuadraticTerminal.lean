import Bilevel.TransportQuadraticObserved
import Bilevel.TransportTerminalCoordinate
import Bilevel.TransportPublicCapBounds

/-! The arbitrary terminal output of the SAME compiled quadratic run has
a blind last macro coordinate before the transport capacity is reached.
No assumption that this output was previously queried is introduced. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
universe u v
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration
  ChiHierarchyExecution EndpointTransportResponse TransportRound TransportNetwork
  PrimitiveGeometry PartialLegendre TransportAugmented
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem quadraticObserved_terminal {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
    (macroN n D : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
    (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤D)
    (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) 0,chainSize i+1≤D)
    (hT : capacity (sourceCounts macroN cn ratios resolutions) 1 0≤D)
    (hA : auxiliaryCapacity (sourceCounts macroN cn ratios resolutions) 0+1≤D)
    (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km ν ρ R δ c : ℝ)
    [MeasurableSpace (Physical n D)] [BorelSpace (Physical n D)]
    [MeasurableSpace (QuadraticOutput D)] [BorelSpace (QuadraticOutput D)]
    [MeasurableSpace (QuadraticQuery n D)] [BorelSpace (QuadraticQuery n D)]
    (P : BorelAdaptive.Program S (QuadraticQuery n D) (QuadraticReply n D) (QuadraticOutput D))
    (start : C → S) (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hweight : ∀ j,0<weight j)
    (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km) (τ : ℝ) (hτ : 0<τ) (N : ℕ)
    (hN : N<(n+1)*capacity (sourceCounts macroN cn ratios resolutions) 1 0)
    (s : C × PhysicalSample (sourceCounts macroN cn ratios resolutions) 0 n D)
    (hobs : quadraticObserved macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start τ N s) :
    let st := quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
      A Kminus ζ CR Km ν ρ R δ c P start s N
    let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s.2 initial Km
    M.coordinates (P.output st.1.2.2.1).fst (Fin.last macroN)<M.width := by
  let counts := sourceCounts macroN cn ratios resolutions
  let ctl := quadraticController (C:=C) macroN n D cn ratios resolutions hdim hAll hT initial weight
    A Kminus ζ CR Km ν ρ R δ c P
  let schedule := auxiliaryRoundSchedule counts 0 (n+1) (Nat.succ_pos n)
  let st := quadraticRun macroN n D cn ratios resolutions hdim hAll hT hA initial weight
    A Kminus ζ CR Km ν ρ R δ c P start s N
  let M := sourcePhysicalMacro macroN 0 n D cn ratios resolutions hAll s.2 initial Km
  let cap := sourcePublicCap macroN 0 initial ratios resolutions weight CR ζ Km τ
  have hc := sourcePublicCap_budgets macroN 0 initial ratios resolutions weight CR ζ Km τ
    hl hw hr hη hweight hCR hζ hKm hτ
  have hk : 0<Fintype.card (FrameIndex counts 0) := Fintype.card_pos_iff.mpr ⟨Sum.inl ()⟩
  have hB : 0<Fintype.card (FrameIndex counts 0)*(auxiliaryCapacity counts 0+1)+1 := by omega
  have hcount : schedule.count N (enumerate counts 0 (Sum.inl ()))≤
      (auxiliaryColumnIndex counts 0 (Sum.inl ()) (Fin.last macroN)).val := by
    rw [auxiliaryRoundSchedule_macro]
    exact macro_incomplete_before_transport_capacity counts 0 (n+1) N (Nat.succ_pos n) hN
  have hi := FrameObservedAny.terminal_inner hk schedule (enlargeBatch ctl) hT hA
    (enumerate counts 0 (Sum.inl ())) hB start (fun _ => ctl.auxiliaryOutput)
    (fun _ => ctl.auxiliaryOutput_measurable) cap hc.1.le s N (hobs.2 (enumerate counts 0 (Sum.inl ())))
    (auxiliaryColumnIndex counts 0 (Sum.inl ()) (Fin.last macroN)) hcount
  rw [auxiliary_column_nested hAll hA s.2 (Sum.inl ()) (Fin.last macroN)] at hi
  have hMR : 0<M.radius := by
    change 0<Km*initial.width*Real.sqrt ((macroN:ℝ)+1)
    positivity
  have hb := terminal_coordinate_bound M hMR (P.output st.1.2.2.1).fst (Fin.last macroN) cap hi
  have hbudget : M.radius*Real.sqrt cap≤M.width/8 := hc.2.2 (Sum.inl ())
  have hMw : 0<M.width := hw
  exact (le_abs_self _).trans_lt ((hb.trans hbudget).trans_lt (by linarith))

end Bilevel.TransportHierarchy
