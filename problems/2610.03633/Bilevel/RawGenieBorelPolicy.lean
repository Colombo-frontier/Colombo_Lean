import Bilevel.RawGenieMeasurable
import Bilevel.RawGenieTheorem
import Bilevel.TransportControllerMachine

/-! Executable Borel raw-projection policies. The response to a query contains
the projections of every frame column onto the enlarged information space.
Full-column revelations update that same space; no orthogonality of an
unrevealed column to the old space is assumed. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.RawGenieBorel
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

inductive Policy (d T : ℕ) : Memory.{u} → ℕ → ℕ → Type (u+1)
  | halt {H : Memory.{u}} {m r : ℕ} : Policy d T H m r
  | query {H K : Memory.{u}} {m r : ℕ} (q : H → Space d) (hq : Measurable q)
      (respond : H × Frame d T → K) (hr : Measurable respond)
      (next : Policy d T K m r) : Policy d T H (m+1) r
  | reveal {H K : Memory.{u}} {m r : ℕ} (j : H → Fin T) (hj : Measurable j)
      (respond : H × (Space d × Frame d T) → K) (hr : Measurable respond)
      (next : Policy d T K m r) : Policy d T H m (r+1)
  | adapt {H K : Memory.{u}} {m r : ℕ} (update : H → K) (hu : Measurable update)
      (next : Policy d T K m r) : Policy d T H m r
  | branch {H : Memory.{u}} {m r : ℕ} (A : Set H) (hA : MeasurableSet A)
      (yes no : Policy d T H m r) : Policy d T H m r

open Classical in
def compile {d T : ℕ} : {H : Memory.{u}} → {m r : ℕ} →
    Policy d T H m r → H → RawGenieProtocol.Protocol d T m r
  | _,_,_,.halt,_ => .halt
  | _,_,_,.query q _ respond _ next,h => .query (q h) (fun Z => compile next (respond (h,Z)))
  | _,_,_,.reveal j _ respond _ next,h => .reveal (j h) (fun Z => compile next (respond (h,Z)))
  | _,_,_,.adapt update _ next,h => compile next (update h)
  | _,_,_,.branch A _ yes no,h => if h∈A then compile yes h else compile no h

theorem compile_family {d T m r : ℕ} {H : Memory.{u}} (P : Policy d T H m r) :
    RawGenieProtocol.MeasurableFamily (compile P) := by
  induction P with
  | halt => exact RawGenieProtocol.MeasurableFamily.halt
  | query q hq respond hr next ih =>
    exact RawGenieProtocol.MeasurableFamily.query q hq _ (ih.comap respond hr)
  | reveal j hj respond hr next ih =>
    exact RawGenieProtocol.MeasurableFamily.reveal j hj _ (ih.comap respond hr)
  | adapt update hu next ih => exact ih.comap update hu
  | branch A hA yes no hy hn =>
    exact hy.piecewise hn A hA

theorem compile_regular {d T m r : ℕ} {H : Memory.{u}}
    (P : Policy d T H m r) (h : H) (V : Submodule ℝ (Space d)) (Z : Frame d T) (b : ℝ) :
    GenieProtocol.Regular b (RawGenieProtocol.normalize (compile P h) V Z) :=
  (compile_family P).regular h V Z b

theorem unsafe_probability {d T M R n : ℕ} {H : Memory.{u}} (hT : T≤d)
    (P : Policy d T H M R) (h : H) (b : ℝ) (hb : 0<b) (hb2 : b≤2)
    (hd : M+R+(n+1)≤d) (hcap : (R:ℝ)*((M:ℝ)*b)≤1/2) :
    (HaarFrame.frameLaw d T hT) {U | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*b) R) (compile P h) ⊥ ∅ U} ≤
      (M:ENNReal)*GenieProtocol.failurePerQuery T n b :=
  RawGenieProtocol.unsafe_probability d T M R n hT (compile P h) b hb hb2 hd hcap
    (compile_regular P h ⊥ 0 b)

theorem logarithmic_energy_bound {d T M n : ℕ} {H : Memory.{u}} (hT : T≤d)
    (hMpos : 0<M) (hTpos : 0<T) (hnpos : 0<n) (P : Policy d T H M T) (h : H)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1) (hd : M+T+(n+1)≤d)
    (hcap : (T:ℝ)*((M:ℝ)*GenieProtocol.logarithmicIncrement M T n δ)≤1/2) :
    (HaarFrame.frameLaw d T hT).real {U | ¬RawGenieProtocol.Safe
      (ProjectionEnergy.envelope ((M:ℝ)*GenieProtocol.logarithmicIncrement M T n δ) T)
      (compile P h) ⊥ ∅ U} ≤ δ/2 :=
  RawGenieProtocol.logarithmic_energy_bound d T M n hT hMpos hTpos hnpos
    (compile P h) δ hδ hδ1 hd hcap (compile_regular P h ⊥ 0 _)

end Bilevel.RawGenieBorel
