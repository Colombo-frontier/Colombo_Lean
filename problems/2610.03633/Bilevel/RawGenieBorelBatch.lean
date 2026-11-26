import Bilevel.RawGenieBorelProbability
import Bilevel.TransportRoundBatch

/-! Frozen finite query batches for the selected-frame genie. The vectors
are computed from the entering memory once; intermediate projection replies
do not alter later batch inputs. This permits charging actual transported
generators as additional observer insertions, without additional SFO calls. -/
noncomputable section
open MeasureTheory
universe u
namespace Bilevel.RawGenieBorel
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

abbrev BatchMemory (H : Memory.{u}) (d T : ℕ) := Memory.of (H × Frame d T)

def batchPrefix {d T m r : ℕ} {H : Memory.{u}} (next : Policy d T (BatchMemory H d T) m r) :
    (b : ℕ) → (q : H → Fin b → Space d) → Measurable q →
    Policy d T (BatchMemory H d T) (m+b) r
  | 0,_,_ => next
  | b+1,q,hq => .query (fun p => q p.1 0)
      (((measurable_pi_apply 0).comp hq).comp measurable_fst)
      (fun p => (p.1.1,p.2)) ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      (batchPrefix next b (fun h i => q h i.succ)
        (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp hq)))

theorem span_zero (d : ℕ) (q : Fin 0 → Space d) : TransportGeneratorStore.span q=⊥ := by
  have he : Set.range q=∅ := by ext x;simp
  rw [TransportGeneratorStore.span,he,Submodule.span_empty]

theorem span_insert_all {d b : ℕ} (V : Submodule ℝ (Space d)) (q : Fin (b+1) → Space d) :
    V ⊔ TransportGeneratorStore.span q=
      (V ⊔ Submodule.span ℝ {q 0}) ⊔ TransportGeneratorStore.span (fun i : Fin b => q i.succ) := by
  have hq : q=Fin.cons (q 0) (fun i : Fin b => q i.succ) := by
    funext i
    cases i using Fin.cases <;> rfl
  conv_lhs => rw [hq,TransportGeneratorStore.span_cons]
  ac_rfl

theorem batchPrefix_safe {d T m r : ℕ} {H : Memory.{u}}
    (next : Policy d T (BatchMemory H d T) m r) (cap : ℝ) :
    ∀ (b : ℕ) (q : H → Fin b → Space d) (hq : Measurable q) (h : H)
      (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T),
    RawGenieProtocol.Safe cap (compile (batchPrefix next b q hq)
      (h,RawGenieProtocol.projections d T V U)) V S U →
    RawGenieProtocol.Safe cap (compile next
      (h,RawGenieProtocol.projections d T (V ⊔ TransportGeneratorStore.span (q h)) U))
      (V ⊔ TransportGeneratorStore.span (q h)) S U := by
  intro b
  induction b with
  | zero =>
    intro q hq h V S U hs
    simpa only [span_zero,sup_bot_eq] using hs
  | succ b ih =>
    intro q hq h V S U hs
    have hn := ih (fun h i => q h i.succ)
      (measurable_pi_lambda _ (fun i => (measurable_pi_apply i.succ).comp hq)) h
      (V ⊔ Submodule.span ℝ {q h 0}) S U hs.2
    rw [←span_insert_all] at hn
    exact hn

theorem batchPrefix_energy {d T m r b : ℕ} {H : Memory.{u}}
    (next : Policy d T (BatchMemory H d T) m r) (cap : ℝ)
    (q : H → Fin b → Space d) (hq : Measurable q) (h : H)
    (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T)
    (hs : RawGenieProtocol.Safe cap (compile (batchPrefix next b q hq)
      (h,RawGenieProtocol.projections d T V U)) V S U) :
    GenieProtocol.BoundedEnergy (V ⊔ TransportGeneratorStore.span (q h)) S U cap :=
  RawGenieProtocol.safe_current _ _ _ _ _ (batchPrefix_safe next cap b q hq h V S U hs)

def transportQueries {n D m : ℕ} {H : Memory.{u}}
    (g : H → TransportRound.Generators n D m) (z : H → TransportNetwork.Latent n D)
    (v : TransportNetwork.Vertex n) (h : H) : Fin (m+(n*m+n*m)) → Space D :=
  TransportRound.execute (g h) (z h) v

theorem transportQueries_measurable {n D m : ℕ} {H : Memory.{u}}
    (g : H → TransportRound.Generators n D m) (hg : Measurable g)
    (z : H → TransportNetwork.Latent n D) (hz : Measurable z) (v : TransportNetwork.Vertex n) :
    Measurable (transportQueries g z v) :=
  (measurable_pi_apply v).comp ((TransportRound.execute_measurable n D m).comp (hg.prodMk hz))

theorem transportBatch_energy {n D T m a r : ℕ} {H : Memory.{u}}
    (next : Policy D T (BatchMemory H D T) a r) (cap : ℝ)
    (g : H → TransportRound.Generators n D m) (hg : Measurable g)
    (z : H → TransportNetwork.Latent n D) (hz : Measurable z) (v : TransportNetwork.Vertex n)
    (h : H) (V : Submodule ℝ (Space D)) (S : Set (Fin T)) (U : Frame D T)
    (hs : RawGenieProtocol.Safe cap (compile (batchPrefix next (m+(n*m+n*m))
      (transportQueries g z v) (transportQueries_measurable g hg z hz v))
      (h,RawGenieProtocol.projections D T V U)) V S U) :
    GenieProtocol.BoundedEnergy (V ⊔ TransportRound.known (TransportRound.execute (g h) (z h)) v) S U cap :=
  batchPrefix_energy next cap (transportQueries g z v) (transportQueries_measurable g hg z hz v) h V S U hs

end Bilevel.RawGenieBorel
