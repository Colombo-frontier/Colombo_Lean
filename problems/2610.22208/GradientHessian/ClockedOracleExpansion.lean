import GradientHessian.ClockedOraclePolicy

/-! Replace every rich instruction of a public finite schedule by a
fixed finite batch of ordinary queries and a measurable decoding step.
All replies are collected by the compiled machine itself. -/

noncomputable section
namespace GradientHessian.ClockedOracle
open MeasureTheory

variable {Seed W X Y Z : Type*} [MeasurableSpace Seed] [MeasurableSpace W]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

structure Batch (X Y Z : Type*) [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] (r : ℕ) where
  query : Fin r → X → X
  decode : X × (Fin r → Y) → Z
  default : Y
  query_measurable : ∀ i,Measurable (query i)
  decode_measurable : Measurable decode

variable {r : ℕ}

def Batch.oracle (b : Batch X Y Z r) (ordinary : X → Y) (x : X) : Z :=
  b.decode (x,fun i => ordinary (b.query i x))

def batchIndex (r k : ℕ) : ℕ := k/(r+1)
def batchSlot (r k : ℕ) : ℕ := k%(r+1)

theorem batchIndex_clock (r i j : ℕ) (hj : j<r+1) : batchIndex r (i*(r+1)+j)=i := by
  unfold batchIndex
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega),Nat.div_eq_of_lt hj,zero_add]

theorem batchSlot_clock (r i j : ℕ) (hj : j<r+1) : batchSlot r (i*(r+1)+j)=j := by
  unfold batchSlot
  simp [Nat.add_mod,Nat.mod_eq_of_lt hj]

def Program.expandedKind (p : Program Seed W X Y Z) (r k : ℕ) : Fin 3 :=
  if p.kind (batchIndex r k)=2 then if batchSlot r k<r then 1 else 0
  else if batchSlot r k=0 then p.kind (batchIndex r k) else 0

def Program.expandedPoint (p : Program Seed W X Y Z) (b : Batch X Y Z r) (k : ℕ)
    (s : W × (Fin r → Y)) : X :=
  if p.kind (batchIndex r k)=2 then
    if h : batchSlot r k<r then b.query ⟨batchSlot r k,h⟩ (p.point (batchIndex r k) s.1)
    else p.point (batchIndex r k) s.1
  else p.point (batchIndex r k) s.1

def Program.expandedThink (p : Program Seed W X Y Z) (b : Batch X Y Z r) (k : ℕ)
    (s : W × (Fin r → Y)) : W × (Fin r → Y) :=
  if p.kind (batchIndex r k)=2 then
    if batchSlot r k=r then
      (p.richNext (batchIndex r k) (s.1,b.decode (p.point (batchIndex r k) s.1,s.2)),s.2)
    else s
  else if batchSlot r k=0 then (p.think (batchIndex r k) s.1,s.2) else s

def Program.expandedOrdinary (p : Program Seed W X Y Z) (r k : ℕ)
    (s : (W × (Fin r → Y)) × Y) : W × (Fin r → Y) :=
  if p.kind (batchIndex r k)=2 then
    if h : batchSlot r k<r then (s.1.1,Function.update s.1.2 ⟨batchSlot r k,h⟩ s.2) else s.1
  else if batchSlot r k=0 then (p.ordinaryNext (batchIndex r k) (s.1.1,s.2),s.1.2) else s.1

theorem Program.expandedPoint_measurable (p : Program Seed W X Y Z) (b : Batch X Y Z r) (k : ℕ) :
    Measurable (p.expandedPoint b k) := by
  unfold expandedPoint
  split_ifs
  · exact (b.query_measurable _).comp ((p.point_measurable _).comp measurable_fst)
  · exact (p.point_measurable _).comp measurable_fst
  · exact (p.point_measurable _).comp measurable_fst

theorem Program.expandedThink_measurable (p : Program Seed W X Y Z) (b : Batch X Y Z r) (k : ℕ) :
    Measurable (p.expandedThink b k) := by
  unfold expandedThink
  split_ifs
  · exact ((p.richNext_measurable _).comp
      (measurable_fst.prodMk (b.decode_measurable.comp (((p.point_measurable _).comp measurable_fst).prodMk measurable_snd)))).prodMk measurable_snd
  · exact measurable_id
  · exact ((p.think_measurable _).comp measurable_fst).prodMk measurable_snd
  · exact measurable_id

theorem Program.expandedOrdinary_measurable (p : Program Seed W X Y Z) (r k : ℕ) :
    Measurable (p.expandedOrdinary r k) := by
  unfold expandedOrdinary
  split_ifs
  · exact measurable_fst.fst.prodMk (measurable_update'.comp (measurable_fst.snd.prodMk measurable_snd))
  · exact measurable_fst
  · exact ((p.ordinaryNext_measurable _).comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
  · exact measurable_fst

def Program.expand (p : Program Seed W X Y Z) (b : Batch X Y Z r) :
    Program Seed (W × (Fin r → Y)) X Y Z where
  length := p.length*(r+1)
  kind := p.expandedKind r
  initial := fun seed => (p.initial seed,fun _ => b.default)
  point := p.expandedPoint b
  output := fun s => p.output s.1
  think := p.expandedThink b
  ordinaryNext := p.expandedOrdinary r
  richNext := fun _ s => s.1
  initial_measurable := p.initial_measurable.prodMk measurable_const
  point_measurable := p.expandedPoint_measurable b
  output_measurable := p.output_measurable.comp measurable_fst
  think_measurable := p.expandedThink_measurable b
  ordinaryNext_measurable := p.expandedOrdinary_measurable r
  richNext_measurable := fun _ => measurable_fst

theorem Program.expandedKind_ne_rich (p : Program Seed W X Y Z) (r k : ℕ) : p.expandedKind r k≠2 := by
  unfold expandedKind
  split_ifs <;> simp_all

theorem Program.expand_rich_count (p : Program Seed W X Y Z) (b : Batch X Y Z r) :
    (p.expand b).count 2=0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [expand,expandedKind_ne_rich,if_false]

def Program.segment (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z) (k : ℕ) : ℕ → W → W
  | 0 => id
  | n+1 => fun w => p.advance ordinary rich (k+n) (p.segment ordinary rich k n w)

theorem Program.evaluate_add (p : Program Seed W X Y Z) (ordinary : X → Y) (rich : X → Z)
    (k n : ℕ) (seed : Seed) :
    p.evaluate ordinary rich (k+n) seed=p.segment ordinary rich k n (p.evaluate ordinary rich k seed) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change p.advance ordinary rich (k+n) (p.evaluate ordinary rich (k+n) seed)=_
    rw [ih]
    rfl

end GradientHessian.ClockedOracle
