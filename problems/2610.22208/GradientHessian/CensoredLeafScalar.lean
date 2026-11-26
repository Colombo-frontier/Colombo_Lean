import GradientHessian.LeafJointOracle
import GradientHessian.MemoryMissJets

/-!
# An explicit censored leaf scalar

The frontier index is fixed before the normal operation. The mask records
which readout and memory blocks are available after that operation. All
earlier weighted terms remain; the current supplied forcing remains; every
future weighted forcing is omitted. Zero storage for unavailable b entries
does not stand in for omission of their nonzero forcing functions.
-/

noncomputable section
namespace GradientHessian.CensoredLeaf

open Classical InnerCoordinates JetLocality PartialJetCalculus
open scoped BigOperators InnerProductSpace

structure Mask (m : ℕ) where
  current : Fin m
  readout : Bool
  memory : Fin m → Bool

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

/-- A finite disclosed view. Unavailable entries are erased before evaluation. -/
def view (mask : Mask m) (θ : Leaf.Marks Y E m) : Leaf.Marks Y E m :=
  (fun i => if i≤mask.current then θ.1 i else 0,
   (fun i => if i<mask.current ∨ (i=mask.current ∧ mask.readout=true) then θ.2.1 i else 0),
   fun i => if mask.memory i then θ.2.2 i else 0)

omit [InnerProductSpace ℝ Y] [InnerProductSpace ℝ E] in
@[simp] theorem view_idempotent (mask : Mask m) (θ : Leaf.Marks Y E m) :
    view mask (view mask θ)=view mask θ := by
  apply Prod.ext
  · funext i; by_cases hi : i≤mask.current <;> simp [view,hi]
  · apply Prod.ext
    · funext i; by_cases hi : i<mask.current ∨ (i=mask.current ∧ mask.readout=true) <;> simp [view,hi]
    · funext i; cases hi : mask.memory i <;> simp [view,hi]

omit [InnerProductSpace ℝ Y] [InnerProductSpace ℝ E] in
theorem view_congr (mask : Mask m) (θ η : Leaf.Marks Y E m)
    (hb : ∀ i,i≤mask.current → θ.1 i=η.1 i)
    (ha : ∀ i,i<mask.current ∨ (i=mask.current ∧ mask.readout=true) → θ.2.1 i=η.2.1 i)
    (hv : ∀ i,mask.memory i=true → θ.2.2 i=η.2.2 i) : view mask θ=view mask η := by
  apply Prod.ext
  · funext i; by_cases hi : i≤mask.current <;> simp [view,hi,hb i]
  · apply Prod.ext
    · funext i; by_cases hi : i<mask.current ∨ (i=mask.current ∧ mask.readout=true) <;> simp [view,hi,ha i]
    · funext i; cases hi : mask.memory i <;> simp [view,hi,hv i]

theorem view_contDiff (mask : Mask m) : ContDiff ℝ 3 (view mask : Leaf.Marks Y E m → Leaf.Marks Y E m) := by
  refine ContDiff.prodMk ?_ (ContDiff.prodMk ?_ ?_)
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ 3 (fun θ : Leaf.Marks Y E m => if i≤mask.current then θ.1 i else 0)
    split_ifs <;> fun_prop
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ 3 (fun θ : Leaf.Marks Y E m =>
      if i<mask.current ∨ (i=mask.current ∧ mask.readout=true) then θ.2.1 i else 0)
    split_ifs <;> fun_prop
  · apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ 3 (fun θ : Leaf.Marks Y E m => if mask.memory i then θ.2.2 i else 0)
    split_ifs <;> fun_prop

def prefixWeight (p : Fin m → ℝ) (k : Fin m) : ℝ := ∏ j,if j<k then p j else 1

def currentPayload (mask : Mask m) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) : ℝ :=
  if mask.readout then Inner.payload θ.1 θ.2.1 θ.2.2 Z mask.current
  else InverseGate.forcing (θ.1 mask.current) (numerical Y E m (Inner.absoluteDepth+2) Z)

def coreKnownTerm (mask : Mask m) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) : ℝ :=
  Inner.selfSum θ.2.2 Z -
    ((∑ i,if i<mask.current then InnerSelector.weight (Inner.ports θ.2.2 Z) i *
      Inner.payload θ.1 θ.2.1 θ.2.2 Z i else 0) +
      prefixWeight (Inner.ports θ.2.2 Z) mask.current * currentPayload mask θ Z)

def knownTerm (mask : Mask m) (θ : Leaf.Marks Y E m) : Leaf.Space Y E m → ℝ :=
  coreKnownTerm mask (view mask θ)

def objective (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) : ℝ :=
  LeafNumerical.base m (Leaf.capRadius m) A (numerical Y E m (Inner.absoluteDepth+2) Z) + knownTerm mask θ Z

@[simp] theorem knownTerm_view (mask : Mask m) (θ : Leaf.Marks Y E m) :
    knownTerm mask (view mask θ)=knownTerm mask θ := by simp only [knownTerm,view_idempotent]

@[simp] theorem objective_view (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m) :
    objective mask A (view mask θ)=objective mask A θ := by funext Z; simp [objective]

theorem knownTerm_erasure (mask : Mask m) {θ η : Leaf.Marks Y E m} (he : view mask θ=view mask η) :
    knownTerm mask θ=knownTerm mask η := by rw [knownTerm,knownTerm,he]

theorem objective_erasure (mask : Mask m) (A : Y →L[ℝ] Y) {θ η : Leaf.Marks Y E m}
    (he : view mask θ=view mask η) : objective mask A θ=objective mask A η := by
  funext Z
  rw [objective,objective,knownTerm_erasure mask he]

def coreKnownJoint (mask : Mask m) (p : Leaf.Marks Y E m × Leaf.Space Y E m) : ℝ :=
  coreKnownTerm mask p.1 p.2

theorem coreKnownJoint_contDiff (mask : Mask m) :
    ContDiff ℝ 3 (coreKnownJoint (Y := Y) (E := E) mask) := by
  let F := Leaf.Marks Y E m × Leaf.Space Y E m
  have hb (i : Fin m) : ContDiff ℝ 3 (fun p : F => p.1.1 i) := by fun_prop
  have ha (i : Fin m) : ContDiff ℝ 3 (fun p : F => p.1.2.1 i) := by fun_prop
  have hv (i : Fin m) (j : Fin (Inner.absoluteDepth+2)) : ContDiff ℝ 3 (fun p : F => p.1.2.2 i j) := by fun_prop
  have hp (i : Fin m) := JointMarkedCalculus.ports_contDiff hv (contDiff_snd : ContDiff ℝ 3 (Prod.snd : F → _)) i
  have hprefix (k : Fin m) : ContDiff ℝ 3 (fun p : F => prefixWeight (Inner.ports p.1.2.2 p.2) k) := by
    apply contDiff_prod
    intro i _
    by_cases hi : i<k
    · simpa [hi] using hp i
    · simp only [if_neg hi]; exact contDiff_const
  have hweight (i : Fin m) : ContDiff ℝ 3 (fun p : F => InnerSelector.weight (Inner.ports p.1.2.2 p.2) i) :=
    (contDiff_const.sub (hp i)).mul (hprefix i)
  have hpay (i : Fin m) := JointMarkedCalculus.payload_contDiff hb ha hv (contDiff_snd : ContDiff ℝ 3 (Prod.snd : F → _)) i
  have hcur : ContDiff ℝ 3 (fun p : F => currentPayload mask p.1 p.2) := by
    cases hg : mask.readout with
    | true => simpa [currentPayload,hg] using hpay mask.current
    | false =>
      simpa [currentPayload,hg] using JointMarkedCalculus.forcing_contDiff (hb mask.current)
        ((numerical Y E m (Inner.absoluteDepth+2)).contDiff.comp (contDiff_snd : ContDiff ℝ 3 (Prod.snd : F → _)))
  exact (JointMarkedCalculus.selfSum_contDiff hv contDiff_snd).sub
    ((ContDiff.sum (fun i _ => by
      by_cases hi : i<mask.current
      · simpa [hi] using (hweight i).mul (hpay i)
      · simp only [if_neg hi]; exact contDiff_const)).add ((hprefix mask.current).mul hcur))

def knownJoint (mask : Mask m) (p : Leaf.Marks Y E m × Leaf.Space Y E m) : ℝ :=
  knownTerm mask p.1 p.2

theorem knownJoint_contDiff (mask : Mask m) : ContDiff ℝ 3 (knownJoint (Y := Y) (E := E) mask) := by
  have he : knownJoint (Y := Y) (E := E) mask = coreKnownJoint mask ∘
      (fun p : Leaf.Marks Y E m × Leaf.Space Y E m => (view mask p.1,p.2)) := rfl
  rw [he]
  exact (coreKnownJoint_contDiff (Y := Y) (E := E) mask).comp
    (((view_contDiff (Y := Y) (E := E) mask).comp contDiff_fst).prodMk contDiff_snd)

theorem knownTerm_contDiff (mask : Mask m) (θ : Leaf.Marks Y E m) : ContDiff ℝ 3 (knownTerm mask θ) := by
  have he : knownTerm mask θ = knownJoint mask ∘ (fun Z : Leaf.Space Y E m => (θ,Z)) := rfl
  rw [he]
  exact (knownJoint_contDiff (Y := Y) (E := E) mask).comp (contDiff_const.prodMk contDiff_id)

theorem objective_contDiff (hm : 1≤m) (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m) :
    ContDiff ℝ 3 (objective mask A θ) := by
  have he : objective mask A θ = fun Z =>
      Leaf.objective A θ.1 θ.2.1 θ.2.2 Z - Leaf.knownTerm θ.1 θ.2.1 θ.2.2 Z + knownTerm mask θ Z := by
    funext Z
    rw [Leaf.objective_decomposition]
    unfold objective Leaf.knownTerm
    ring
  rw [he]
  exact ((Leaf.objective_contDiff hm A θ.1 θ.2.1 θ.2.2).sub
    (Leaf.knownTerm_contDiff θ.1 θ.2.1 θ.2.2)).add (knownTerm_contDiff mask θ)

def objectiveJoint (mask : Mask m) (p : Leaf.MatrixMarks Y E m × Leaf.Space Y E m) : ℝ :=
  objective mask p.1.1 p.1.2 p.2

theorem objectiveJoint_contDiff (hm : 1≤m) (mask : Mask m) :
    ContDiff ℝ 3 (objectiveJoint (Y := Y) (E := E) mask) := by
  have he : objectiveJoint (Y := Y) (E := E) mask = fun p =>
      Leaf.objectiveJoint p - Leaf.knownTermJoint (p.1.2,p.2) + knownJoint mask (p.1.2,p.2) := by
    funext p
    simp only [objectiveJoint,objective,Leaf.objectiveJoint,Leaf.objective_decomposition,
      Leaf.knownTermJoint,Leaf.knownTerm,knownJoint]
    ring
  rw [he]
  exact ((Leaf.objective_joint_contDiff hm).sub
    (Leaf.knownTerm_joint_contDiff.comp (by fun_prop))).add
    ((knownJoint_contDiff mask).comp (by fun_prop))

end GradientHessian.CensoredLeaf
