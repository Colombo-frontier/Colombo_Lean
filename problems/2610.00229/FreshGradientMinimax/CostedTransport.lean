import FreshGradientMinimax.CostedComposition

/-! Exact transport of output and accumulated call count through a state
embedding. In particular this lets a continuous parameter remain frozen
through batching, state updates and adaptive sequences. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory
variable {X Y Z X' Y' Z' : Type*}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable [MeasurableSpace X'] [MeasurableSpace Y'] [MeasurableSpace Z']

def costedMap (f : X → Y) (z : X × ℕ) : Y × ℕ := (f z.1, z.2)

theorem costedMap_measurable {f : X → Y} (hf : Measurable f) : Measurable (costedMap f) :=
  (hf.comp measurable_fst).prodMk measurable_snd

theorem costed_transport_first (K : Kernel X (Y × ℕ)) (L : Kernel X' (Y' × ℕ))
    (f : X → X') (hf : Measurable f) (g : Y → Y') (hg : Measurable g)
    (h : L.comap f hf = K.map (costedMap g)) :
    (L.map Prod.fst).comap f hf = (K.map Prod.fst).map g := by
  rw [Kernel.comap_map_comm _ hf measurable_fst, h,
    ← Kernel.map_comp_right _ (costedMap_measurable hg) measurable_fst,
    ← Kernel.map_comp_right _ measurable_fst hg]
  rfl

theorem costedCarryKernel_transport (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (L : Kernel X' (Y' × ℕ)) [IsMarkovKernel L]
    (f : X → X') (hf : Measurable f) (g : Y → Y') (hg : Measurable g)
    (h : L.comap f hf = K.map (costedMap g)) :
    (costedCarryKernel L).comap (costedMap f) (costedMap_measurable hf) =
      (costedCarryKernel K).map (costedMap g) := by
  apply Kernel.ext
  intro x
  have hx := congrArg (fun M : Kernel X (Y' × ℕ) => M x.1) h
  dsimp only at hx
  rw [Kernel.comap_apply, Kernel.map_apply _ (costedMap_measurable hg)] at hx
  rw [Kernel.comap_apply, Kernel.map_apply _ (costedMap_measurable hg), costedCarryKernel,
    costedUpdateKernel_apply _ _ measurable_snd _ measurable_snd,
    costedCarryKernel, costedUpdateKernel_apply _ _ measurable_snd _ measurable_snd]
  simp only [Kernel.comap_apply, costedMap, hx]
  rw [Measure.map_map (measurable_fst.prodMk (measurable_const.add measurable_snd))
      (costedMap_measurable hg),
    Measure.map_map (costedMap_measurable hg)
      (measurable_fst.prodMk (measurable_const.add measurable_snd))]
  rfl

theorem costedCompose_transport (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (L : Kernel X' (Y' × ℕ)) [IsMarkovKernel L]
    (R : Kernel Y (Z × ℕ)) [IsMarkovKernel R]
    (T : Kernel Y' (Z' × ℕ)) [IsMarkovKernel T]
    (f : X → X') (hf : Measurable f) (g : Y → Y') (hg : Measurable g)
    (h : Z → Z') (hh : Measurable h)
    (hK : L.comap f hf = K.map (costedMap g))
    (hR : T.comap g hg = R.map (costedMap h)) :
    (costedCompose L T).comap f hf = (costedCompose K R).map (costedMap h) := by
  rw [costedCompose, ← Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc,
    Kernel.comp_deterministic_eq_comap, hK, Kernel.comp_map _ _ (costedMap_measurable hg),
    costedCarryKernel_transport R T g hg h hh hR, ← Kernel.map_comp, costedCompose]

theorem costedIterate_transport (K : Kernel X (X × ℕ)) [IsMarkovKernel K]
    (L : Kernel Y (Y × ℕ)) [IsMarkovKernel L]
    (f : X → Y) (hf : Measurable f)
    (h : L.comap f hf = K.map (costedMap f)) (n : ℕ) :
    (costedIterate L n).comap f hf = (costedIterate K n).map (costedMap f) := by
  induction n with
  | zero =>
    apply Kernel.ext
    intro x
    simp only [costedIterate, taggedKernel, Kernel.comap_apply,
      Kernel.map_apply _ (costedMap_measurable hf)]
    rw [Kernel.map_apply (f := fun y : Y => (y, (0 : ℕ))) _ (measurable_id.prodMk measurable_const),
      Kernel.map_apply (f := fun x : X => (x, (0 : ℕ))) _ (measurable_id.prodMk measurable_const)]
    simp only [Kernel.id_apply]
    rw [Measure.map_dirac (show Measurable (fun y : Y => (y, (0 : ℕ))) from measurable_id.prodMk measurable_const),
      Measure.map_dirac (show Measurable (fun x : X => (x, (0 : ℕ))) from measurable_id.prodMk measurable_const),
      Measure.map_dirac (costedMap_measurable hf)]
    rfl
  | succ n ih => exact costedCompose_transport _ _ _ _ f hf f hf f hf ih h

theorem costedUpdateKernel_transport (K : Kernel X (Y × ℕ)) [IsMarkovKernel K]
    (L : Kernel X' (Y' × ℕ)) [IsMarkovKernel L]
    (f : X → X') (hf : Measurable f) (g : Y → Y') (hg : Measurable g)
    (h : Z → Z') (hh : Measurable h)
    (u : X × Y → Z) (hu : Measurable u) (v : X' × Y' → Z') (hv : Measurable v)
    (hK : L.comap f hf = K.map (costedMap g))
    (hupdate : ∀ x y, v (f x, g y) = h (u (x, y))) :
    (costedUpdateKernel L v (fun _ => 0)).comap f hf =
      (costedUpdateKernel K u (fun _ => 0)).map (costedMap h) := by
  apply Kernel.ext
  intro x
  have hx := congrArg (fun M : Kernel X (Y' × ℕ) => M x) hK
  dsimp only at hx
  rw [Kernel.comap_apply, Kernel.map_apply _ (costedMap_measurable hg)] at hx
  rw [Kernel.comap_apply, costedUpdateKernel_apply _ _ hv _ measurable_const,
    Kernel.map_apply _ (costedMap_measurable hh), costedUpdateKernel_apply _ _ hu _ measurable_const, hx,
    Measure.map_map (g := fun t : Y' × ℕ => (v (f x, t.1), 0 + t.2))
      ((hv.comp (measurable_const.prodMk measurable_fst)).prodMk
      (measurable_const.add measurable_snd)) (costedMap_measurable hg),
    Measure.map_map (f := fun t : Y × ℕ => (u (x, t.1), 0 + t.2)) (costedMap_measurable hh)
      ((hu.comp (measurable_const.prodMk measurable_fst)).prodMk (measurable_const.add measurable_snd))]
  congr 1
  funext t
  simp only [Function.comp_def, costedMap, hupdate]

theorem costedSumKernel_comap {d : ℕ} (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K]
    (f : Y → X) (hf : Measurable f) (n : ℕ) :
    (costedSumKernel K n).comap f hf = costedSumKernel (K.comap f hf) n := by
  induction n with
  | zero => apply Kernel.ext; intro x; rfl
  | succ n ih => rw [costedSumKernel, Kernel.comap_map_comm _ hf costedAdd_measurable,
      Kernel.comap_prod _ _ hf, ih, costedSumKernel]

theorem costedBatchKernel_comap {d : ℕ} (K : Kernel X (Euclid d × ℕ)) [IsMarkovKernel K]
    (f : Y → X) (hf : Measurable f) (b : ℕ) :
    (costedBatchKernel K b).comap f hf = costedBatchKernel (K.comap f hf) b := by
  rw [costedBatchKernel, Kernel.comap_map_comm _ hf
    ((measurable_const.smul measurable_fst).prodMk measurable_snd), costedSumKernel_comap, costedBatchKernel]

end FreshGradientMinimax
