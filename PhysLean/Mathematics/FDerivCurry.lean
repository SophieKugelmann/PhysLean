/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Tomáš Skřivan, Joseph Tooby-Smith
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import PhysLean.Meta.TODO.Basic
/-!
# fderiv currying lemmas

Various lemmas related to fderiv on curried/uncurried functions.

-/
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

lemma fderiv_uncurry (f : X → Y → Z) (xy dxy : X × Y)
    (hf : DifferentiableAt 𝕜 (↿f) xy) :
    fderiv 𝕜 ↿f xy dxy
    =
    fderiv 𝕜 (f · xy.2) xy.1 dxy.1 + fderiv 𝕜 (f xy.1 ·) xy.2 dxy.2 := by
  have hx : (f · xy.2) = ↿f ∘ (fun x' => (x',xy.2)) := by rfl
  have hy : (f xy.1 ·) = ↿f ∘ (fun y' => (xy.1,y')) := by rfl
  rw [hx,hy]
  repeat rw [fderiv_comp (hg := by fun_prop) (hf := by fun_prop)]
  dsimp
  rw [← ContinuousLinearMap.map_add]
  congr
  repeat rw [DifferentiableAt.fderiv_prodMk (hf₁ := by fun_prop) (hf₂ := by fun_prop)]
  simp

lemma fderiv_curry_fst (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x,y)) (dx : X) :
    fderiv 𝕜 (fun x' => Function.curry f x' y) x dx = fderiv 𝕜 f (x,y) (dx, 0) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  simp only [Function.curry_apply, map_zero, add_zero]
  exact h

lemma fderiv_curry_snd (f : X × Y → Z) (x : X) (y : Y)
    (h : DifferentiableAt 𝕜 f (x,y)) (dy : Y) :
    fderiv 𝕜 (Function.curry f x) y dy = fderiv 𝕜 (f) (x,y) (0, dy) := by
  have h1 : f = ↿(Function.curry f) := by
    ext x
    rfl
  conv_rhs =>
    rw [h1]
  rw [fderiv_uncurry]
  simp
  rfl
  exact h

lemma fderiv_uncurry_clm_comp (f : X → Y → Z) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 ↿f
    =
    fun xy =>
      (fderiv 𝕜 (f · xy.2) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (f xy.1 ·) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) := by
  funext xy
  apply ContinuousLinearMap.ext
  intro dxy
  rw [fderiv_uncurry]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd']
  fun_prop

lemma fderiv_wrt_prod_clm_comp (f : X × Y → Z) (hf : Differentiable 𝕜 f) :
    fderiv 𝕜 f
    =
    fun xy =>
      (fderiv 𝕜 (fun x' => f (x',xy.2)) xy.1).comp (ContinuousLinearMap.fst 𝕜 X Y)
      +
      (fderiv 𝕜 (fun y' => f (xy.1,y')) xy.2).comp (ContinuousLinearMap.snd 𝕜 X Y) :=
  fderiv_uncurry_clm_comp (fun x y => f (x,y)) hf

lemma fderiv_curry_clm_apply (f : X → Y →L[𝕜] Z) (y : Y) (x dx : X) (h : Differentiable 𝕜 f) :
    fderiv 𝕜 f x dx y
    =
    fderiv 𝕜 (f · y) x dx := by
  rw [fderiv_clm_apply] <;> first | simp | fun_prop

TODO "AZ2QN" "Replace following helper lemmas with fun_prop after
    #24056 in Mathlib has gone through."

/-- Helper lemmas showing differentiability from ContDiff 𝕜 2 ↿f. -/
lemma ContDiff.two_differentiable (f : X → Y → Z) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (↿f) :=
  ContDiff.differentiable hf (by simp)

lemma ContDiff.uncurry (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    ContDiff 𝕜 2 (f x) := by
  have h : f x = ↿f ∘ (x, ·) := by rfl
  rw [h]
  apply ContDiff.comp
  · exact hf
  · exact contDiff_prodMk_right x

lemma ContDiff.two_fderiv_differentiable (f : X → Y → Z) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 (↿f)) := by
  change ContDiff 𝕜 (1 + 1) ↿f at hf
  rw [contDiff_succ_iff_fderiv] at hf
  have hd2 := hf.2.2
  apply ContDiff.differentiable hd2
  rfl

/- Helper rw lemmas for proving differentiablity conditions. -/
lemma fderiv_uncurry_comp_fst (f : X → Y → Z) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 (fun x' => (↿f) (x', y))
    =
    fun x => (fderiv 𝕜 (↿f) ((·, y) x)).comp (fderiv 𝕜 (·, y) x) := by
  have hl (y : Y) : (fun x' => (↿f) (x', y)) = ↿f ∘ (·, y) := by
    rfl
  rw [hl]
  funext x
  rw [fderiv_comp]
  · fun_prop
  · fun_prop

lemma fderiv_uncurry_comp_snd (f : X → Y → Z) (x : X) (hf : Differentiable 𝕜 (↿f)) :
    fderiv 𝕜 (fun y' => (↿f) (x, y'))
    =
    fun y => (fderiv 𝕜 (↿f) ((x, ·) y)).comp (fderiv 𝕜 (x, ·) y) := by
  have hl (x : X) : (fun y' => (↿f) (x, y')) = ↿f ∘ (x, ·) := by
    rfl
  rw [hl]
  funext y
  rw [fderiv_comp]
  · fun_prop
  · fun_prop

lemma fderiv_curry_comp_fst (f : X → Y → Z) (x dx : X) (y : Y)
    (hf : Differentiable 𝕜 (↿f)) :
    (fderiv 𝕜 (fun x' => f x' y) x) dx
    =
    (fderiv 𝕜 (↿f) ((·, y) x)) ((fderiv 𝕜 (·, y) x) dx) := by
  have hl (y : Y) : (fun x' => f x' y) = ↿f ∘ (·, y) := by
    rfl
  rw [hl]
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · fun_prop
  · fun_prop

lemma fderiv_curry_comp_snd (f : X → Y → Z) (x : X) (y dy : Y)
    (hf : Differentiable 𝕜 (↿f)) :
    (fderiv 𝕜 (fun y' => f x y') y) dy
    =
    (fderiv 𝕜 (↿f) ((x, ·) y)) ((fderiv 𝕜 (x, ·) y) dy) := by
  have hl (x : X) : (fun y' => f x y') = ↿f ∘ (x, ·) := by
    rfl
  rw [hl]
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  · fun_prop
  · fun_prop

lemma fderiv_inr_fst_clm (x : X) (y : Y) :
    (fderiv 𝕜 (x, ·) y) = ContinuousLinearMap.inr 𝕜 X Y := by
  rw [(hasFDerivAt_prodMk_right x y).fderiv]

lemma fderiv_inl_snd_clm (x : X) (y : Y) :
    (fderiv 𝕜 (·, y) x) = ContinuousLinearMap.inl 𝕜 X Y := by
  rw [(hasFDerivAt_prodMk_left x y).fderiv]

/- Differentiablity conditions. -/
lemma function_differentiableAt_fst (f : X → Y → Z) (x : X) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    DifferentiableAt 𝕜 (fun x' => f x' y) x := by
  have hl : (fun x' => f x' y) = ↿f ∘ (·, y) := by
    funext x'
    rfl
  rw [hl]
  apply Differentiable.differentiableAt
  apply Differentiable.comp
  · fun_prop
  · fun_prop

lemma function_differentiableAt_snd (f : X → Y → Z) (x : X) (y : Y) (hf : Differentiable 𝕜 (↿f)) :
    DifferentiableAt 𝕜 (fun y' => f x y') y := by
  have hl : (fun y' => f x y') = ↿f ∘ (x, ·) := by
    funext y'
    rfl
  rw [hl]
  apply Differentiable.differentiableAt
  apply Differentiable.comp
  · fun_prop
  · fun_prop

lemma fderiv_uncurry_differentiable_fst (f : X → Y → Z) (y : Y) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 fun x' => (↿f) (x', y)) := by
  conv_rhs =>
    ext x
    rw [fderiv_uncurry_comp_fst (hf := hf.two_differentiable)]
  apply Differentiable.clm_comp
  · apply Differentiable.comp
    · exact hf.two_fderiv_differentiable
    · fun_prop
  · conv_rhs =>
      enter [x]
      rw [fderiv_inl_snd_clm]
    fun_prop

lemma fderiv_uncurry_differentiable_snd (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fderiv 𝕜 fun y' => (↿f) (x, y')) := by
  conv_rhs =>
    ext y
    rw [fderiv_uncurry_comp_snd (hf := hf.two_differentiable)]
  apply Differentiable.clm_comp
  · apply Differentiable.comp
    · exact hf.two_fderiv_differentiable
    · fun_prop
  · conv_rhs =>
      enter [y]
      rw [fderiv_inr_fst_clm]
    fun_prop

lemma fderiv_uncurry_differentiable_fst_comp_snd (f : X → Y → Z) (x : X) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun y' => fderiv 𝕜 (fun x' => (↿f) (x', y')) x) := by
  conv_rhs =>
    enter [y']
    rw [fderiv_uncurry_comp_fst (hf := hf.two_differentiable)]
  apply Differentiable.clm_comp
  · apply Differentiable.comp
    · exact hf.two_fderiv_differentiable
    · fun_prop
  · conv_rhs =>
      enter [y]
      rw [fderiv_inl_snd_clm]
    fun_prop

lemma fderiv_uncurry_differentiable_snd_comp_fst (f : X → Y → Z) (y : Y) (hf : ContDiff 𝕜 2 ↿f) :
    Differentiable 𝕜 (fun x' => fderiv 𝕜 (fun y' => (↿f) (x', y')) y) := by
  conv_rhs =>
    enter [x']
    rw [fderiv_uncurry_comp_snd (hf := hf.two_differentiable)]
  apply Differentiable.clm_comp
  · apply Differentiable.comp
    · exact hf.two_fderiv_differentiable
    · fun_prop
  · conv_rhs =>
      enter [x]
      rw [fderiv_inr_fst_clm]
    fun_prop

lemma fderiv_curry_differentiableAt_fst_comp_snd (f : X → Y → Z) (x dx : X) (y : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    DifferentiableAt 𝕜 (fun y' => (fderiv 𝕜 (fun x' => f x' y') x) dx) y := by
  conv_lhs =>
    enter [x']
    rw [fderiv_curry_comp_fst (hf := hf.two_differentiable)]
  refine DifferentiableAt.clm_apply ?_ ?_
  · simp
    refine DifferentiableAt.comp y ?_ ?_
    · apply Differentiable.differentiableAt
      exact hf.two_fderiv_differentiable
    · fun_prop
  · conv_lhs =>
      enter [x']
      rw [fderiv_inl_snd_clm]
    fun_prop

lemma fderiv_curry_differentiableAt_snd_comp_fst (f : X → Y → Z) (x : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    DifferentiableAt 𝕜 (fun x' => (fderiv 𝕜 (fun y' => f x' y') y) dy) x := by
  conv_lhs =>
    enter [x']
    rw [fderiv_curry_comp_snd (hf := hf.two_differentiable)]
  refine DifferentiableAt.clm_apply ?_ ?_
  · simp
    refine DifferentiableAt.comp x ?_ ?_
    · apply Differentiable.differentiableAt
      exact hf.two_fderiv_differentiable
    · fun_prop
  · conv_lhs =>
      enter [x']
      rw [fderiv_inr_fst_clm]
    fun_prop

/- fderiv commutes on X × Y. -/
lemma fderiv_swap [IsRCLikeNormedField 𝕜] (f : X → Y → Z) (x dx : X) (y dy : Y)
    (hf : ContDiff 𝕜 2 ↿f) :
    fderiv 𝕜 (fun x' => fderiv 𝕜 (fun y' => f x' y') y dy) x dx
    =
    fderiv 𝕜 (fun y' => fderiv 𝕜 (fun x' => f x' y') x dx) y dy := by
  have hf' : IsSymmSndFDerivAt 𝕜 (↿f) (x,y) := by
    apply ContDiffAt.isSymmSndFDerivAt (n := 2)
    · exact ContDiff.contDiffAt hf
    · simp
  have h := IsSymmSndFDerivAt.eq hf' (dx,0) (0,dy)
  rw [fderiv_wrt_prod_clm_comp, fderiv_wrt_prod_clm_comp] at h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_fst', Function.comp_apply, ContinuousLinearMap.coe_snd', map_zero,
    add_zero, zero_add] at h
  rw [fderiv_curry_clm_apply, fderiv_curry_clm_apply] at h
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
    ContinuousLinearMap.coe_fst', Function.comp_apply, map_zero, ContinuousLinearMap.coe_snd',
    zero_add, add_zero] at h
  exact h
  /- Start of differentiablity conditions. -/
  · refine Differentiable.add ?_ ?_
    · refine Differentiable.clm_comp ?_ ?_
      · apply fderiv_uncurry_differentiable_fst_comp_snd
        exact hf
      · fun_prop
    · refine Differentiable.clm_comp ?_ ?_
      · apply fderiv_uncurry_differentiable_snd
        exact hf
      · fun_prop
  · refine Differentiable.add ?_ ?_
    · refine Differentiable.clm_comp ?_ ?_
      · apply fderiv_uncurry_differentiable_fst
        exact hf
      · fun_prop
    · refine Differentiable.clm_comp ?_ ?_
      · apply fderiv_uncurry_differentiable_snd_comp_fst
        exact hf
      · fun_prop
  · exact hf.two_differentiable
  · exact hf.two_fderiv_differentiable
