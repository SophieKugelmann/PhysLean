/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import PhysLean.SpaceAndTime.Space.VectorIdentities
import PhysLean.SpaceAndTime.Time.Basic
import PhysLean.Mathematics.Distribution.Function.OfFunction
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
/-!

# Distributions on Space

In this module we define the derivatives, gradient, divergence and curl of distributions
on `Space`.

Contrary to the usual definition of derivatives on functions, when working with
distributions one does not need to check that the function is differentiable to perform
basic operations. This has the consequence that in a lot of cases, distributions are in fact
somewhat easier to work with than functions.

## Examples of distributions

Distributions cover a wide range of objects that we use in physics.

- The dirac delta function.
- The potential 1/r (which is not defined at the origin).
- The Heaviside step function.
- Interfaces between materials, such as a charged sphere.

-/

namespace Space

open Distribution
open SchwartzMap

/-!

## The constant distribution on space

-/

/-- The constant distribution from `Space d` to a module `M` associated with
  `m : M`. -/
noncomputable def constD {M } [NormedAddCommGroup M] [NormedSpace ℝ M] (d : ℕ) (m : M) :
    (Space d) →d[ℝ] M := const ℝ (Space d) m

/-!

## Derivatives

-/

/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def derivD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) : ((Space d) →d[ℝ] M) →ₗ[ℝ] (Space d) →d[ℝ] M where
  toFun f :=
    let ev : (Space d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (basis μ)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma schwartMap_fderiv_comm { d}
    (μ ν : Fin d) (x : Space d) (η : 𝓢(Space d, ℝ)) :
    ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis μ))
      ((fderivCLM ℝ) ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis ν)) ((fderivCLM ℝ) η)))) x =
    ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis ν))
      ((fderivCLM ℝ) ((SchwartzMap.evalCLM (𝕜 := ℝ) (basis μ)) ((fderivCLM ℝ) η)))) x := by
  have h1 := η.smooth
  have h2 := h1 2
  change fderiv ℝ (fun x => fderiv ℝ η x (basis ν)) x (basis μ) =
    fderiv ℝ (fun x => fderiv ℝ η x (basis μ)) x (basis ν)
  rw [fderiv_clm_apply, fderiv_clm_apply]
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  rw [IsSymmSndFDerivAt.eq]
  apply ContDiffAt.isSymmSndFDerivAt (n := 2)
  · refine ContDiff.contDiffAt ?_
    exact h2
  · simp
  · fun_prop
  · exact differentiableAt_const (basis μ)
  · fun_prop
  · exact differentiableAt_const (basis ν)

lemma derivD_comm {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ ν : Fin d) (f : (Space d) →d[ℝ] M) :
    (derivD ν (derivD μ f)) = (derivD μ (derivD ν f)) := by
  ext η
  simp [derivD, Distribution.fderivD]
  congr 1
  ext x
  rw [schwartMap_fderiv_comm μ ν x η]

@[simp]
lemma derivD_constD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (m : M) :
    derivD μ (constD d m) = 0 := by
  ext η
  simp [derivD, constD]

lemma derivD_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (f : (Space d) →d[ℝ] M) (ε : 𝓢(Space d, ℝ)) :
    (derivD μ f) ε = fderivD ℝ f ε (basis μ) := by
  simp [derivD, Distribution.fderivD]

/-!

## The gradient

-/

open InnerProductSpace

/-- The gradient of a distribution `(Space d) →d[ℝ] ℝ` as a distribution
  `(Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))`. -/
noncomputable def gradD {d} :
    ((Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d)) where
  toFun f :=
    ((InnerProductSpace.toDual ℝ (Space d)).symm.toContinuousLinearMap).comp (fderivD ℝ f)
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

lemma gradD_inner_eq {d} (f : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ))
    (y : EuclideanSpace ℝ (Fin d)) : ⟪gradD f η, y⟫_ℝ = fderivD ℝ f η y := by
  rw [gradD]
  simp only [LinearIsometryEquiv.toLinearEquiv_symm, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.coe_comp', LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_symm_toLinearEquiv, Function.comp_apply, toDual_symm_apply]

lemma gradD_eq_of_inner {d} (f : (Space d) →d[ℝ] ℝ) (g : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d))
    (h : ∀ η y, fderivD ℝ f η y = ⟪g η, y⟫_ℝ) :
    gradD f = g := by
  ext1 η
  specialize h η
  conv at h => enter [x]; rw [← gradD_inner_eq]
  exact ext_inner_right (𝕜 := ℝ) h

lemma gradD_eq_sum_basis {d} (f : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ)) :
    gradD f η = ∑ i, - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis i) (fderivCLM ℝ η)) • basis i := by
  have h1 (y : EuclideanSpace ℝ (Fin d)) :
      ⟪∑ i, - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis i) (fderivCLM ℝ η)) • basis i, y⟫_ℝ =
      fderivD ℝ f η y := by
    have hy : y = ∑ i, y i • basis i := by
      conv_lhs => rw [← OrthonormalBasis.sum_repr basis y]
      dsimp [basis]
    rw [hy]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, map_sum, map_smul, smul_eq_mul]
    conv_lhs =>
      enter [2, x]
      rw [Fintype.sum_apply, Fintype.sum_apply]
    simp only [PiLp.smul_apply, basis_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_neg]
    congr
    ext i
    rw [fderivD_apply]
    ring
  have hx (y : EuclideanSpace ℝ (Fin d)) : ⟪gradD f η, y⟫_ℝ =
      ⟪∑ i, - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis i) (fderivCLM ℝ η)) • basis i, y⟫_ℝ := by
    rw [gradD_inner_eq, h1]
  have h1 : ∀ y, ⟪gradD f η -
    (∑ i, - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis i) (fderivCLM ℝ η)) • basis i), y⟫_ℝ = 0 := by
    intro y
    rw [inner_sub_left, hx y]
    simp
  have h2 := h1 (gradD f η -
    (∑ i, - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis i) (fderivCLM ℝ η)) • basis i))
  rw [inner_self_eq_zero, sub_eq_zero] at h2
  rw [h2]

@[simp]
lemma gradD_constD {d} (m : ℝ) :
    gradD (constD d m) = 0 := by
  ext η
  simp [gradD, constD]

lemma gradD_toFun_eq_derivD {d} (f : (Space d) →d[ℝ] ℝ) :
    (gradD f).toFun = fun ε i => derivD i f ε := by
  ext ε i
  simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, ContinuousLinearMap.coe_coe]
  rw [gradD_eq_sum_basis]
  simp only [neg_smul, sum_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    Finset.sum_neg_distrib]
  rw [Finset.sum_eq_single i]
  · simp
    rfl
  · intro b _ h
    simp only [mul_eq_zero]
    right
    simpa [basis_apply] using h
  · simp

lemma gradD_apply {d} (f : (Space d) →d[ℝ] ℝ) (ε : 𝓢(Space d, ℝ)) :
    (gradD f) ε = fun i => derivD i f ε := by
  change (gradD f).toFun ε = fun i => derivD i f ε
  rw [gradD_toFun_eq_derivD]

/-!

## The divergence

-/

/-- The divergence of a distribution `(Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))` as a distribution
  `(Space d) →d[ℝ] ℝ`. -/
noncomputable def divD {d} :
    ((Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] (Space d) →d[ℝ] ℝ where
  toFun f :=
    let trace : (Space d →L[ℝ] (EuclideanSpace ℝ (Fin d))) →L[ℝ] ℝ := {
      toFun v := ∑ i, ⟪v (basis i), basis i⟫_ℝ
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply, inner_basis, PiLp.add_apply]
        rw [Finset.sum_add_distrib]
      map_smul' a v := by
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, inner_basis, PiLp.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
      cont := by fun_prop}
    trace.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

lemma divD_apply_eq_sum_fderivD {d}
    (f : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) (η : 𝓢(Space d, ℝ)) :
    divD f η = ∑ i, fderivD ℝ f η (basis i) i := by
  simp [divD]

lemma divD_apply_eq_sum_derivD {d}
    (f : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) (η : 𝓢(Space d, ℝ)) :
    divD f η = ∑ i, derivD i f η i := by
  rw [divD_apply_eq_sum_fderivD]
  rfl

@[simp]
lemma divD_constD {d} (m : EuclideanSpace ℝ (Fin d)) :
    divD (constD d m) = 0 := by
  ext η
  simp [divD, constD]

open MeasureTheory
open SchwartzMap

/-- The divergence of a distribution from a bounded function. -/
lemma divD_ofFunction {dm1 : ℕ} {f : Space dm1.succ → EuclideanSpace ℝ (Fin dm1.succ)}
    {hf : IsDistBounded f}
    {hae: AEStronglyMeasurable (fun x => f x) volume} (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    divD (Distribution.ofFunction f hf hae) η =
    - ∫ x : Space dm1.succ, ⟪f x, Space.grad η x⟫_ℝ := by
  rw [divD_apply_eq_sum_fderivD]
  conv_rhs =>
    enter [1, 2, x]
    rw [grad_eq_sum, inner_sum]
  conv_lhs =>
    enter [2, i]
    rw [fderivD_apply, ofFunction_apply]
  /- The following lemma could probably be moved out of this result. -/
  have integrable_lemma (i j : Fin (dm1 + 1)) :
      Integrable (fun x =>
        (((SchwartzMap.evalCLM (𝕜 := ℝ) (basis i)) ((fderivCLM ℝ) η)) x • f x) j) volume := by
    simp only [PiLp.smul_apply]
    apply IsDistBounded.schwartzMap_smul_integrable
    · exact IsDistBounded.pi_comp hf j
    · fun_prop
  rw [MeasureTheory.integral_finset_sum]
  · simp
    congr
    funext i
    rw [MeasureTheory.eval_integral_piLp]
    · congr
      funext x
      simp [inner_smul_right]
      left
      rw [deriv_eq_fderiv_basis]
      rfl
    · intro j
      exact integrable_lemma i j
  · intro i hi
    simp only [Nat.succ_eq_add_one, inner_smul_right, inner_basis]
    convert integrable_lemma i i
    rename_i x
    simp only [Nat.succ_eq_add_one, PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff]
    left
    rw [deriv_eq_fderiv_basis]
    rfl

/- The quantity `⟪f x, Space.grad η x⟫_ℝ` is integrable for `f` bounded
  and `η` a Schwartz map. -/
lemma integrable_isDistBounded_inner_grad_schwartzMap {dm1 : ℕ}
    {f : Space dm1.succ → EuclideanSpace ℝ (Fin dm1.succ)}
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    Integrable (fun x => ⟪f x, Space.grad η x⟫_ℝ) volume := by
  conv =>
    enter [1, x]
    rw [grad_eq_sum, inner_sum]
  apply MeasureTheory.integrable_finset_sum
  intro i _
  simp [inner_smul_right]
  have integrable_lemma (i j : Fin (dm1 + 1)) :
      Integrable (fun x => (((SchwartzMap.evalCLM (𝕜 := ℝ) (basis i)) ((fderivCLM ℝ) η)) x • f x) j)
        volume := by
    simp only [PiLp.smul_apply]
    apply IsDistBounded.schwartzMap_smul_integrable
    · exact IsDistBounded.pi_comp hf j
    · fun_prop
  convert integrable_lemma i i
  rename_i x
  simp only [Nat.succ_eq_add_one, PiLp.smul_apply, smul_eq_mul, mul_eq_mul_right_iff]
  left
  rw [deriv_eq_fderiv_basis]
  rfl

lemma integrable_isDistBounded_inner_grad_schwartzMap_spherical{dm1 : ℕ}
    {f : Space dm1.succ → EuclideanSpace ℝ (Fin dm1.succ)}
    (hf : IsDistBounded f)
    (hae: AEStronglyMeasurable (fun x => f x) volume) (η : 𝓢(EuclideanSpace ℝ (Fin dm1.succ), ℝ)) :
    Integrable ((fun x => ⟪f x.1, Space.grad η x.1⟫_ℝ)
      ∘ (homeomorphUnitSphereProd (Space dm1.succ)).symm)
      ((volume (α := Space dm1.succ)).toSphere.prod
      (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin dm1.succ)) - 1))) := by
  have h1 : Integrable ((fun x => ⟪f x.1, Space.grad η x.1⟫_ℝ))
      (.comap (Subtype.val (p := fun x => x ∈ ({0}ᶜ : Set _))) volume) := by
    change Integrable ((fun x => ⟪f x, Space.grad η x⟫_ℝ) ∘ Subtype.val)
      (.comap (Subtype.val (p := fun x => x ∈ ({0}ᶜ : Set _))) volume)
    rw [← MeasureTheory.integrableOn_iff_comap_subtypeVal]
    apply Integrable.integrableOn
    exact integrable_isDistBounded_inner_grad_schwartzMap hf hae η
    simp
  have he := (MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd
    (volume (α := EuclideanSpace ℝ (Fin dm1.succ))))
  rw [← he.integrable_comp_emb]
  convert h1
  simp only [Nat.succ_eq_add_one, Function.comp_apply, Homeomorph.symm_apply_apply]
  exact Homeomorph.measurableEmbedding (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin dm1.succ)))

/-!

## The curl

-/

/-- The curl of a distribution `Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))` as a distribution
  `Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))`. -/
noncomputable def curlD : (Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ]
    (Space) →d[ℝ] (EuclideanSpace ℝ (Fin 3)) where
  toFun f :=
    let curl : (Space →L[ℝ] (EuclideanSpace ℝ (Fin 3))) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) := {
      toFun dfdx:= fun i =>
        match i with
        | 0 => dfdx (basis 2) 1 - dfdx (basis 1) 2
        | 1 => dfdx (basis 0) 2 - dfdx (basis 2) 0
        | 2 => dfdx (basis 1) 0 - dfdx (basis 0) 1
      map_add' v1 v2 := by
        ext i
        fin_cases i
        all_goals
          simp only [Fin.isValue, ContinuousLinearMap.add_apply, PiLp.add_apply, Fin.zero_eta]
          ring
      map_smul' a v := by
        ext i
        fin_cases i
        all_goals
          simp only [Fin.isValue, ContinuousLinearMap.coe_smul', Pi.smul_apply, PiLp.smul_apply,
            smul_eq_mul, RingHom.id_apply, Fin.reduceFinMk]
          ring
      cont := by
        rw [continuous_pi_iff]
        intro i
        fin_cases i
        all_goals
          fun_prop
        }
    curl.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

lemma curlD_apply_zero (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    curlD f η 0 = - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 2) (fderivCLM ℝ η)) 1
    + f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 1) (fderivCLM ℝ η)) 2 := by
  simp [curlD]
  rw [fderivD_apply, fderivD_apply]
  simp

lemma curlD_apply_one (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    curlD f η 1 = - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0) (fderivCLM ℝ η)) 2
    + f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 2) (fderivCLM ℝ η)) 0 := by
  simp [curlD]
  rw [fderivD_apply, fderivD_apply]
  simp

lemma curlD_apply_two (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    curlD f η 2 = - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 1) (fderivCLM ℝ η)) 0
    + f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0) (fderivCLM ℝ η)) 1 := by
  simp [curlD]
  rw [fderivD_apply, fderivD_apply]
  simp

lemma curlD_apply (f : Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) (η : 𝓢(Space, ℝ)) :
    curlD f η = fun
    | 0 => - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 2) (fderivCLM ℝ η)) 1
      + f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 1) (fderivCLM ℝ η)) 2
    | 1 => - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0) (fderivCLM ℝ η)) 2
      + f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 2) (fderivCLM ℝ η)) 0
    | 2 => - f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 1) (fderivCLM ℝ η)) 0
      + f (SchwartzMap.evalCLM (𝕜 := ℝ) (basis 0) (fderivCLM ℝ η)) 1 := by
  funext i
  fin_cases i
  · simp [curlD_apply_zero]
  · simp [curlD_apply_one]
  · simp [curlD_apply_two]

@[simp]
lemma curlD_constD (m : EuclideanSpace ℝ (Fin 3)) :
    curlD (constD 3 m) = 0 := by
  ext η
  simp [curlD, constD]

/-!

## Vector identities

-/

/-- The curl of a grad is equal to zero. -/
@[simp]
lemma curlD_gradD_eq_zero (f : (Space) →d[ℝ] ℝ) :
    curlD (gradD f) = 0 := by
  ext η i
  fin_cases i
  all_goals
  · dsimp
    try rw [curlD_apply_zero]
    try rw [curlD_apply_one]
    try rw [curlD_apply_two]
    rw [gradD_eq_sum_basis, gradD_eq_sum_basis]
    simp [basis_apply]
    rw [← map_neg, ← map_add, ← ContinuousLinearMap.map_zero f]
    congr
    ext x
    simp only [Fin.isValue, add_apply, zero_apply]
    rw [schwartMap_fderiv_comm]
    change ((SchwartzMap.evalCLM (𝕜 := ℝ) _)
      ((fderivCLM ℝ) ((SchwartzMap.evalCLM (𝕜 := ℝ) _) ((fderivCLM ℝ) η)))) x +
      - ((SchwartzMap.evalCLM (𝕜 := ℝ) _)
        ((fderivCLM ℝ) ((SchwartzMap.evalCLM (𝕜 := ℝ) _) ((fderivCLM ℝ) η)))) x = _
    simp

/-!

## For time-dependent distributions

-/

/-- The time derivative of a distribution dependent on time and space. -/
noncomputable def timeDerivD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M] :
    ((Time × Space d) →d[ℝ] M) →ₗ[ℝ] (Time × Space d) →d[ℝ] M where
  toFun f :=
    let ev : ((Time × Space d) →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (1, 0)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma timeDerivD_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (timeDerivD f) ε = fderivD ℝ f ε (1, 0) := by
  simp [timeDerivD]

/-- The space derivative of a distribution dependent on time and space. -/
noncomputable def spaceDerivD {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) : ((Time × Space d) →d[ℝ] M) →ₗ[ℝ] (Time × Space d) →d[ℝ] M where
  toFun f :=
    let ev : (Time × Space d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (0, basis i)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    simp
  map_smul' a f := by simp

lemma spaceDerivD_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (i : Fin d) (f : (Time × Space d) →d[ℝ] M) (ε : 𝓢(Time × Space d, ℝ)) :
    (spaceDerivD i f) ε = fderivD ℝ f ε (0, basis i) := by
  simp [spaceDerivD]

/-- The spatial gradient of a distribution dependent on time and space. -/
noncomputable def spaceGradD {d} :
    ((Time × Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d)) where
  toFun f := {
      toFun := fun ε i => spaceDerivD i f ε
      map_add' ε1 ε2 := by funext i; simp
      map_smul' a ε := by funext i; simp
      cont := by fun_prop}
  map_add' f1 f2 := by
    ext x
    simp
  map_smul' a f := by
    ext x
    simp

lemma spaceGradD_apply {d} (f : (Time × Space d) →d[ℝ] ℝ) (ε : 𝓢(Time × Space d, ℝ)) :
    spaceGradD f ε = fun i => spaceDerivD i f ε := by
  rfl
/-- The spatial divergence of a distribution dependent on time and space. -/
noncomputable def spaceDivD {d} :
    ((Time × Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] (Time × Space d) →d[ℝ] ℝ where
  toFun f := {
    toFun ε := ∑ i, spaceDerivD i f ε i
    map_add' ε1 ε2 := by simp [Finset.sum_add_distrib]
    map_smul' a ε := by simp [Finset.mul_sum]
    cont := by fun_prop}
  map_add' f1 f2 := by
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' a f := by
    ext x
    simp [Finset.mul_sum]

lemma spaceDivD_apply_eq_sum_spaceDerivD {d}
    (f : (Time × Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) (η : 𝓢(Time ×Space d, ℝ)) :
    spaceDivD f η = ∑ i, spaceDerivD i f η i := by rfl

/-- The curl of a distribution dependent on time and space. -/
noncomputable def spaceCurlD : ((Time × Space 3) →d[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ]
    (Time × Space 3) →d[ℝ] (EuclideanSpace ℝ (Fin 3)) where
  toFun f :={
    toFun ε := fun i =>
      match i with
      | 0 => spaceDerivD 2 f ε 1 - spaceDerivD 1 f ε 2
      | 1 => spaceDerivD 0 f ε 2 - spaceDerivD 2 f ε 0
      | 2 => spaceDerivD 1 f ε 0 - spaceDerivD 0 f ε 1
    map_add' ε1 ε2 := by
      funext i
      fin_cases i
      all_goals
        simp only [Fin.isValue, map_add, PiLp.add_apply, Fin.reduceFinMk]
        ring
    map_smul' a ε := by
      funext i
      fin_cases i
      all_goals
        simp only [Fin.isValue, map_smul, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
          Fin.zero_eta]
        ring
    cont := by
      rw [continuous_pi_iff]
      intro i
      fin_cases i <;> fun_prop
      }
  map_add' f1 f2 := by
    ext x i
    fin_cases i
    all_goals
      simp only [Fin.isValue, map_add, ContinuousLinearMap.add_apply, PiLp.add_apply, Fin.zero_eta,
        ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      ring
  map_smul' a f := by
    ext x i
    fin_cases i
    all_goals
      simp only [Fin.isValue, map_smul, ContinuousLinearMap.coe_smul', Pi.smul_apply,
        PiLp.smul_apply, smul_eq_mul, Fin.reduceFinMk, ContinuousLinearMap.coe_mk',
        LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply]
      ring

end Space
