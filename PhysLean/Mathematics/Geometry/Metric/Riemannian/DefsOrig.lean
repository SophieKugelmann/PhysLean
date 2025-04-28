/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.LinearAlgebra.QuadraticForm.Dual
import PhysLean.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Riemannian Metrics on Manifolds

/-!
This file introduces `RiemannianMetric`, a smooth positive‐definite specialization of
`PseudoRiemannianMetric` over ℝ.  It requires that each bilinear form `gₓ` satisfy
`gₓ(v,v) > 0` for nonzero tangent vectors `v`, and uses this to define the canonical
inner product, norm, and distance on each tangent space.  (TODO: assemble these
data into an `InnerProductSpace ℝ (TangentSpace I_ℝ x)` instance).
-/

## Main Definitions

*   `RiemannianMetric I n M`: A structure representing a `C^n` Riemannian metric on a manifold `M`
    modelled on `(E_ℝ, H_ℝ)` with model `I_ℝ`. This specializes `PseudoRiemannianMetric` to the
    case where the base field is `ℝ` and requires the bilinear form `gₓ` at each point `x` to be
    positive-definite.
*   `RiemannianMetric.inner g x`: The inner product (bilinear form `gₓ`) on the tangent space `TₓM`.
*   `RiemannianMetric.sharp g x`: The musical isomorphism (index raising) from the cotangent space
    `T*ₓM` to the tangent space `TₓM`, which is an isomorphism in the Riemannian case due to
    positive definiteness.
*   `RiemannianMetric.toQuadraticForm g x`: Expresses the metric at point `x` as a quadratic form.

## Implementation Notes

*   Extends `PseudoRiemannianMetric` by fixing the base field to `ℝ` and adding the `pos_def'`
    field, ensuring `gₓ(v, v) > 0` for non-zero `v`.
*   The positive definiteness allows defining an `InnerProductSpace ℝ (TₓM)` instance on each
    tangent space `TₓM`.
-/
universe u v w

open PseudoRiemannianMetric Bundle ContinuousLinearMap

noncomputable section

variable {E_ℝ : Type v} [NormedAddCommGroup E_ℝ] [NormedSpace ℝ E_ℝ] [FiniteDimensional ℝ E_ℝ]
variable {H_ℝ : Type w} [TopologicalSpace H_ℝ]
variable {M_ℝ : Type w} [TopologicalSpace M_ℝ] [ChartedSpace H_ℝ M_ℝ] [ChartedSpace H_ℝ E_ℝ]

/-- A Riemannian metric of smoothness class `n` on a manifold `M` over `ℝ`.
    This extends a pseudo-Riemannian metric with the positive definiteness condition. -/
@[ext]
structure RiemannianMetric
  (I_ℝ : ModelWithCorners ℝ E_ℝ H_ℝ)
  (n    : WithTop ℕ∞)
  [inst_top : TopologicalSpace (TangentBundle I_ℝ M_ℝ)]
  [inst_fib : FiberBundle      E_ℝ (TangentSpace I_ℝ : M_ℝ → Type _)]
  [inst_vec : VectorBundle    ℝ E_ℝ (TangentSpace I_ℝ : M_ℝ → Type _)]
  [inst_mani : IsManifold       I_ℝ (n + 1) M_ℝ]
  [inst_cmvb : ContMDiffVectorBundle n E_ℝ (TangentSpace I_ℝ : M_ℝ → Type _) I_ℝ]
  extends @PseudoRiemannianMetric ℝ Real.instRCLike E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib
    inst_vec inst_mani inst_cmvb where
  /-- `gₓ(v, v) > 0` for all nonzero `v`. -/
  pos_def' : ∀ x v, v ≠ 0 → val x v v > 0


namespace RiemannianMetric

-- Propagate instance assumptions
variable {I_ℝ : ModelWithCorners ℝ E_ℝ H_ℝ} {n : WithTop ℕ∞}
variable [inst_top : TopologicalSpace (TangentBundle I_ℝ M_ℝ)]
variable [inst_fib : FiberBundle E_ℝ (TangentSpace I_ℝ : M_ℝ → Type _)]
variable [inst_vec : VectorBundle ℝ E_ℝ (TangentSpace I_ℝ : M_ℝ → Type _)]
variable [inst_mani : IsManifold I_ℝ (n + 1) M_ℝ]
variable [inst_cmvb : ContMDiffVectorBundle n E_ℝ (TangentSpace I_ℝ : M_ℝ → Type _) I_ℝ]

/-- Coercion from RiemannianMetric to its underlying PseudoRiemannianMetric. -/
instance : Coe (@RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani
      inst_cmvb)
                (@PseudoRiemannianMetric ℝ Real.instRCLike E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top
         inst_fib inst_vec inst_mani inst_cmvb) where
  coe g := g.toPseudoRiemannianMetric

omit [FiniteDimensional ℝ E_ℝ] [ChartedSpace H_ℝ E_ℝ] in
@[simp] lemma pos_def (g : RiemannianMetric I_ℝ n) (x : M_ℝ) (v : TangentSpace I_ℝ x) (hv : v ≠ 0) :
  (g.toPseudoRiemannianMetric.val x v) v > 0 := g.pos_def' x v hv

/-- The inverse of the musical isomorphism (index raising), which is an isomorphism
    in the Riemannian case. This is well-defined because the metric is positive definite. -/
def sharp
    (g : (@RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani
      inst_cmvb)) (x : M_ℝ) :
    Module.Dual ℝ (TangentSpace I_ℝ x) ≃ₗ[ℝ] TangentSpace I_ℝ x :=
  let bilin := g.toPseudoRiemannianMetric.toBilinForm x
  have h_nondeg : bilin.Nondegenerate :=
    g.toPseudoRiemannianMetric.toBilinForm_nondegenerate x
  LinearEquiv.symm (bilin.toDual h_nondeg)

/-- Express a Riemannian metric at a point as a quadratic form. -/
abbrev toQuadraticForm
    (g : (@RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani
      inst_cmvb))
    (x : M_ℝ) :
    QuadraticForm ℝ (TangentSpace I_ℝ x) :=
  g.toPseudoRiemannianMetric.toQuadraticForm x

omit [FiniteDimensional ℝ E_ℝ] [ChartedSpace H_ℝ E_ℝ] in
/-- The quadratic form associated with a Riemannian metric is positive definite. -/
lemma toQuadraticForm_posDef (g : RiemannianMetric I_ℝ n) (x : M_ℝ) :
    (g.toQuadraticForm x).PosDef :=
  λ v hv => g.pos_def x v hv

omit [FiniteDimensional ℝ E_ℝ] [ChartedSpace H_ℝ E_ℝ] in
/-- The application of a Riemannian metric's quadratic form to a vector. -/
lemma toQuadraticForm_apply (g : RiemannianMetric I_ℝ n) (x : M_ℝ)
    (v : TangentSpace I_ℝ x) :
    g.toQuadraticForm x v = g.val x v v := by
  simp only [toQuadraticForm, PseudoRiemannianMetric.toQuadraticForm_apply]

omit [FiniteDimensional ℝ E_ℝ] [ChartedSpace H_ℝ E_ℝ] in
/-- A positive definite quadratic form is nondegenerate. -/
lemma posDef_to_nondegenerate [Invertible (2 : ℝ)]
    (g : RiemannianMetric I_ℝ n) (x : M_ℝ) :
    (QuadraticMap.associated (R := ℝ) (N := ℝ) (g.toQuadraticForm x)).Nondegenerate := by
  let Q := g.toQuadraticForm x
  let B := QuadraticMap.associated (R := ℝ) (N := ℝ) Q
  constructor
  · intro v h_all_zero_w
    specialize h_all_zero_w v
    have h_assoc_self : B v v = Q v :=
        QuadraticMap.associated_eq_self_apply ℝ Q v
    rw [h_assoc_self] at h_all_zero_w
    by_cases h_v_zero : v = 0
    · exact h_v_zero
    · have h_quad_pos : Q v > 0 := g.pos_def x v h_v_zero
      linarith [h_all_zero_w, h_quad_pos]
  · intro w h_all_zero_v
    specialize h_all_zero_v w
    have h_assoc_self : B w w = Q w :=
        QuadraticMap.associated_eq_self_apply ℝ Q w
    rw [h_assoc_self] at h_all_zero_v
    by_cases h_w_zero : w = 0
    · exact h_w_zero
    · have h_quad_pos : Q w > 0 := g.pos_def x w h_w_zero
      linarith [h_all_zero_v, h_quad_pos]

/-- The isometry between `(Q.prod <| -Q)` and `QuadraticForm.dualProd`,
    where `Q` is the quadratic form associated with the Riemannian metric at `x`. -/
abbrev toDualProdIso [Invertible (2 : ℝ)] (g : RiemannianMetric I_ℝ n) (x : M_ℝ) :
    ((g.toQuadraticForm x).prod <| -(g.toQuadraticForm x)) →qᵢ
    (QuadraticForm.dualProd ℝ (TangentSpace I_ℝ x)) :=
  QuadraticForm.toDualProd (g.toQuadraticForm x)

/-- The inner product on the tangent space at point `x` induced by the Riemannian metric `g`. -/
def inner
    (g : (@RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani
      inst_cmvb)) (x : M_ℝ) (v w : TangentSpace I_ℝ x) : ℝ :=
  g.toPseudoRiemannianMetric.val x v w

omit [FiniteDimensional ℝ E_ℝ] [ChartedSpace H_ℝ E_ℝ] in
@[simp] lemma inner_apply (g : RiemannianMetric I_ℝ n) (x : M_ℝ) (v w : TangentSpace I_ℝ x) :
  inner g x v w = g.val x v w := rfl

variable (g : @RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n _ _ _ _ _) (x : M_ℝ)

omit [FiniteDimensional ℝ E_ℝ] [ChartedSpace H_ℝ E_ℝ] in
/-- Pointwise symmetry of the inner product. -/
lemma inner_symm (v w : TangentSpace I_ℝ x) :
    g.inner x v w = g.inner x w v := by
  simp only [inner_apply]
  exact g.toPseudoRiemannianMetric.symm' x v w

/-- The inner product space core for the tangent space at a point, derived from the
Riemannian metric. -/
noncomputable def tangentInnerCore
  (g : @RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani inst_cmvb)
  (x : M_ℝ) :
  InnerProductSpace.Core ℝ (TangentSpace I_ℝ x) where
  inner := λ v w => g.inner x v w
  conj_symm := λ v w => by
    simp only [inner_apply, conj_trivial]
    exact g.toPseudoRiemannianMetric.symm' x w v
  nonneg_re := λ v => by
    simp only [inner_apply, RCLike.re_to_real]
    by_cases hv : v = 0
    · simp [hv, inner_apply, map_zero, zero_apply]
    · exact le_of_lt (g.pos_def x v hv)
  add_left := λ u v w => by
    simp only [inner_apply, map_add, add_apply]
  smul_left := λ r u v => by
    simp only [inner_apply, map_smul, smul_apply, conj_trivial]
    rfl
  definite := fun v (h_inner_zero : g.inner x v v = 0) => by
    by_contra h_v_ne_zero
    have h_pos : g.inner x v v > 0 := g.pos_def x v h_v_ne_zero
    linarith [h_inner_zero, h_pos]

/-! ### Inner product space structure. -/

/-- Normed additive commutative group structure on the tangent space at a point `x`,
derived from the Riemannian metric `g`. -/
noncomputable def TangentSpace.metricNormedAddCommGroup
  (g : @RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani inst_cmvb)
  (x : M_ℝ) :
  NormedAddCommGroup (TangentSpace I_ℝ x) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I_ℝ x) _ _ _ (tangentInnerCore g x)

/-- The pre-inner product space core for the tangent space at a point,
derived from the Riemannian metric. -/
noncomputable def tangentPreInnerCore
  (g : @RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani inst_cmvb)
  (x : M_ℝ) :
  PreInnerProductSpace.Core ℝ (TangentSpace I_ℝ x) where
  inner := λ v w => g.inner x v w
  conj_symm := λ v w => by
    simp only [inner_apply, conj_trivial]
    exact g.toPseudoRiemannianMetric.symm' x w v
  nonneg_re := λ v => by
    simp only [inner_apply, RCLike.re_to_real]
    by_cases hv : v = 0
    · simp [hv, inner_apply, map_zero, zero_apply]
    · exact le_of_lt (g.pos_def x v hv)
  add_left := λ u v w => by
    simp only [inner_apply, map_add, add_apply]
  smul_left := λ r u v => by
    simp only [inner_apply, map_smul, smul_apply, conj_trivial]
    rfl

/-- Each tangent space carries a seminormed add comm group structure derived from
the Riemannian metric -/
noncomputable def TangentSpace.metricSeminormedAddCommGroup
  (g : @RiemannianMetric E_ℝ _ _ H_ℝ _ M_ℝ _ _ I_ℝ n inst_top inst_fib inst_vec inst_mani inst_cmvb)
  (x : M_ℝ) :
  SeminormedAddCommGroup (TangentSpace I_ℝ x) :=
  (TangentSpace.metricNormedAddCommGroup g x).toSeminormedAddCommGroup
