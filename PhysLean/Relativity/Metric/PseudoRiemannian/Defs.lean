/- Lean 4 code -/
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Algebra.Module.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Topology.Connected.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Dual -- Needed for Module.Dual
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Topology.VectorBundle.Constructions -- Added for VectorBundle.dual
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic


--section PseudoRiemannianMetric

universe u v w

open Bundle Set Function Filter Module -- Added Module to open namespaces
open scoped Manifold Topology Bundle LinearMap.dualMap

abbrev contMDiff_linear {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) {n : ℕ∞} :
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n f :=
  f.contDiff.contMDiff

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type w} [TopologicalSpace H]
variable {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- A pseudo-Riemannian metric of smoothness class `n` on a manifold `M`.
    This structure separates the smoothness parameter from the context to allow
    composition of structures with different smoothness requirements. -/
@[ext]
structure PseudoRiemannianMetric
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type w} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M]
    [ChartedSpace H M] -- Removed [ChartedSpace H E] as it seemed incorrect
    (I : ModelWithCorners 𝕜 E H)
    (n : WithTop ℕ∞)
    -- Now list instances depending on I and n
    -- Ensure necessary instances for TangentBundle are available
    -- These instances are typically inferred when M is a manifold.
    [TopologicalSpace (TangentBundle I M)]
    [FiberBundle E (TangentSpace I : M → Type _)] -- Use explicit type family
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)] -- Use explicit type family
    -- Add IsManifold and ContMDiffVectorBundle constraints here
    -- Require IsManifold I (n + 1) M to ensure ContMDiffVectorBundle n can be inferred
    [IsManifold I (n + 1) M] -- Removed name h_manifold
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I] -- Removed name h_contMDiffVec
   : Type (max u v w) where
  /-- The metric as a function on tangent vectors, providing a bilinear form at each point. -/
  val : ∀ (x : M), LinearMap.BilinForm 𝕜 (TangentSpace I x)
  /-- The metric is symmetric: g(v,w) = g(w,v) for all tangent vectors v, w. -/
  symm : ∀ (x : M), (val x).IsSymm
  /-- The metric is non-degenerate: if g(v,w) = 0 for all w, then v = 0. -/
  nondegenerate : ∀ (x : M), (val x).Nondegenerate
  /-- The metric is smooth of class `n`: it varies smoothly across the manifold when applied to
      smooth vector fields. -/
  smooth : ∀ (X Y : Cₛ^n⟮I; E, (TangentSpace I : M → Type _)⟯), -- Use explicit type family
    ContMDiff I (modelWithCornersSelf 𝕜 𝕜) n (λ x => val x (X x) (Y x))

namespace PseudoRiemannianMetric

--variable [FiniteDimensional 𝕜 E]

-- Define the model fiber for bilinear forms
@[nolint unusedArguments]
abbrev ModelBilinForm (_𝕜 E : Type*) [NontriviallyNormedField _𝕜] [NormedAddCommGroup E] [NormedSpace _𝕜 E] : Type _ :=
  E →L[_𝕜] (E →L[_𝕜] _𝕜)

-- Define the bundle of continuous bilinear forms on the tangent bundle
-- The fiber at x is the space of continuous linear maps from TangentSpace I x to its continuous dual.
@[nolint unusedArguments]
def TangentBilinFormBundle (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type w} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners 𝕜 E H)
    -- Instances ensuring TangentSpace I x is a normed space and the bundle structure exists
    [TopologicalSpace (TangentBundle I M)]
    [FiberBundle E (TangentSpace I : M → Type _)]
    [VectorBundle 𝕜 E (TangentSpace I : M → Type _)] : M → Type _ :=
  fun x => TangentSpace I x →L[𝕜] (TangentSpace I x →L[𝕜] 𝕜)

/-- The fibers of a vector bundle are finite-dimensional if the model fiber is finite-dimensional. -/
noncomputable def VectorBundle.finiteDimensional_fiber
    (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {B : Type w} [TopologicalSpace B]
    {E : B → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)]
    [TopologicalSpace (Bundle.TotalSpace F E)]
    [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E]
    [VectorBundle 𝕜 F E]
    (x : B) :
    FiniteDimensional 𝕜 (E x) :=
  -- Get a trivialization at `x` from the FiberBundle atlas
  let triv := trivializationAt F E x
  -- Get the fact that x is in the base set
  let hx := mem_baseSet_trivializationAt F E x
  -- Obtain linear property through the vector bundle structure
  have h_linear : triv.IsLinear 𝕜 := by
    apply VectorBundle.trivialization_linear'
  -- Register linearity as an instance
  haveI : triv.IsLinear 𝕜 := h_linear
  -- Get the linear equivalence between the fiber E x and the model fiber F
  let linear_equiv := triv.continuousLinearEquivAt 𝕜 x hx
  -- Transfer the finite-dimensionality from F to E x via the linear equivalence
  have : FiniteDimensional 𝕜 (E x) :=
    LinearEquiv.finiteDimensional linear_equiv.symm.toLinearEquiv
  this

-- Instance providing FiniteDimensional for tangent spaces, needed for VectorBundle.dual
-- Require the VectorBundle instance explicitly as an argument
noncomputable instance TangentSpace.finiteDimensional
  (𝕜 : Type u) [NontriviallyNormedField 𝕜]
  {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] -- Model Fiber E
  {H : Type w} [TopologicalSpace H]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners 𝕜 E H)
  -- Add SmoothManifoldWithCorners instance, which implies the bundle structures
  [IsManifold I ⊤ M] -- Specify smoothness level, e.g., C^infinity
  (x : M) :
  FiniteDimensional 𝕜 (TangentSpace I x) :=
  -- The fibers of a vector bundle with a finite-dimensional model fiber are finite-dimensional.
  -- The FiberBundle and VectorBundle instances are inferred from IsManifold I ⊤ M.
  VectorBundle.finiteDimensional_fiber 𝕜 (F := E) (E := TangentSpace I) x

-- Instance for the dual bundle (VectorBundle)
section DualBundle
  variable (𝕜 : Type u) [NontriviallyNormedField 𝕜]
    {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {H : Type w} [TopologicalSpace H]
    {M : Type w} [TopologicalSpace M] [ChartedSpace H M] -- Explicitly require ChartedSpace
    (I : ModelWithCorners 𝕜 E H)
    [IsManifold I ⊤ M] -- This requires ChartedSpace H M and provides TangentBundle structure

  -- Define the dual bundle type family
  abbrev TangentDualFiber (x : M) := TangentSpace I x →L[𝕜] 𝕜
  -- Define the model fiber for the dual bundle
  abbrev TangentDualModelFiber := E →L[𝕜] 𝕜

  -- Explicitly provide instances for the dual model fiber
  noncomputable instance : NormedAddCommGroup (E →L[𝕜] 𝕜) := inferInstance
  noncomputable instance : NormedSpace 𝕜 (E →L[𝕜] 𝕜) := inferInstance
  -- Finite dimensionality of the dual model fiber requires FiniteDimensional 𝕜 E
  noncomputable instance : FiniteDimensional 𝕜 (E →L[𝕜] 𝕜) := inferInstance

-- Instance for the trivial vector bundle M × 𝕜 needed for continuousLinearMap
  noncomputable instance TrivialBundleInstance : VectorBundle 𝕜 𝕜 (fun _ : M => 𝕜) :=
    Bundle.Trivial.vectorBundle 𝕜 M 𝕜

end DualBundle
end PseudoRiemannianMetric
