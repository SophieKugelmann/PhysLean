import PhysLean.Electromagnetism.Basic
import Mathlib.LinearAlgebra.CrossProduct
import PhysLean.ClassicalMechanics.ChargedParticle.Basic


open Electromagnetism
open ChargedParticle
open Real

-- using Gauß system

-- m mass definieren?
@[simp]
noncomputable def Force (m : ℝ) (r : path) (t : Time): (Fin 3 → ℝ) := m • ((acceleration r) t)

@[simp]
noncomputable abbrev F := Force


def cross (V W : Space): Space :=
  ↑ (crossProduct V W)


/-- The speed of light UNVOLLSTÄNDIG-/
def c := 3

variable (p : ChargedParticle)
variable (E : ElectricField)
variable (B : MagneticField)
variable (t : Time)


axiom LorentzForce:
  F p.m p.r t = p.q • ((E t (p.r t)) + ((1/c) • cross (velocity p.r t) (B t (p.r t))))


lemma EquationOfMotion : p.m • (acceleration p.r t) = p.q • ((E t (p.r t)) + ((1/c) • cross (velocity p.r t) (B t (p.r t)))):= by
 rw [← LorentzForce]
 rfl


/-- The initial conditions for the motion of a particle in EM-field
  specified by a charged particle, an electric field, a magnetic field,
  a starting point and a given initial velocity. -/
structure InitialConditions where
  /-- The charged particle. -/
  p : ChargedParticle
  /-- The electric field. -/
  E : ElectricField
  /-- The magnetic field. -/
  B : MagneticField
  /-- The initial velocity. -/
  v₀ : Fin 3 → ℝ
  /-- The starting point. -/
  r₀ : Fin 3 → ℝ


-- geklaut


/-- Prove that if the 'elements/fields' of two initial conditions are equal, the initial conditions are equal. -/
@[ext]
lemma InitialConditions.ext {IC₁ IC₂ : InitialConditions} (h1 : IC₁.p = IC₂.p)
    (h2 : IC₁.E = IC₂.E) (h3 : IC₁.B = IC₂.B) (h4 : IC₁.v₀ = IC₂.v₀) (h5 : IC₁.r₀ = IC₂.r₀)
    : IC₁ = IC₂ := by
  cases IC₁
  cases IC₂
  simp_all


-- The zero initial condition

-- sinnvoll?
variable (r₀ : Fin 3 → ℝ)
variable (v₀ : Fin 3 → ℝ)


/-- The zero initial condition. -/
def zeroIC : InitialConditions := ⟨p,0,0,v₀,r₀⟩

/-- The zero initial condition has zero electric field. -/
@[simp]
lemma E_zeroIC : (zeroIC p v₀ r₀).E = 0 := rfl

/-- The zero initial condition has zero magnetic field. -/
@[simp]
lemma B_zeroIC : (zeroIC p v₀ r₀).B = 0 := rfl


/-- The initial condition that the particle is restricted to a plane with a perpendicular magnetic field and E=0. -/
structure B_perpendicular_IC extends InitialConditions where
  prz := ∀ t, p.r t 2  =  r₀ 2
  b : ℝ
  Bz := ∀ t, B t (p.r t) 2  = b
  E := 0



variable (IC : B_perpendicular_IC)


/-- Given the initial condition named B_perpendicular_IC, the solution to the equation of motion. -/
noncomputable def sol : path := fun t =>
  let d := IC.p.m*c/(IC.p.q*IC.b)
  ![d*(IC.v₀ 0)*(sin d⁻¹*t)-d*(IC.v₀ 1)*(cos d⁻¹*t)+(IC.r₀ 0)+d*(IC.v₀ 1),
    d*(IC.v₀ 0)*(cos d⁻¹*t)+d*(IC.v₀ 1)*(sin d⁻¹*t)+(IC.r₀ 1)+d*(IC.v₀ 0),
    IC.r₀ 2]



-- For the zero initial condition, the solution is zero. -/
--lemma sol_zeroIC : S.sol zeroIC = fun _ => 0 := by

--lemma sol_B_perpendicular_IC : EquationOfMotion IC.p IC.E IC.B :=
