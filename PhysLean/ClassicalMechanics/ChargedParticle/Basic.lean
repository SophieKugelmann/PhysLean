import PhysLean.Electromagnetism.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

def path := Time → Space

noncomputable def velocity (r : path) : Time → Space := deriv r

noncomputable def acceleration (r : path) : Time → Space := fun t => deriv (deriv r) t


/-- The charged particle is specified by a mass `m`, a charge `q` and its path.
  The mass is assumed to be positive. -/
structure ChargedParticle where
  /-- The charge of the particle -/
  q : ℝ
  /-- The mass of the particle -/
  m : ℝ

  m_pos : 0 < m


open Electromagnetism
open Real

def cross (V W : Space): Space :=
  ↑ (crossProduct V W)


/-- The speed of light. This is set to 3 for now as a placeholder.-/
def c := 3

/-- The EM-System is specified by an electric field 'E', a magnetic field 'B' and a charged particle 'p'. -/
structure ChargedParticleInEM where
  E : ElectricField
  B : MagneticField
  p : ChargedParticle


/-- The equation of motion for a charged particle in an Electromagnetic-field. -/
def EquationOfMotion (EM : ChargedParticleInEM) (r : path) : Prop := ∀t ,
EM.p.m • (acceleration r t) = EM.p.q • ((EM.E t (r t)) + ((1/c) • cross (velocity r t) (EM.B t (r t))))


/-- The initial conditions for the motion of a particle in EM-field
  specified by a charged particle, an electric field, a magnetic field,
  a starting point and a given initial velocity. -/
structure InitialConditions where
  /-- The initial velocity. -/
  v₀ : Fin 3 → ℝ
  /-- The starting point. -/
  r₀ : Fin 3 → ℝ

/-- The conditions that the particle is restricted to a plane with a perpendicular magnetic field and E=0. -/
structure ChargedParticleInEM_restriction extends ChargedParticleInEM where
  b : ℝ
  B_perpendicular : ∀ x : Space , ∀ t, B t x = ![0,0,b]
  E_zero: E = 0


def plane_restriction (IC : InitialConditions) (EMS : ChargedParticleInEM) : Prop := ∀t : Time, ∀x : Space, inner ℝ (EMS.B t x) IC.v₀=0

namespace ChargedParticleInEM_restriction

/-- Given the initial conditions and certain restrictions named EM_Special, the solution to the equation of motion. -/
noncomputable def sol (EMS : ChargedParticleInEM_restriction)(IC: InitialConditions) : path := fun t =>
  let d := EMS.p.m*c/(EMS.p.q*EMS.b)
  ![d*(IC.v₀ 0)*(sin d⁻¹*t)-d*(IC.v₀ 1)*(cos d⁻¹*t)+(IC.r₀ 0)+d*(IC.v₀ 1),
    d*(IC.v₀ 0)*(cos d⁻¹*t)+d*(IC.v₀ 1)*(sin d⁻¹*t)+(IC.r₀ 1)+d*(IC.v₀ 0),
    IC.r₀ 2]


lemma cross_simp (EMS : ChargedParticleInEM_restriction) (r : path) : ∀ t,
cross (velocity r t) (EMS.B t (r t)) = EMS.b •![velocity r t 1, (-1) * (velocity r t 0), 0] := by
  simp [cross]
  intro t
  have hB : EMS.B  t (r t) = ![0,0,EMS.b] := by
    apply EMS.B_perpendicular
  rw [hB, crossProduct]
  simp
  rw [mul_comm (velocity r t 1) EMS.b, mul_comm EMS.b (velocity r t 0)]


lemma EquationOfMotion_simp (EMS : ChargedParticleInEM_restriction) (r : path) :
(EquationOfMotion EMS.toChargedParticleInEM r) ↔ (∀t , EMS.p.m • (acceleration r t) =
EMS.p.q • (1/c) • EMS.b •![velocity r t 1, (-1) * (velocity r t 0), 0] ) := by
  constructor
  · rw [EquationOfMotion]
    intro h
    rw [EMS.E_zero] at h
    simp at h
    exact h
  · rw [EquationOfMotion]
    intro h
    rw [EMS.E_zero]
    simp
    exact h

#check fderiv

lemma solution_true (EMS : ChargedParticleInEM_restriction) (IC : InitialConditions) : (EquationOfMotion EMS.toChargedParticleInEM (sol EMS IC)):= by sorry


-- The condition that there is no field and its solution.

variable (p : ChargedParticle)
variable (r₀ : Fin 3 → ℝ)
variable (v₀ : Fin 3 → ℝ)

/-- The condition that there is no field. -/
def zeroEM : ChargedParticleInEM := ⟨0,0,p⟩

-- /-- The zero initial condition has zero electric field. -/
-- @[simp]
-- lemma E_zeroIC : zeroEM.E = 0 := rfl

-- /-- The zero initial condition has zero magnetic field. -/
-- @[simp]
-- lemma B_zeroIC : (zeroIC p v₀ r₀).B = 0 := rfl


end ChargedParticleInEM_restriction
