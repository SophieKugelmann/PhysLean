import PhysLean.Electromagnetism.Basic
import Mathlib.LinearAlgebra.CrossProduct



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
  /-- The path of the particle -/
  r : path

  m_pos : 0 < m


namespace ChargedParticle


@[simp]
lemma m_neq_zero (p : ChargedParticle) : p.m ≠ 0 := Ne.symm (ne_of_lt p.m_pos)

end ChargedParticle


open Electromagnetism
open ChargedParticle
open Real

@[simp]
noncomputable def Force (m : ℝ) (r : path) (t : Time): (Fin 3 → ℝ) := m • ((acceleration r) t)

@[simp]
noncomputable abbrev F := Force


def cross (V W : Space): Space :=
  ↑ (crossProduct V W)


/-- The speed of light. This is set to 3 for now as a placeholder.-/
def c := 3

variable (p : ChargedParticle)
variable (E : ElectricField)
variable (B : MagneticField)
variable (t : Time)


axiom LorentzForce:
  F p.m p.r t = p.q • ((E t (p.r t)) + ((1/c) • cross (velocity p.r t) (B t (p.r t))))



/-- The equation of motion for a charged particle in a EM-field. -/
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

/-- The initial conditions that the particle is restricted to a plane with a perpendicular magnetic field and E=0. -/
structure B_perpendicular_IC extends InitialConditions where
  prz := ∀ t, p.r t 2  =  r₀ 2
  b : ℝ
  Bz := ∀ t, B t (p.r t) 2  = b
  E := 0
