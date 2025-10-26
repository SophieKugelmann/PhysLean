import PhysLean.Electromagnetism.Basic
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.Deriv.Pi

-- for now Time is Tim cause the Definition was changed, have to adjust
abbrev Tim := ℝ

def path := Tim → Space

noncomputable def velocity (r : path) : Tim → (Fin 3 → ℝ) := fun t i => deriv (fun t => r t i) t

noncomputable def acceleration (r : path) : Tim → (Fin 3 → ℝ) := fun t i => deriv (fun t => velocity r t i) t

/-- The charged particle is specified by a mass `m`, a charge `q`.
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


/-- The equation of motion for a charged particle in an electromagnetic-field. -/
def EquationOfMotion (EM : ChargedParticleInEM) (r : path) : Prop := ∀t ,
EM.p.m • (acceleration r t) = EM.p.q • ((EM.E t (r t)) + ((1/c) • cross (velocity r t) (EM.B t (r t))))


/-- The initial conditions for the motion of a particle in EM-field
  specified by a starting point and a given initial velocity. -/
structure InitialConditions where
  /-- The initial velocity. -/
  v₀ : Fin 3 → ℝ
  /-- The starting point. -/
  r₀ : Fin 3 → ℝ

/-- The conditions that B is parallel to the z-axis and E=0. -/
structure ChargedParticleInEM_restriction extends ChargedParticleInEM where
  b : ℝ
  B_parallel : ∀ x : Space , ∀ t, B t x = ![0,0,b]
  E_zero: E = 0

namespace ChargedParticleInEM_restriction

/-- Given the ChargedParticleInEM_restrcition and initial conditions, the solution to the equation of motion. -/
noncomputable def sol (EMS : ChargedParticleInEM_restriction)(IC: InitialConditions) : path :=
  let d := EMS.p.m*c/(EMS.p.q*EMS.b)
  fun t =>
  ![d*(IC.v₀ 0)*(sin d⁻¹*t)-d*(IC.v₀ 1)*(cos d⁻¹*t)+(IC.r₀ 0)+d*(IC.v₀ 1),
    d*(IC.v₀ 0)*(cos d⁻¹*t)+d*(IC.v₀ 1)*(sin d⁻¹*t)+(IC.r₀ 1)+d*(IC.v₀ 0),
    IC.r₀ 2]


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


lemma solution_true (EMS : ChargedParticleInEM_restriction) (IC : InitialConditions) : (EquationOfMotion EMS.toChargedParticleInEM (sol EMS IC)):= by
  rw [EquationOfMotion_simp EMS (sol EMS IC)]
  intro t
  apply funext
  intro i
  fin_cases i
  · set d := EMS.p.m*c/(EMS.p.q*EMS.b) with hd
    dsimp [acceleration, velocity]
    unfold sol
    simp
    rw [← hd]
    sorry

  · sorry
  · sorry

-- lemma satisfies_IC (EMS : ChargedParticleInEM_restriction) (IC : InitialConditions) : (EMS.sol IC 0 = IC.r₀ ∧ deriv EMS.sol IC 0 = IC.v₀):= by sorry


-- The condition that there is no field and its solution.
variable (p : ChargedParticle)
variable (r₀ : Fin 3 → ℝ)
variable (v₀ : Fin 3 → ℝ)

/-- The condition that there is no field. -/
def zeroEM : ChargedParticleInEM := ⟨0,0,p⟩
-- ...

end ChargedParticleInEM_restriction
