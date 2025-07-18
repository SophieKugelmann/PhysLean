
-- noncomputable def acceleration (p : ChargedParticle): Time → Space := deriv (velocity p)


--don't forget the speed of light

--def LorentzForce (E : ElectricField) (B : MagneticField) (p : cPIF): Prop :=
--  ∀ t, p.m • (acceleration p t) = p.q • (E t+crossProduct (velocity p t) B t)


-- noncomputable def acceleration (r : path)(t : Time): Space :=
-- deriv (deriv r) t

-- noncomputable def velocity (r : path)(t : Time): Space :=
-- deriv r t



-- def LorentzForce (E : ElectricField) (B : MagneticField) (p : ChargedParticle) (r : path): Prop :=
-- ∀ t, p.m • (acceleration r t) = p.q • (E t (r t) + crossProduct (velocity r t) (B t (r t)))


-- Version mit F
--def EquationOfMotion (E : Time → Space → Fin 3 → ℝ) (B : MagneticField) (p : ChargedParticle) (r : path) : Prop :=
 -- ∀ t, F p r t = p.q • (E t (r t) + (crossProduct (velocity r t) (B t (r t))))

-- Version mit fin3
-- def EquationOfMotion (E : Time → Space → Fin 3 → ℝ) (B : MagneticField) (p : ChargedParticle) (r : path) : Prop :=
--  ∀ t, p.m • acceleration r t = p.q • (E t (r t) + (crossProduct (velocity r t) (B t (r t))))


-- def LorentzForce (E : ElectricField) (B : MagneticField) (p : ChargedParticle) (r : path) : Prop :=
--   ∀ t, F p r t = p.q • ((E t (r t)) + (crossy (velocity r t) (B t (r t))))

-- axiom LorentzForce_holds :
--  LorentzForce E B p r






-- lemma sol_eq (IC : InitialConditions) :
--     S.sol IC = fun t => IC.x₀ * cos (S.ω * t) + IC.v₀/S.ω * sin (S.ω * t) := rfl

-- /-- For zero initial conditions, the solution is zero. -/
-- lemma sol_zeroIC : S.sol zeroIC = fun _ => 0 := by
--   simp [sol_eq]


--def B₀ : MagneticField:= λ (t r) => ![0, 0, z]


-- initial shit
-- But I tried:
variable (b : ℝ)
variable (x : Time → ℝ)
variable (y : Time → ℝ)

def B₀ : MagneticField := fun t r => ![0, 0, b]

variable (x : Time → ℝ)
variable (y : Time → ℝ)

/-- The initial condition that the particle is restricted to a plane with a perpendicular magnetic field and E=0. -/
def B_perpendicular_IC : InitialConditions := ⟨p ,0 ,B₀ b,v₀,r₀⟩
  where p.r := fun t  => ![x t, y t, 0]



  fun t =>

-- teil vom axiom

∀ (E : ElectricField) (B : MagneticField) (p : ChargedParticle)(t : Time),


def mass := ℝ


-- importante!!!

namespace ChargedParticle

@[simp]
lemma m_neq_zero (p : ChargedParticle) : p.m ≠ 0 := Ne.symm (ne_of_lt p.m_pos)

end ChargedParticle



open ChargedParticle


@[simp]
noncomputable def Force (m : ℝ) (r : path) (t : Time): (Fin 3 → ℝ) := m • ((acceleration r) t)

@[simp]
noncomputable abbrev F := Force

axiom LorentzForce:
  F p.m p.r t = p.q • ((E t (p.r t)) + ((1/c) • cross (velocity p.r t) (B t (p.r t))))


-------------------------

-- -- warum geht das hier nicht wie bei Equation of Motion sondern braucht input
-- /-- The equation of motion for a charged particle in a magnetic-field. -/
-- lemma EquationOfMotion_ENull (EM : EM_System) (h: E = 0) (r : path):
--  ∀ t, EM.p.m • (acceleration r t) = EM.p.q • (((1/c) • cross (velocity r t) (EM.B t (r t)))):= by
--  intro k
--  rw [h]
--  rfl


lemma cross_simp (EMS : EM_Special) (r : path) (t : Time):
cross (velocity r t) (EMS.B t (r t)) = ![EMS.b * (velocity r t 1), EMS.b * (-1) * (velocity r t 0), 0] := by
  simp [cross]
  have hB : EMS.B  t (r t) = ![0,0,EMS.b] := by
    apply EMS.B_perpendicular
  rw [hB, crossProduct]
  simp
  rw [mul_comm (velocity r t 1) EMS.b, mul_comm EMS.b (velocity r t 0)]





  -- lemma one (EMS : EM_Special) (IC : InitialConditions) : ∀t : Time ,velocity (sol EMS IC) t 2 = 0 := by
--   intro k
--   rw [velocity]



-- lemma two (EMS : EM_Special) (IC : InitialConditions) :
--   ∀t , EMS.p.m * (deriv (deriv (fun t : ℝ  ↦ sol EMS IC 2)) t) = EMS.p.q * (1/c)* (EMS.b * (deriv (fun t : ℝ  ↦ sol EMS IC 2)) t ) := by
--   simp


--  lemma one (EMS : EM_Special) (IC : InitialConditions): ∀t ,
--   EMS.p.m • (deriv deriv (sol EMS IC) 2) = EMS.p.q • ((1/c) • EMS.b • deriv IC.r₀ 2):= by
--   sorry




-- lemma solution_true (EMS : EM_Special) (IC : InitialConditions) : (EquationOfMotion EMS.toEM_System (sol EMS IC)):= by
--   intro k
--   rw[EMS.E_zero]
--   simp



def zeroEM : ChargedParticleInEM := {E:=0, B:=0,p}
