/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.ClassicalMechanics.Time.Basic
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic
/-!
# Seconds

In this file we define the notation of a second.

## Explaination

The type `Time` is defined as `ℝ`.
The type `ℝ` carries the instance of `NormedField`, giving us one
way to define distances between times.

However, this norm (since it is defined through the field structure on `ℝ`)
gives special meaning to `1`, which it does not have in the context of time.
Afterall, time does not form a field - the product of two times is not a time.

In fact we can rescale the norm on `ℝ` to give a different, but completely
valid definition of distance between two times.

This ambiguity is removed if we pick the time between two events `p1` and `p2`
in SpaceTime
and define distances in time relative to the difference in time between `p1` and `p2`.

If we fix `p1` and `p2` to correspond to the start and end of 9 192 631 770
hyperfine transtions of the unperturbed ground-state of caesium-133 atom, this
relative distance corresponds to a second.

So how do we tell Lean about `p1` and `p2`? We do this by
introducing an axiom.

Note that none of the definitions here are computable.

-/

namespace Time

/-- The axiom that there are two events in time whose seperation
  is defined to be a second. -/
axiom secondAxiom : {p : SpaceTime × SpaceTime |
  Lorentz.Vector.causallyFollows p.1 p.2}

/-- The event at which the start of the event defining a second occured. -/
noncomputable abbrev secondSpaceTimeStart : SpaceTime := secondAxiom.1.1

/-- The event at which the end of the event defining a second occured. -/
noncomputable abbrev secondSpaceTimeEnd : SpaceTime := secondAxiom.1.2

lemma secondSpaceTimeEnd_causallyFollows_secondSpaceTimeStart :
    Lorentz.Vector.causallyFollows secondSpaceTimeStart secondSpaceTimeEnd :=
  secondAxiom.2

/-- The time at which the start of the event defining a second occured. -/
noncomputable abbrev secondTimeStart : Time := Lorentz.Vector.timeComponent secondSpaceTimeStart

/-- The time at which the end of the event defining a second occured. -/
noncomputable abbrev secondTimeEnd : Time := Lorentz.Vector.timeComponent secondSpaceTimeEnd

lemma secondTimeStart_lt_secondTimeEnd :
    secondTimeStart < secondTimeEnd := by
  have h1 := secondSpaceTimeEnd_causallyFollows_secondSpaceTimeStart
  simp [Lorentz.Vector.causallyFollows] at h1
  rcases h1 with h1 | h1
  · simp [Lorentz.Vector.interiorFutureLightCone] at h1
    linarith
  · simp [Lorentz.Vector.futureLightConeBoundary] at h1
    linarith

/-- The definition of a second. -/
noncomputable def second : ℝ := dist secondTimeStart secondTimeEnd

lemma second_ne_zero : second ≠ 0 := by
  simp [second]
  have h1 := secondTimeStart_lt_secondTimeEnd
  linarith

/-- The distance between two time events in seconds. -/
noncomputable def distSecond (p1 p2 : Time) : ℝ :=
  dist p1 p2 / second

/-- The time between two events in minutes. -/
noncomputable def distMinute (p1 p2 : Time) : ℝ :=
  60 * distSecond p1 p2

/-- The time between two events in hours. -/
noncomputable def distHour (p1 p2 : Time) : ℝ :=
  60 * 60 * distSecond p1 p2

end Time
