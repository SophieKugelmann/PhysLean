/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Data.Finset.Sort
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges

open PotentialTerm

inductive ChargeLeaf
  | leaf : Finset ℤ → ChargeLeaf

unsafe instance : Repr ChargeLeaf where
  reprPrec x _ :=
    match x with
    | .leaf xs => "leaf " ++ reprStr xs

inductive ChargeTwig
  | twig : Finset ℤ → Multiset ChargeLeaf → ChargeTwig

unsafe instance : Repr ChargeTwig where
  reprPrec x _ :=
    match x with
    | .twig xs a => "twig " ++ reprStr xs  ++ " " ++ reprStr a

inductive ChargeBranch
  | branch : Option ℤ → Multiset ChargeTwig → ChargeBranch

unsafe instance : Repr ChargeBranch where
  reprPrec x _ :=
    match x with
    | .branch xa a => "branch (" ++ reprStr xa ++ ") " ++ reprStr a

inductive ChargeTrunk
  | trunk : Option ℤ → Multiset ChargeBranch → ChargeTrunk

unsafe instance : Repr ChargeTrunk where
  reprPrec x _ :=
    match x with
    | .trunk xa a => "trunk (" ++ reprStr xa ++ ") " ++ reprStr a

inductive ChargeTree
  | root : Multiset ChargeTrunk → ChargeTree

unsafe instance : Repr ChargeTree where
  reprPrec x _ :=
    match x with
    | .root xs => "root " ++ reprStr xs

namespace ChargeTree

open ChargeLeaf ChargeTwig ChargeBranch ChargeTrunk

def fromMultiset (l : Multiset Charges) : ChargeTree :=
  let A1 : Multiset (Option ℤ) := (l.map fun x => x.1).dedup
  root <| A1.map fun xa => trunk xa <|
    let B2 := (l.filter fun y => y.1 = xa)
    let C2 : Multiset (Option ℤ × Finset ℤ × Finset ℤ) := (B2.map fun y => y.2).dedup
    let A2 : Multiset (Option ℤ) := (C2.map fun x => x.1).dedup
    A2.map fun xb => branch xb <|
      let B3 := (C2.filter fun y => y.1 = xb)
      let C3 : Multiset (Finset ℤ × Finset ℤ) := (B3.map fun y => y.2).dedup
      let A3 : Multiset (Finset ℤ) := (C3.map fun x => x.1).dedup
      A3.map fun xc => twig xc <|
        let B4 := (C3.filter fun y => y.1 = xc)
        let C4 : Multiset (Finset ℤ) := (B4.map fun y => y.2).dedup
        C4.map fun xd => leaf xd

def toMultiset (T : ChargeTree) : Multiset Charges :=
  match T with
  | .root trunks =>
    trunks.bind fun (trunk xT branches) =>
        branches.bind fun (branch xB twigs) =>
            twigs.bind fun (twig xTw leafs) =>
                leafs.map fun (leaf xL)  => (xT, xB, xTw, xL)

end ChargeTree

/-!

## Subset of members condition

-/

def ChargeLeaf.SupersetOfMem (T : ChargeLeaf) (x : Finset ℤ)  : Prop :=
  match T with
  | .leaf xs => xs ⊆ x

instance (T : ChargeLeaf) (x : Finset ℤ)  : Decidable (T.SupersetOfMem x) :=
  inferInstanceAs (Decidable (match T with | .leaf xs => xs ⊆ x ))

def ChargeTwig.SupersetOfMem (T : ChargeTwig) (x : Finset ℤ × Finset ℤ) : Prop :=
  match T with
  | .twig xs leafs => xs ⊆ x.1 ∧ ∃ leaf ∈ leafs, leaf.SupersetOfMem x.2

instance (T : ChargeTwig) (x : Finset ℤ × Finset ℤ) : Decidable (T.SupersetOfMem x) :=
  match T with
  | .twig _ leafs =>
    haveI : Decidable (∃ leaf ∈ leafs, leaf.SupersetOfMem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

def ChargeBranch.SupersetOfMem (T : ChargeBranch) (x : Option ℤ × Finset ℤ × Finset ℤ) : Prop :=
  match T with
  | .branch xo twigs => xo.toFinset ⊆ x.1.toFinset ∧ ∃ twig ∈ twigs, twig.SupersetOfMem x.2

instance (T : ChargeBranch) (x : Option ℤ × Finset ℤ × Finset ℤ) : Decidable (T.SupersetOfMem x) :=
  match T with
  | .branch _ twigs =>
    haveI : Decidable (∃ twig ∈ twigs, twig.SupersetOfMem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

def ChargeTrunk.SupersetOfMem (T : ChargeTrunk) (x : Charges) : Prop :=
  match T with
  | .trunk xo branches => xo.toFinset ⊆ x.1.toFinset ∧ ∃ branch ∈ branches, branch.SupersetOfMem x.2

instance (T : ChargeTrunk) (x : Charges) : Decidable (T.SupersetOfMem x) :=
  match T with
  | .trunk _ branches =>
    haveI : Decidable (∃ branch ∈ branches, branch.SupersetOfMem x.2) := Multiset.decidableExistsMultiset
    instDecidableAnd

def ChargeTree.SupersetOfMem (T : ChargeTree) (x : Charges) : Prop :=
  match T with
  | .root trunks => ∃ trunk ∈ trunks, trunk.SupersetOfMem x

instance (T : ChargeTree) (x : Charges) : Decidable (T.SupersetOfMem x) :=
  Multiset.decidableExistsMultiset


end Charges

end SU5U1

end FTheory
