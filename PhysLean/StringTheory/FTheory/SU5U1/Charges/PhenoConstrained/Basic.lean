/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Basic
import PhysLean.StringTheory.FTheory.SU5U1.Potential.ChargeProfile.Irreducible.Elems
import PhysLean.StringTheory.FTheory.SU5U1.Charges.Tree
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}
namespace Charges
open PotentialTerm
open ChargeProfile

def IsPhenoConstrained (x : Charges) : Prop :=
  IsPresent μ (toChargeProfile μ x) ∨
  IsPresent β (toChargeProfile β x) ∨
  IsPresent Λ (toChargeProfile Λ x) ∨
  IsPresent W2 (toChargeProfile W2 x) ∨
  IsPresent W4 (toChargeProfile W4 x) ∨
  IsPresent K1 (toChargeProfile K1 x) ∨
  IsPresent K2 (toChargeProfile K2 x) ∨
  IsPresent W1 (toChargeProfile W1 x)

instance decidableIsPhenoConstrained (x : Charges) : Decidable x.IsPhenoConstrained :=
  inferInstanceAs (Decidable (IsPresent μ (toChargeProfile μ x) ∨
    IsPresent β (toChargeProfile β x) ∨
    IsPresent Λ (toChargeProfile Λ x) ∨
    IsPresent W2 (toChargeProfile W2 x) ∨
    IsPresent W4 (toChargeProfile W4 x) ∨
    IsPresent K1 (toChargeProfile K1 x) ∨
    IsPresent K2 (toChargeProfile K2 x) ∨
    IsPresent W1 (toChargeProfile W1 x)))

def IsIrreducible (x : Charges) : Prop :=
  ∀ y ∈ powerset x, y = x ↔ IsPhenoConstrained y

instance decidableIsIrreducible (x : Charges) : Decidable x.IsIrreducible :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ IsPhenoConstrained y))

def testElems (I : CodimensionOneConfig) :  ChargeTree :=
  let S1 := (irreducibleElems I μ).map (fromChargeProfile μ)
  let S2 := (irreducibleElems I β).map (fromChargeProfile β)
  let S3 := (irreducibleElems I Λ).map (fromChargeProfile Λ)
  let S4 := (irreducibleElems I W2).map (fromChargeProfile W2)
  let S5 := (irreducibleElems I W4).map (fromChargeProfile W4)
  let S6 := (irreducibleElems I K1).map (fromChargeProfile K1)
  let S7 := (irreducibleElems I K2).map (fromChargeProfile K2)
  let S8 := (irreducibleElems I W1).map (fromChargeProfile W1)
  let T1 := (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8)
  let T3 := T1.filter fun x => IsIrreducible x

  ChargeTree.fromMultiset T3


open ChargeTree ChargeBranch ChargeTwig ChargeLeaf ChargeTrunk

def irreducibleTree (I : CodimensionOneConfig) : ChargeTree :=
  match I with
  | .same =>
    root {trunk (some (-3)) {branch (some (-3)) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {1}, leaf {-1, 2}, leaf {-3, 3}, leaf {0, 3}, leaf {-2, 2, 3}}},
    branch (some (-2)) {twig {-1} {leaf ∅}},
    branch (some (-1)) {twig {1} {leaf ∅}},
    branch (some 0) {twig {3} {leaf ∅}, twig ∅ {leaf {3}}},
    branch (some 1) {twig ∅ {leaf {2}}},
    branch (some 3) {twig ∅ {leaf {0}}}},
  trunk (some (-2)) {branch (some (-2)) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {0, 1}, leaf {-2, 2}, leaf {0, 2}, leaf {-1, 1, 2}, leaf {-1, 0, 3}, leaf {-2, 1, 3}, leaf {-3, 2, 3}}},
    branch (some (-1)) {twig {0} {leaf ∅}, twig ∅ {leaf {3}}},
    branch (some 0) {twig {2} {leaf ∅}, twig ∅ {leaf {2}}},
    branch (some 1) {twig ∅ {leaf {1}}},
    branch (some 2) {twig ∅ {leaf {0}}},
    branch (some 3) {twig ∅ {leaf {-1}}}},
  trunk (some (-1)) {branch (some (-1)) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {-1, 1},
      leaf {0, 1},
      leaf {-3, 2},
      leaf {-1, 0, 2},
      leaf {-2, 1, 2},
      leaf {-1, 3},
      leaf {-2, 0, 3},
      leaf {-3, 1, 3}}},
    branch (some (-2)) {twig {-3} {leaf ∅}, twig ∅ {leaf {3}}},
    branch (some 0) {twig {1} {leaf ∅}, twig ∅ {leaf {1}}},
    branch (some 1) {twig {3} {leaf ∅}, twig ∅ {leaf {0}}},
    branch (some 2) {twig ∅ {leaf {-1}}},
    branch (some 3) {twig ∅ {leaf {-2}}}},
  trunk (some 0) {branch (some 0) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {0}, leaf {-2, 1}, leaf {-1, 2}, leaf {-3, 1, 2}, leaf {-2, -1, 3}}},
    branch (some (-3)) {twig ∅ {leaf {3}}},
    branch (some (-2)) {twig ∅ {leaf {2}}},
    branch (some (-1)) {twig {-2} {leaf ∅}, twig ∅ {leaf {1}}},
    branch (some 1) {twig {2} {leaf ∅}, twig ∅ {leaf {-1}}},
    branch (some 2) {twig ∅ {leaf {-2}}},
    branch (some 3) {twig ∅ {leaf {-3}}}},
  trunk (some 1) {branch (some 1) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {-1, 0},
      leaf {-3, 1},
      leaf {-1, 1},
      leaf {-2, 0, 1},
      leaf {-2, -1, 2},
      leaf {-3, 0, 2},
      leaf {-2, 3},
      leaf {-3, -1, 3}}},
    branch (some (-3)) {twig ∅ {leaf {2}}},
    branch (some (-2)) {twig ∅ {leaf {1}}},
    branch (some (-1)) {twig {-3} {leaf ∅}, twig ∅ {leaf {0}}},
    branch (some 0) {twig {-1} {leaf ∅}, twig ∅ {leaf {-1}}},
    branch (some 2) {twig {3} {leaf ∅}, twig ∅ {leaf {-3}}}},
  trunk (some 2) {branch (some 2) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {-2, 0}, leaf {-1, 0}, leaf {-2, -1, 1}, leaf {-3, 0, 1}, leaf {-2, 2}, leaf {-3, -1, 2}, leaf {-3, -2, 3}}},
    branch (some (-3)) {twig ∅ {leaf {1}}},
    branch (some (-2)) {twig ∅ {leaf {0}}},
    branch (some (-1)) {twig ∅ {leaf {-1}}},
    branch (some 0) {twig {-2} {leaf ∅}, twig ∅ {leaf {-2}}},
    branch (some 1) {twig {0} {leaf ∅}, twig ∅ {leaf {-3}}}},
  trunk (some 3) {branch (some 3) {twig ∅ {leaf ∅}},
    branch (none) {twig ∅ {leaf {-1}, leaf {-3, 0}, leaf {-2, 1}, leaf {-3, -2, 2}, leaf {-3, 3}}},
    branch (some 1) {twig {-1} {leaf ∅}},
    branch (some 2) {twig {1} {leaf ∅}},
    branch (some (-3)) {twig ∅ {leaf {0}}},
    branch (some (-1)) {twig ∅ {leaf {-2}}},
    branch (some 0) {twig {-3} {leaf ∅}, twig ∅ {leaf {-3}}}},
  trunk (none) {branch (some (-3)) {twig {-3} {leaf ∅}},
    branch (some (-2)) {twig {-2} {leaf ∅}},
    branch (some (-1)) {twig {-1} {leaf ∅}},
    branch (some 0) {twig {0} {leaf ∅}},
    branch (some 1) {twig {1} {leaf ∅}},
    branch (some 2) {twig {2} {leaf ∅}},
    branch (some 3) {twig {3} {leaf ∅}},
    branch (none) {twig {-2, -1} {leaf {3}},
    twig {-3, 0} {leaf {3}},
    twig {-2, 0} {leaf {2}},
    twig {-1, 0} {leaf {1}},
    twig {-3, 1} {leaf {2}},
    twig {-2, 1} {leaf {1}},
    twig {-1, 1} {leaf {0}},
    twig {0, 1} {leaf {-1}},
    twig {-2, 2} {leaf {0}},
    twig {-1, 2} {leaf {-1}},
    twig {0, 2} {leaf {-2}},
    twig {1, 2} {leaf {-3}},
    twig {-3, 3} {leaf {0}},
    twig {-1, 3} {leaf {-2}},
    twig {0, 3} {leaf {-3}},
    twig {-3} {leaf {-2, -1}, leaf {-3, 0}, leaf {1}, leaf {-1, 2}, leaf {-3, 3}, leaf {0, 3}, leaf {-2, 2, 3}},
    twig {-2} {leaf {-1}, leaf {-2, 0}, leaf {-3, 1}, leaf {0, 1}, leaf {-2, 2}, leaf {0, 2}, leaf {-2, 1, 3}, leaf {-3, 2, 3}},
    twig {-1} {leaf {2}, leaf {-1, 0}, leaf {-2, 1}, leaf {-1, 1}, leaf {0, 1}, leaf {-1, 3}, leaf {-2, 0, 3}, leaf {-3, 1, 3}},
    twig {0} {leaf {-1, 1}, leaf {-2, 2}, leaf {-3, 3}, leaf {0}, leaf {-2, 1}, leaf {-1, 2}, leaf {-3, 1, 2}, leaf {-2, -1, 3}},
    twig {1} {leaf {-2}, leaf {0, 1}, leaf {-1, 2}, leaf {-1, 0}, leaf {-3, 1}, leaf {-1, 1}, leaf {-3, 0, 2}, leaf {-3, -1, 3}},
    twig {2} {leaf {1}, leaf {0, 2}, leaf {-1, 3}, leaf {-2, 0}, leaf {-1, 0}, leaf {-2, 2}, leaf {-3, -1, 2}, leaf {-3, -2, 3}},
    twig {3} {leaf {1, 2}, leaf {0, 3}, leaf {-1}, leaf {-3, 0}, leaf {-2, 1}, leaf {-3, -2, 2}, leaf {-3, 3}}}}}
  | .nearestNeighbor =>
    root {trunk (some (-14)) {branch (some (-14)) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-2, 8}, leaf {3, 8}, leaf {-12, 13}, leaf {-2, 3, 13}, leaf {-7, 8, 13}}},
  branch (some (-9)) {twig {-4} {leaf ∅}},
  branch (some (-4)) {twig {6} {leaf ∅}},
  branch (some 1) {twig ∅ {leaf {13}}},
  branch (some 6) {twig ∅ {leaf {8}}},
  branch (some 11) {twig ∅ {leaf {3}}}},
 trunk (some (-9)) {branch (some (-9)) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {3}, leaf {-7, 8}, leaf {-2, 13}, leaf {-12, 8, 13}}},
  branch (some (-4)) {twig {1} {leaf ∅}, twig ∅ {leaf {13}}},
  branch (some 1) {twig {11} {leaf ∅}, twig ∅ {leaf {8}}},
  branch (some 11) {twig ∅ {leaf {-2}}}},
 trunk (some (-4)) {branch (some (-4)) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-2, 3}, leaf {-12, 8}, leaf {-2, 8}, leaf {-7, 3, 8}, leaf {-7, -2, 13}, leaf {-12, 3, 13}}},
  branch (some (-9)) {twig {-14} {leaf ∅}, twig ∅ {leaf {13}}},
  branch (some 1) {twig {6} {leaf ∅}, twig ∅ {leaf {3}}},
  branch (some 6) {twig ∅ {leaf {-2}}},
  branch (some 11) {twig ∅ {leaf {-7}}}},
 trunk (some 1) {branch (some 1) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-7, 3}, leaf {-2, 3}, leaf {-7, -2, 8}, leaf {-12, 3, 8}, leaf {-7, 13}, leaf {-12, -2, 13}}},
  branch (some (-14)) {twig ∅ {leaf {13}}},
  branch (some (-9)) {twig ∅ {leaf {8}}},
  branch (some (-4)) {twig {-9} {leaf ∅}, twig ∅ {leaf {3}}},
  branch (some 6) {twig {11} {leaf ∅}, twig ∅ {leaf {-7}}},
  branch (some 11) {twig ∅ {leaf {-12}}}},
 trunk (some 6) {branch (some 6) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-2}, leaf {-12, 3}, leaf {-7, 8}, leaf {-12, -7, 13}}},
  branch (some (-4)) {twig {-14} {leaf ∅}},
  branch (some (-14)) {twig ∅ {leaf {8}}},
  branch (some (-9)) {twig ∅ {leaf {3}}},
  branch (some 1) {twig {-4} {leaf ∅}, twig ∅ {leaf {-7}}}},
 trunk (some 11) {branch (some 11) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-7, -2}, leaf {-7, 3}, leaf {-12, -2, 3}, leaf {-12, -7, 8}, leaf {-12, 13}}},
  branch (some 6) {twig {1} {leaf ∅}},
  branch (some (-14)) {twig ∅ {leaf {3}}},
  branch (some (-9)) {twig ∅ {leaf {-2}}},
  branch (some (-4)) {twig ∅ {leaf {-7}}},
  branch (some 1) {twig {-9} {leaf ∅}, twig ∅ {leaf {-12}}}},
 trunk (none) {branch (some (-14)) {twig {-14} {leaf ∅}},
  branch (some (-9)) {twig {-9} {leaf ∅}},
  branch (some (-4)) {twig {-4} {leaf ∅}},
  branch (some 1) {twig {1} {leaf ∅}},
  branch (some 6) {twig {6} {leaf ∅}},
  branch (some 11) {twig {11} {leaf ∅}},
  branch (none) {twig {-9, -4} {leaf {13}},
   twig {-14, 1} {leaf {13}},
   twig {-9, 1} {leaf {8}},
   twig {-4, 1} {leaf {3}},
   twig {-14, 6} {leaf {8}},
   twig {1, 6} {leaf {-7}},
   twig {-14, 11} {leaf {3}},
   twig {-9, 11} {leaf {-2}},
   twig {-4, 11} {leaf {-7}},
   twig {1, 11} {leaf {-12}},
   twig {-14} {leaf {-7}, leaf {-12, -2}, leaf {-2, 8}, leaf {3, 8}, leaf {-12, 13}, leaf {-2, 3, 13}},
   twig {-9} {leaf {-7, -2}, leaf {3}, leaf {-7, 8}, leaf {-2, 13}, leaf {-12, 8, 13}},
   twig {-4} {leaf {8}, leaf {-2}, leaf {-7, 3}, leaf {-12, 3, 13}},
   twig {1} {leaf {-2}, leaf {-7, 8}, leaf {-12, 13}, leaf {-7, 3}, leaf {-12, 3, 8}, leaf {-7, 13}},
   twig {6} {leaf {-12}, leaf {3}, leaf {-7, 13}, leaf {-2}, leaf {-7, 8}},
   twig {11} {leaf {3, 8}, leaf {-2, 13}, leaf {-7, -2}, leaf {-7, 3}, leaf {-12, -2, 3}, leaf {-12, -7, 8}, leaf {-12, 13}}}}}
  | .nextToNearestNeighbor =>
    root {trunk (some (-13)) {branch (some (-13)) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {1, 6}, leaf {-9, 11}, leaf {1, 11}, leaf {-4, 6, 11}}},
  branch (some (-8)) {twig {-3} {leaf ∅}},
  branch (some (-3)) {twig {7} {leaf ∅}},
  branch (some 2) {twig ∅ {leaf {11}}},
  branch (some 7) {twig ∅ {leaf {6}}},
  branch (some 12) {twig ∅ {leaf {1}}}},
 trunk (some (-8)) {branch (some (-8)) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-4, 6}, leaf {1, 6}, leaf {-4, 1, 11}, leaf {-9, 6, 11}}},
  branch (some (-3)) {twig {2} {leaf ∅}, twig ∅ {leaf {11}}},
  branch (some 2) {twig {12} {leaf ∅}, twig ∅ {leaf {6}}},
  branch (some 7) {twig ∅ {leaf {1}}},
  branch (some 12) {twig ∅ {leaf {-4}}}},
 trunk (some (-3)) {branch (some (-3)) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {1}, leaf {-9, 6}, leaf {-4, 11}}},
  branch (some 2) {twig {7} {leaf ∅}},
  branch (some (-8)) {twig {-13} {leaf ∅}, twig ∅ {leaf {11}}},
  branch (some 7) {twig ∅ {leaf {-4}}},
  branch (some 12) {twig ∅ {leaf {-9}}}},
 trunk (some 2) {branch (some 2) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-4, 1}, leaf {-4, 6}, leaf {-9, 1, 6}, leaf {-9, -4, 11}}},
  branch (some (-13)) {twig ∅ {leaf {11}}},
  branch (some (-8)) {twig ∅ {leaf {6}}},
  branch (some (-3)) {twig {-8} {leaf ∅}, twig ∅ {leaf {1}}},
  branch (some 7) {twig {12} {leaf ∅}, twig ∅ {leaf {-9}}}},
 trunk (some 7) {branch (some 7) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-9, 1}, leaf {-4, 1}, leaf {-9, -4, 6}, leaf {-9, 11}}},
  branch (some (-13)) {twig ∅ {leaf {6}}},
  branch (some (-8)) {twig ∅ {leaf {1}}},
  branch (some (-3)) {twig {-13} {leaf ∅}, twig ∅ {leaf {-4}}},
  branch (some 2) {twig {-3} {leaf ∅}, twig ∅ {leaf {-9}}}},
 trunk (some 12) {branch (some 12) {twig ∅ {leaf ∅}},
  branch (none) {twig ∅ {leaf {-4}, leaf {-9, 6}}},
  branch (some 2) {twig {-8} {leaf ∅}},
  branch (some 7) {twig {2} {leaf ∅}},
  branch (some (-13)) {twig ∅ {leaf {1}}},
  branch (some (-3)) {twig ∅ {leaf {-9}}}},
 trunk (none) {branch (some (-13)) {twig {-13} {leaf ∅}},
  branch (some (-8)) {twig {-8} {leaf ∅}},
  branch (some (-3)) {twig {-3} {leaf ∅}},
  branch (some 2) {twig {2} {leaf ∅}},
  branch (some 7) {twig {7} {leaf ∅}},
  branch (some 12) {twig {12} {leaf ∅}},
  branch (none) {twig {-8, -3} {leaf {11}},
   twig {-13, 2} {leaf {11}},
   twig {-8, 2} {leaf {6}},
   twig {-13, 7} {leaf {6}},
   twig {-8, 7} {leaf {1}},
   twig {-3, 7} {leaf {-4}},
   twig {2, 7} {leaf {-9}},
   twig {-13, 12} {leaf {1}},
   twig {-3, 12} {leaf {-9}},
   twig {2} {leaf {-4}, leaf {1}, leaf {-9, 11}},
   twig {-13} {leaf {-9, -4}, leaf {1, 6}, leaf {-9, 11}, leaf {1, 11}, leaf {-4, 6, 11}},
   twig {-8} {leaf {-4}, leaf {-9, 1}, leaf {1, 6}, leaf {-9, 6, 11}},
   twig {-3} {leaf {6}, leaf {1}, leaf {-4, 11}},
   twig {7} {leaf {1, 6}, leaf {-4, 11}, leaf {-9, 1}, leaf {-4, 1}, leaf {-9, -4, 6}, leaf {-9, 11}},
   twig {12} {leaf {6}, leaf {1, 11}, leaf {-4}}}}}

set_option maxRecDepth 2000 in
lemma mem_irreducibleTree :
    ∀ I, ∀ T ∈ ({μ, β, Λ, W2, W4, K1, K2, W1} : Finset PotentialTerm),
    ∀ x ∈ (irreducibleElems I T).map (fromChargeProfile T), (irreducibleTree I).SupersetOfMem x := by
  decide


end Charges

end SU5U1

end FTheory
