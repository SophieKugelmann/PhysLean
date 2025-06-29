/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.IsComplete
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.PhenoConstrained
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.PhenoInsertQ10
import PhysLean.StringTheory.FTheory.SU5U1.Charges.PhenoConstrained.Elems.PhenoInsertQ5
/-!

# Complete of `nonPhenoConstrainedCharges I`

We show that the `nonPhenoConstrainedCharges I` is complete, that is,
it contains every charge in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`
which is not pheno-constrained, permits a top yukawa and is complete.

## Method

The method of our proof is the following.

1. We define `completionTopYukawa` which contains all `completions` of elements
  which minimally allow the top Yukawa, which are not pheno-constrained. We show
  that every charge in `ofFinset I.allowedBarFiveCharges I.allowedTenCharges`
  which is not pheno-constrained and complete must contain an element
  of `completionTopYukawaSame` as a subset.
2. We show that `completionTopYukawa I` is a subset of `nonPhenoConstrainedCharges I`.
3. We then use the fact that one can not add to any charge in `nonPhenoConstrainedCharges`
  another `Q5` or `Q10` without remaining in `nonPhenoConstrainedCharges` or allowing
  a pheno-constraining term to be present.

This proof of completeness is more like a certification of completeness, rather
than a constructive proof.

## Key results

- `not_isPhenoConstrained_iff_mem_nonPhenoConstrainedCharge` which specifies
  the completeness of the tree of charges `nonPhenoConstrainedCharges I`.
-/
namespace FTheory

namespace SU5U1

variable {I : CodimensionOneConfig}

namespace Charges
open SuperSymmetry.SU5
open SuperSymmetry.SU5.Charges
open PotentialTerm
open CodimensionOneConfig

open PhysLean Tree

set_option maxRecDepth 2000

lemma nonPhenoConstrainedCharges_insertQ10_filter (I : CodimensionOneConfig) :
    ∀ (q10 : { x // x ∈ I.allowedTenCharges }),
      Multiset.filter (fun x => ¬ IsPhenoConstrained x)
      ((nonPhenoConstrainedCharges I).uniqueMap4 (insert q10.1)).toMultiset = ∅ := by
  intro ⟨q10, hq10⟩
  simp only [Multiset.empty_eq_zero]
  rw [Multiset.filter_eq_nil]
  intro C hC
  intro hn
  have hmemP : C ∈ (phenoInsertQ10 (nonPhenoConstrainedCharges I) q10) := by
    rw [← FourTree.mem_iff_mem_toMultiset] at hC
    obtain ⟨qHd, qHu, Q5, Q10, rfl, h1⟩ := FourTree.exists_of_mem_uniqueMap4 (insert q10) C hC
    apply mem_phenoInsertQ10_of_mem_allowsTerm
    · exact hC
    simp [IsPhenoConstrained] at hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, Q5, insert q10 Q10) K2 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, Q5, insert q10 Q10) Λ:= by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, Q5, insert q10 Q10) W1 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, Q5, insert q10 Q10) K1 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, Q5, insert q10 Q10) W2 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
  have hemp : (phenoInsertQ10 (nonPhenoConstrainedCharges I) q10).toMultiset = ∅ := by
    rw [Multiset.empty_eq_zero, ← Multiset.card_eq_zero]
    have hx := nonPhenoConstrainedCharges_phenoInsertQ10_card_zero I q10 hq10
    rw [← hx]
    rw [FourTree.card_eq_toMultiset_card]
  rw [FourTree.mem_iff_mem_toMultiset] at hmemP
  simp_all

lemma nonPhenoConstrainedCharges_insertQ5_filter (I : CodimensionOneConfig) :
    ∀ (q5 : { x // x ∈ I.allowedBarFiveCharges }),
      Multiset.filter (fun x => ¬ IsPhenoConstrained x)
      ((nonPhenoConstrainedCharges I).uniqueMap3 (insert q5.1)).toMultiset = ∅ := by
  intro ⟨q5, hq5⟩
  simp only [Multiset.empty_eq_zero]
  rw [Multiset.filter_eq_nil]
  intro C hC
  intro hn
  have hmemP : C ∈ (phenoInsertQ5 (nonPhenoConstrainedCharges I) q5) := by
    rw [← FourTree.mem_iff_mem_toMultiset] at hC
    obtain ⟨qHd, qHu, Q5, Q10, rfl, h1⟩ := FourTree.exists_of_mem_uniqueMap3 _ C hC
    apply mem_phenoInsertQ5_of_mem_allowsTerm
    · exact hC
    simp [IsPhenoConstrained] at hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, insert q5 Q5, Q10) β := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, insert q5 Q5, Q10) W4 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, insert q5 Q5, Q10) W1 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, insert q5 Q5, Q10) K1 := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
    · by_contra hc
      have hc' : AllowsTerm (qHd, qHu, insert q5 Q5, Q10) Λ := by
        apply allowsTerm_mono _ hc
        simp [Subset]
      simp_all
  have hemp : (Tree.phenoInsertQ5 (nonPhenoConstrainedCharges I) q5).toMultiset = ∅ := by
    rw [Multiset.empty_eq_zero, ← Multiset.card_eq_zero]
    have hx := nonPhenoConstrainedCharges_phenoInsertQ5_card_zero I q5 hq5
    rw [← hx]
    rw [FourTree.card_eq_toMultiset_card]
  rw [FourTree.mem_iff_mem_toMultiset] at hmemP
  simp_all

/--
The tree of charges which contains all `completions` of
charges which minimally allow the top Yukawa,
which are not pheno-constrained.

This can be constructed via

#eval FourTree.fromMultiset <|
    ((minimallyAllowsTermsOfFinset same.allowedBarFiveCharges
        same.allowedTenCharges topYukawa).bind <|
      completions same.allowedBarFiveCharges same.allowedTenCharges).dedup.filter
    fun x => ¬ IsPhenoConstrained x
-/
private def completionTopYukawa (I : CodimensionOneConfig) :
    FourTree (Option ℤ) (Option ℤ) (Finset ℤ) (Finset ℤ) :=
  match I with
  | same => root {trunk (some 3) {branch (some (-2)) {twig {-3} {leaf {-2, 0}},
      twig {-1} {leaf {-2, 0}, leaf {-3, 1}},
      twig {0} {leaf {-3, 1}},
      twig {3} {leaf {-2, 0}, leaf {-3, 1}}},
      branch (some (-1)) {twig {-3} {leaf {-3, 2}},
      twig {-2} {leaf {-3, 2}},
      twig {0} {leaf {-3, 2}},
      twig {1} {leaf {-3, 2}},
      twig {2} {leaf {-3, 2}},
      twig {3} {leaf {-3, 2}}},
      branch (some 0) {twig {-2} {leaf {0}},
      twig {-1} {leaf {0}},
      twig {1} {leaf {0}},
      twig {2} {leaf {0}},
      twig {3} {leaf {0}, leaf {-2, 2}}},
      branch (some 1) {twig {-3} {leaf {-2, 3}},
      twig {-2} {leaf {-2, 3}},
      twig {0} {leaf {-2, 3}},
      twig {2} {leaf {-2, 3}},
      twig {3} {leaf {0, 1}, leaf {-2, 3}}},
      branch (some 2) {twig {-2} {leaf {1}},
      twig {-1} {leaf {1}},
      twig {0} {leaf {1}},
      twig {-3} {leaf {0, 2}},
      twig {3} {leaf {1}, leaf {0, 2}}}},
    trunk (some (-3)) {branch (some (-2)) {twig {0} {leaf {-1}},
      twig {1} {leaf {-1}},
      twig {2} {leaf {-1}},
      twig {-3} {leaf {-1}, leaf {-2, 0}},
      twig {3} {leaf {-2, 0}}},
      branch (some (-1)) {twig {-3} {leaf {-1, 0}, leaf {-3, 2}},
      twig {-2} {leaf {-3, 2}},
      twig {0} {leaf {-3, 2}},
      twig {2} {leaf {-3, 2}},
      twig {3} {leaf {-3, 2}}},
      branch (some 0) {twig {-2} {leaf {0}},
      twig {-1} {leaf {0}},
      twig {1} {leaf {0}},
      twig {2} {leaf {0}},
      twig {-3} {leaf {0}, leaf {-2, 2}}},
      branch (some 1) {twig {-3} {leaf {-2, 3}},
      twig {-2} {leaf {-2, 3}},
      twig {-1} {leaf {-2, 3}},
      twig {0} {leaf {-2, 3}},
      twig {2} {leaf {-2, 3}},
      twig {3} {leaf {-2, 3}}},
      branch (some 2) {twig {3} {leaf {0, 2}},
      twig {-3} {leaf {0, 2}, leaf {-1, 3}},
      twig {0} {leaf {-1, 3}},
      twig {1} {leaf {0, 2}, leaf {-1, 3}}}},
    trunk (some 0) {branch (some (-3)) {twig {-1} {leaf {-2, -1}}, twig {0} {leaf {-2, -1}},
        twig {2} {leaf {-2, -1}}},
      branch (some (-2)) {twig {-3} {leaf {-1}},
      twig {1} {leaf {-1}},
      twig {2} {leaf {-1}},
      twig {-1} {leaf {-1}, leaf {-3, 1}},
      twig {0} {leaf {-1}, leaf {-3, 1}},
      twig {3} {leaf {-3, 1}}},
      branch (some (-1)) {twig {-3} {leaf {-3, 2}},
      twig {0} {leaf {-3, 2}},
      twig {1} {leaf {-3, 2}},
      twig {2} {leaf {-3, 2}},
      twig {3} {leaf {-3, 2}}},
      branch (some 1) {twig {-3} {leaf {-2, 3}},
      twig {-2} {leaf {-2, 3}},
      twig {-1} {leaf {-2, 3}},
      twig {0} {leaf {-2, 3}},
      twig {3} {leaf {-2, 3}}},
      branch (some 2) {twig {-2} {leaf {1}},
      twig {-1} {leaf {1}},
      twig {3} {leaf {1}},
      twig {-3} {leaf {-1, 3}},
      twig {0} {leaf {1}, leaf {-1, 3}},
      twig {1} {leaf {1}, leaf {-1, 3}}},
      branch (some 3) {twig {-2} {leaf {1, 2}}, twig {0} {leaf {1, 2}}, twig {1} {leaf {1, 2}}}},
    trunk (some (-2)) {branch (some (-3)) {twig {0} {leaf {-2, -1}},
      twig {-2} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}},
      twig {1} {leaf {-3, 0}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
      branch (some (-1)) {twig {-3} {leaf {-1, 0}, leaf {-3, 2}},
      twig {-2} {leaf {-2, 1}, leaf {-3, 2}},
      twig {1} {leaf {-3, 2}},
      twig {2} {leaf {-3, 2}},
      twig {3} {leaf {-3, 2}}},
      branch (some 0) {twig {-3} {leaf {0}},
      twig {3} {leaf {0}},
      twig {-2} {leaf {0}, leaf {-3, 3}},
      twig {-1} {leaf {0}, leaf {-3, 3}},
      twig {1} {leaf {0}, leaf {-3, 3}}},
      branch (some 1) {twig {-3} {leaf {-2, 3}},
      twig {-2} {leaf {-2, 3}},
      twig {-1} {leaf {-2, 3}},
      twig {0} {leaf {-2, 3}},
      twig {2} {leaf {-1, 2}, leaf {-2, 3}},
      twig {3} {leaf {-2, 3}}},
      branch (some 2) {twig {-2} {leaf {1}},
      twig {-1} {leaf {1}},
      twig {3} {leaf {1}},
      twig {-3} {leaf {-1, 3}},
      twig {0} {leaf {1}, leaf {-1, 3}},
      twig {1} {leaf {1}, leaf {-1, 3}}},
      branch (some 3) {twig {0} {leaf {1, 2}},
      twig {-2} {leaf {1, 2}, leaf {0, 3}},
      twig {-1} {leaf {0, 3}},
      twig {1} {leaf {1, 2}, leaf {0, 3}},
      twig {2} {leaf {0, 3}}}},
    trunk (some (-1)) {branch (some (-3)) {twig {0} {leaf {-2, -1}},
      twig {-2} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}},
      twig {1} {leaf {-3, 0}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
      branch (some (-2)) {twig {1} {leaf {-1}},
      twig {2} {leaf {-1}},
      twig {-1} {leaf {-1}, leaf {-2, 0}, leaf {-3, 1}},
      twig {0} {leaf {-1}, leaf {-3, 1}},
      twig {3} {leaf {-2, 0}, leaf {-3, 1}}},
      branch (some 0) {twig {-3} {leaf {0}, leaf {-2, 2}},
      twig {3} {leaf {0}, leaf {-2, 2}},
      twig {-2} {leaf {0}, leaf {-3, 3}},
      twig {-1} {leaf {0}, leaf {-3, 3}},
      twig {2} {leaf {0}, leaf {-3, 3}}},
      branch (some 1) {twig {-3} {leaf {-2, 3}},
      twig {-2} {leaf {-2, 3}},
      twig {-1} {leaf {-2, 3}},
      twig {0} {leaf {-2, 3}},
      twig {2} {leaf {-1, 2}, leaf {-2, 3}}},
      branch (some 2) {twig {-2} {leaf {1}},
      twig {-1} {leaf {1}},
      twig {0} {leaf {1}},
      twig {-3} {leaf {0, 2}},
      twig {1} {leaf {1}, leaf {0, 2}},
      twig {3} {leaf {1}, leaf {0, 2}}},
      branch (some 3) {twig {0} {leaf {1, 2}},
      twig {-2} {leaf {1, 2}, leaf {0, 3}},
      twig {-1} {leaf {0, 3}},
      twig {1} {leaf {1, 2}, leaf {0, 3}},
      twig {2} {leaf {0, 3}}}},
    trunk (some 1) {branch (some (-3)) {twig {0} {leaf {-2, -1}},
      twig {-2} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}},
      twig {1} {leaf {-3, 0}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
      branch (some (-2)) {twig {0} {leaf {-1}},
      twig {1} {leaf {-1}},
      twig {2} {leaf {-1}},
      twig {-3} {leaf {-1}, leaf {-2, 0}},
      twig {-1} {leaf {-1}, leaf {-2, 0}},
      twig {3} {leaf {-2, 0}}},
      branch (some (-1)) {twig {-2} {leaf {-2, 1}, leaf {-3, 2}},
      twig {0} {leaf {-3, 2}},
      twig {1} {leaf {-3, 2}},
      twig {2} {leaf {-3, 2}},
      twig {3} {leaf {-3, 2}}},
      branch (some 0) {twig {-3} {leaf {0}, leaf {-2, 2}},
      twig {3} {leaf {0}, leaf {-2, 2}},
      twig {-2} {leaf {0}, leaf {-3, 3}},
      twig {1} {leaf {0}, leaf {-3, 3}},
      twig {2} {leaf {0}, leaf {-3, 3}}},
      branch (some 2) {twig {-2} {leaf {1}},
      twig {-1} {leaf {1}},
      twig {-3} {leaf {0, 2}, leaf {-1, 3}},
      twig {0} {leaf {1}, leaf {-1, 3}},
      twig {1} {leaf {1}, leaf {0, 2}, leaf {-1, 3}}},
      branch (some 3) {twig {0} {leaf {1, 2}},
      twig {-2} {leaf {1, 2}, leaf {0, 3}},
      twig {-1} {leaf {0, 3}},
      twig {1} {leaf {1, 2}, leaf {0, 3}},
      twig {2} {leaf {0, 3}}}},
    trunk (some 2) {branch (some (-3)) {twig {0} {leaf {-2, -1}},
      twig {-2} {leaf {-3, 0}},
      twig {-1} {leaf {-2, -1}, leaf {-3, 0}},
      twig {1} {leaf {-3, 0}},
      twig {2} {leaf {-2, -1}, leaf {-3, 0}}},
      branch (some (-2)) {twig {-3} {leaf {-1}},
      twig {1} {leaf {-1}},
      twig {2} {leaf {-1}},
      twig {-1} {leaf {-1}, leaf {-3, 1}},
      twig {0} {leaf {-1}, leaf {-3, 1}},
      twig {3} {leaf {-3, 1}}},
      branch (some (-1)) {twig {-3} {leaf {-3, 2}},
      twig {-2} {leaf {-2, 1}, leaf {-3, 2}},
      twig {0} {leaf {-3, 2}},
      twig {1} {leaf {-3, 2}},
      twig {2} {leaf {-3, 2}},
      twig {3} {leaf {-3, 2}}},
      branch (some 0) {twig {-3} {leaf {0}},
      twig {3} {leaf {0}},
      twig {-1} {leaf {0}, leaf {-3, 3}},
      twig {1} {leaf {0}, leaf {-3, 3}},
      twig {2} {leaf {0}, leaf {-3, 3}}},
      branch (some 1) {twig {-3} {leaf {-2, 3}},
      twig {-2} {leaf {-2, 3}},
      twig {-1} {leaf {-2, 3}},
      twig {2} {leaf {-1, 2}, leaf {-2, 3}},
      twig {3} {leaf {0, 1}, leaf {-2, 3}}},
      branch (some 3) {twig {0} {leaf {1, 2}},
      twig {-2} {leaf {1, 2}, leaf {0, 3}},
      twig {-1} {leaf {0, 3}},
      twig {1} {leaf {1, 2}, leaf {0, 3}},
      twig {2} {leaf {0, 3}}}}}
  | nearestNeighbor => root {trunk (some (-9)) {branch (some (-14)) {twig {-4} {leaf {-7}},
      twig {1} {leaf {-7}},
      twig {6} {leaf {-7}},
      twig {-9} {leaf {-7}, leaf {-12, -2}},
      twig {11} {leaf {-7}, leaf {-12, -2}}},
      branch (some (-4)) {twig {-14} {leaf {-2}, leaf {-12, 8}},
        twig {-9} {leaf {-2}, leaf {-12, 8}}, twig {11} {leaf {-2}, leaf {-12, 8}}},
      branch (some 1) {twig {-9} {leaf {-12, 13}}, twig {-4} {leaf {-12, 13}}},
      branch (some 6) {twig {-9} {leaf {-2, 8}, leaf {-7, 13}}, twig {-4} {leaf {-7, 13}},
        twig {11} {leaf {-2, 8}, leaf {-7, 13}}}},
    trunk (some 11) {branch (some (-14)) {twig {-4} {leaf {-7}},
      twig {1} {leaf {-7}},
      twig {6} {leaf {-7}},
      twig {-9} {leaf {-7}, leaf {-12, -2}},
      twig {11} {leaf {-7}, leaf {-12, -2}}},
      branch (some (-9)) {twig {-14} {leaf {-12, 3}}, twig {-4} {leaf {-12, 3}},
        twig {1} {leaf {-12, 3}}, twig {11} {leaf {-12, 3}}},
      branch (some (-4)) {twig {-14} {leaf {-2}, leaf {-12, 8}},
      twig {-9} {leaf {-2}, leaf {-12, 8}},
      twig {1} {leaf {-12, 8}},
      twig {11} {leaf {-2}, leaf {-12, 8}}},
      branch (some 1) {twig {-14} {leaf {-2, 3}}, twig {11} {leaf {-2, 3}, leaf {-7, 8}}},
      branch (some 6) {twig {-14} {leaf {3}},
      twig {-9} {leaf {-2, 8}, leaf {-7, 13}},
      twig {-4} {leaf {3}, leaf {-7, 13}},
      twig {11} {leaf {3}, leaf {-2, 8}, leaf {-7, 13}}}},
    trunk (some 6) {branch (some (-14)) {twig {-9} {leaf {-7}}, twig {-4} {leaf {-7}},
        twig {1} {leaf {-7}}, twig {6} {leaf {-7}}, twig {11} {leaf {-7}}},
      branch (some (-4)) {twig {-9} {leaf {-12, 8}}, twig {1} {leaf {-12, 8}},
        twig {11} {leaf {-12, 8}}},
      branch (some 1) {twig {-9} {leaf {-12, 13}}},
      branch (some 11) {twig {1} {leaf {3, 8}}}},
    trunk (some (-14)) {branch (some (-9)) {twig {-14} {leaf {-12, 3}},
      twig {1} {leaf {-12, 3}}, twig {11} {leaf {-12, 3}}},
      branch (some (-4)) {twig {-14} {leaf {-2}, leaf {-12, 8}},
      twig {-9} {leaf {-2}, leaf {-12, 8}},
      twig {1} {leaf {-12, 8}},
      twig {11} {leaf {-2}, leaf {-12, 8}}},
      branch (some 1) {twig {-14} {leaf {-2, 3}}, twig {11} {leaf {-2, 3}, leaf {-7, 8}}},
      branch (some 6) {twig {-14} {leaf {3}},
      twig {1} {leaf {3}},
      twig {-9} {leaf {-7, 13}},
      twig {-4} {leaf {3}, leaf {-7, 13}},
      twig {11} {leaf {3}, leaf {-7, 13}}}, branch (some 11) {twig {-14} {leaf {-2, 13}}}},
    trunk (some (-4)) {branch (some (-14)) {twig {-4} {leaf {-7}},
      twig {1} {leaf {-7}},
      twig {6} {leaf {-7}},
      twig {-9} {leaf {-7}, leaf {-12, -2}},
      twig {11} {leaf {-7}, leaf {-12, -2}}},
      branch (some (-9)) {twig {-4} {leaf {-12, 3}}, twig {1} {leaf {-12, 3}},
        twig {11} {leaf {-12, 3}}},
      branch (some 1) {twig {11} {leaf {-7, 8}}, twig {-9} {leaf {-12, 13}},
        twig {-4} {leaf {-12, 13}}},
      branch (some 6) {twig {-14} {leaf {3}},
      twig {1} {leaf {3}},
      twig {-9} {leaf {-7, 13}},
      twig {-4} {leaf {3}, leaf {-7, 13}},
      twig {11} {leaf {3}, leaf {-7, 13}}}, branch (some 11) {twig {1} {leaf {3, 8}},
        twig {-14} {leaf {-2, 13}}}},
    trunk (some 1) {branch (some (-14)) {twig {-4} {leaf {-7}},
      twig {1} {leaf {-7}},
      twig {6} {leaf {-7}},
      twig {-9} {leaf {-7}, leaf {-12, -2}},
      twig {11} {leaf {-7}, leaf {-12, -2}}},
      branch (some (-9)) {twig {-14} {leaf {-12, 3}}, twig {-4} {leaf {-12, 3}},
        twig {1} {leaf {-12, 3}}, twig {11} {leaf {-12, 3}}},
      branch (some (-4)) {twig {-14} {leaf {-2}, leaf {-12, 8}}, twig {1} {leaf {-12, 8}},
        twig {11} {leaf {-2}, leaf {-12, 8}}},
      branch (some 6) {twig {-14} {leaf {3}}, twig {-4} {leaf {3}},
        twig {1} {leaf {3}}, twig {-9} {leaf {-2, 8}}},
      branch (some 11) {twig {1} {leaf {3, 8}}, twig {-14} {leaf {-2, 13}}}}}
  | nextToNearestNeighbor => root {trunk (some 12) {branch (some (-8)) {twig {-13} {leaf {-9, 1}},
    twig {12} {leaf {-9, 1}}},
  branch (some 2) {twig {-13} {leaf {1}}, twig {7} {leaf {1}}, twig {-3} {leaf {-9, 11}},
    twig {12} {leaf {1}, leaf {-9, 11}}}},
  trunk (some (-13)) {branch (some (-8)) {twig {7} {leaf {-4}},
    twig {-13} {leaf {-4}, leaf {-9, 1}},
    twig {12} {leaf {-9, 1}}},
  branch (some (-3)) {twig {-13} {leaf {-4, 1}, leaf {-9, 6}}, twig {-8} {leaf {-9, 6}},
    twig {2} {leaf {-9, 6}}},
  branch (some 2) {twig {-8} {leaf {1}}, twig {12} {leaf {1}}, twig {-13} {leaf {1}, leaf {-4, 6}},
    twig {7} {leaf {1}, leaf {-4, 6}}},
  branch (some 7) {twig {-13} {leaf {-4, 11}}},
  branch (some 12) {twig {-13} {leaf {6}}, twig {-8} {leaf {6}}, twig {2} {leaf {6}},
    twig {7} {leaf {6}}}},
  trunk (some (-3)) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some (-8)) {twig {-3} {leaf {-4}}, twig {7} {leaf {-4}}},
  branch (some 2) {twig {-13} {leaf {-4, 6}}, twig {-8} {leaf {-9, 11}}, twig {-3} {leaf {-9, 11}},
    twig {12} {leaf {-9, 11}}},
  branch (some 12) {twig {-13} {leaf {6}}, twig {-8} {leaf {6}}, twig {2} {leaf {6}},
    twig {7} {leaf {6}}}},
  trunk (some (-8)) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some (-3)) {twig {-13} {leaf {-4, 1}, leaf {-9, 6}}, twig {-8} {leaf {-9, 6}},
    twig {7} {leaf {-9, 6}}},
  branch (some 2) {twig {-13} {leaf {1}}, twig {7} {leaf {1}}, twig {-8} {leaf {1}, leaf {-9, 11}},
    twig {-3} {leaf {-9, 11}}},
  branch (some 7) {twig {-13} {leaf {-4, 11}}},
  branch (some 12) {twig {-13} {leaf {6}}, twig {2} {leaf {6}}, twig {-8} {leaf {6}, leaf {1, 11}},
    twig {7} {leaf {6}, leaf {1, 11}}}},
  trunk (some 2) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some (-8)) {twig {-3} {leaf {-4}}, twig {7} {leaf {-4}},
    twig {-13} {leaf {-4}, leaf {-9, 1}}, twig {12} {leaf {-9, 1}}},
  branch (some (-3)) {twig {-13} {leaf {-9, 6}}, twig {2} {leaf {-9, 6}}, twig {7} {leaf {-9, 6}}},
  branch (some 7) {twig {-13} {leaf {-4, 11}}},
  branch (some 12) {twig {-13} {leaf {6}}, twig {2} {leaf {6}}, twig {-8} {leaf {6}, leaf {1, 11}},
    twig {7} {leaf {6}, leaf {1, 11}}}},
  trunk (some 7) {branch (some (-13)) {twig {-3} {leaf {-9, -4}}, twig {7} {leaf {-9, -4}}},
  branch (some (-8)) {twig {-13} {leaf {-4}}, twig {-3} {leaf {-4}}, twig {7} {leaf {-4}}},
  branch (some (-3)) {twig {-8} {leaf {-9, 6}}, twig {2} {leaf {-9, 6}}, twig {7} {leaf {-9, 6}}},
  branch (some 2) {twig {-8} {leaf {1}}, twig {12} {leaf {1}}, twig {-13} {leaf {1}, leaf {-4, 6}},
    twig {7} {leaf {1}, leaf {-4, 6}}},
  branch (some 12) {twig {-13} {leaf {6}}, twig {2} {leaf {6}}, twig {-8} {leaf {6}, leaf {1, 11}},
    twig {7} {leaf {6}, leaf {1, 11}}}}}

lemma completionTopYukawa_complete_of_same :
    ∀ x ∈ (minimallyAllowsTermsOfFinset CodimensionOneConfig.same.allowedBarFiveCharges
      CodimensionOneConfig.same.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions same.allowedBarFiveCharges same.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa .same := by
  decide

lemma completionTopYukawa_complete_of_nearestNeighbor :
    ∀ x ∈ (minimallyAllowsTermsOfFinset
      CodimensionOneConfig.nearestNeighbor.allowedBarFiveCharges
      CodimensionOneConfig.nearestNeighbor.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nearestNeighbor.allowedBarFiveCharges
      nearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa .nearestNeighbor := by
  decide

lemma completionTopYukawa_complete_of_nextToNearestNeighbor :
    ∀ x ∈ (minimallyAllowsTermsOfFinset
      CodimensionOneConfig.nextToNearestNeighbor.allowedBarFiveCharges
      CodimensionOneConfig.nextToNearestNeighbor.allowedTenCharges topYukawa),
    ¬ x.IsPhenoConstrained →
    ∀ y ∈ completions nextToNearestNeighbor.allowedBarFiveCharges
      nextToNearestNeighbor.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa .nextToNearestNeighbor := by
  decide

lemma completionTopYukawa_complete {I : CodimensionOneConfig} (x : Charges)
    (hx : x ∈ (minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
      I.allowedTenCharges topYukawa))
    (hPheno : ¬ x.IsPhenoConstrained) :
    ∀ y ∈ completions I.allowedBarFiveCharges I.allowedTenCharges x, ¬ y.IsPhenoConstrained
    → y ∈ completionTopYukawa I := by
  cases I
  case same => exact completionTopYukawa_complete_of_same x hx hPheno
  case nearestNeighbor => exact completionTopYukawa_complete_of_nearestNeighbor x hx hPheno
  case nextToNearestNeighbor => exact
    completionTopYukawa_complete_of_nextToNearestNeighbor x hx hPheno

set_option maxRecDepth 2000 in
lemma exists_subset_completionTopYukawa_of_not_isPhenoConstrained {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (htopYukawa : AllowsTerm x topYukawa)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) : ∃ (y : Charges), y ∈ completionTopYukawa I ∧ y ⊆ x := by
  have hIrreducible :
        ∃ y ∈ (minimallyAllowsTermsOfFinset I.allowedBarFiveCharges
        I.allowedTenCharges topYukawa), y ⊆ x := by
      rw [allowsTerm_iff_subset_minimallyAllowsTerm] at htopYukawa
      obtain ⟨y, hPower, hIrre⟩ := htopYukawa
      use y
      constructor
      · rw [← minimallyAllowsTerm_iff_mem_minimallyAllowsTermOfFinset]
        · exact hIrre
        · simp at hPower
          exact mem_ofFinset_antitone I.allowedBarFiveCharges I.allowedTenCharges hPower hsub
      · simpa using hPower
  obtain ⟨y, hyMem, hysubsetx⟩ := hIrreducible
  obtain ⟨z, hz1, hz2⟩ := exist_completions_subset_of_complete
    I.allowedBarFiveCharges I.allowedTenCharges y x hysubsetx hsub hcomplete
  use z
  constructor
  · refine completionTopYukawa_complete y hyMem ?_ z hz1 ?_
    · by_contra hn
      have h' := isPhenoConstrained_mono hysubsetx hn
      simp_all
    · by_contra hn
      have h' := isPhenoConstrained_mono hz2 hn
      simp_all
  · simp_all

set_option maxRecDepth 2000 in
lemma completionTopYukawa_subset_nonPhenoConstrainedCharges :
    ∀ x ∈ (completionTopYukawa I).toMultiset, x ∈ nonPhenoConstrainedCharges I := by
  decide +revert

set_option maxRecDepth 2000 in
lemma not_isPhenoConstrained_mem_nonPhenoConstrainedCharges {x : Charges}
    (hx : ¬ x.IsPhenoConstrained)
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges)
    (hcomplete : IsComplete x) :
    x ∉ nonPhenoConstrainedCharges I → ¬ (¬ IsPhenoConstrained x ∧
      AllowsTerm x topYukawa) := by
  by_cases hn : ¬ (AllowsTerm x topYukawa)
  · simp [hn]
  simp only [not_and, hn, imp_false]
  simp at hn
  obtain ⟨y, y_mem, hyx⟩ :=
    exists_subset_completionTopYukawa_of_not_isPhenoConstrained hx hn hsub hcomplete
  refine subset_insert_filter_card_zero (nonPhenoConstrainedCharges I)
    I.allowedBarFiveCharges I.allowedTenCharges (fun x => ¬x.IsPhenoConstrained)
    ?_ ?_ y ?_ x hyx hsub ?_ ?_
  · intro x y hxy
    simp only [Decidable.not_not]
    exact fun a => isPhenoConstrained_mono hxy a
  · intro x
    rw [FourTree.mem_iff_mem_toMultiset]
    exact fun a => isComplete_of_mem_nonPhenoConstrainedCharge I x a
  · apply completionTopYukawa_subset_nonPhenoConstrainedCharges
    rw [FourTree.mem_iff_mem_toMultiset] at y_mem
    exact y_mem
  · exact nonPhenoConstrainedCharges_insertQ10_filter I
  · exact nonPhenoConstrainedCharges_insertQ5_filter I

lemma not_isPhenoConstrained_iff_mem_nonPhenoConstrainedCharge {x : Charges}
    (hsub : x ∈ ofFinset I.allowedBarFiveCharges I.allowedTenCharges) :
    AllowsTerm x topYukawa ∧
    ¬ IsPhenoConstrained x ∧ IsComplete x ↔
    x ∈ nonPhenoConstrainedCharges I := by
  constructor
  · intro ⟨hTop, hPheno, hComplete⟩
    by_contra hn
    apply not_isPhenoConstrained_mem_nonPhenoConstrainedCharges hPheno hsub hComplete hn
    simp_all
  · intro h
    rw [FourTree.mem_iff_mem_toMultiset] at h
    refine ⟨?_, ?_, ?_⟩
    · exact allowsTerm_topYukawa_of_mem_nonPhenoConstrainedCharges I x h
    · exact not_isPhenoConstrained_of_mem_nonPhenoConstrainedCharges I x h
    · exact isComplete_of_mem_nonPhenoConstrainedCharge I x h

end Charges

end SU5U1

end FTheory
