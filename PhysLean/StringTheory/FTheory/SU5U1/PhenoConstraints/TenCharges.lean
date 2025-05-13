/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.Basic
import PhysLean.StringTheory.FTheory.SU5U1.NoExotics.HyperchargeFlux
import Mathlib.Order.CompleteLattice.Finset
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.FiveBarSeven
import PhysLean.StringTheory.FTheory.SU5U1.AnomalyCancellation.Multiset
/-!

# Phenomenological constraints on the ten-dimension charges

The phenomenological constraints restrict the possible values
of the ten-dimensional charges of the matter content in
conjunction with the charge of the up-type quark through the
needed existence of a top Yukawa-term.

## Important results

The important results in this file are lemmas of the form:

`qHu_quantaTen_q_mem_of_card_..._config_...`

-/

namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace MatterContent

instance (T : Finset ℤ) (F : Finset (Multiset ℤ)) :
    Decidable (∀ s ∈ F, ¬ s ⊆ T.val) := by
  haveI x : (a : Multiset ℤ) → a ∈ F → Decidable ¬a ⊆ T.val := by
    intro a ha
    rw [Multiset.subset_iff]
    infer_instance
  apply Finset.decidableDforallFinset (_hp := x)

/-!

## Cardinialty of quantaBarFiveMatter equal to 2

-/


lemma quantaTen_q_not_mem_of_card_two_config_nearestNeighbor (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-12, -2}, {-12, 13}, {-7, -2}, {-7, 3}, {-7, 8}, {-2, 3},
      {-2, 8}, {-2, 13}, {3, 8}, {-12, -7, 13},
      {-12, 3, 13}, {-12, 8, 13}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.quantaTen.map QuantaTen.q := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

/-!

## card = three,

-/

-- {-12, -7, -2, 3, 8, 13}
lemma quantaTen_q_not_mem_of_card_three_config_nearestNeighbor (𝓜 : MatterContent .nearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-2}, {3}, {-12, 13}, {-7, 8}, {-7, 13}, {-12, -7, 13}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.quantaTen.map QuantaTen.q := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

set_option maxRecDepth 2000 in
lemma quantaTen_q_not_mem_of_card_three_config_same (𝓜 : MatterContent .same)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-3, 0}, {-3, 1}, {-3, 3}, {-2, -1}, {-2, 0}, {-2, 1}, {-2, 2},
    {-1, 0}, {-1, 1}, {-1, 2}, {-1, 3}, {0, 1}, {0, 2}, {0, 3}, {1, 2}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.quantaTen.map QuantaTen.q := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

lemma quantaTen_q_not_mem_of_card_three_config_nextToNearestNeighbor
    (𝓜 : MatterContent .nextToNearestNeighbor)
    (hcard : 𝓜.quantaBarFiveMatter.card = 3) (h : 𝓜.ProtonDecayU1Constrained) :
    ∀ S ∈ ({{-4}, {1}, {6}, {-9, 11}} : Finset (Multiset ℤ)),
    ¬ S ⊆ 𝓜.quantaTen.map QuantaTen.q := by
  intro S hS
  fin_cases hS
  all_goals
    exact 𝓜.lambdaTerm_K1Term_W1Term_subset_check hcard h _

set_option maxRecDepth 20000 in
lemma qHu_quantaTen_q_mem_of_card_three_config_same
    (𝓜 : MatterContent .same) (hcard : 𝓜.quantaBarFiveMatter.card = 3)
    (h : 𝓜.ProtonDecayU1Constrained) (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum) :
    (𝓜.qHu, 𝓜.quantaTen.map QuantaTen.q) ∈ ({(-2, {-3, -1}), (-2, {-1}), (-1, {-3, 2}),
    (0, {0}), (2, {1}), (1, {-2, 3}), (2, {1, 3})} : Finset (ℤ × Multiset ℤ)) := by
  have hmem := 𝓜.quantaTen_map_q_powerset_filter_card_three hSpec.2.1 hSpec.1
  rw [HasATopYukawa] at hTop
  have hN0 := quantaTen_q_not_mem_of_card_three_config_same 𝓜 hcard h
  rw [quantaTen_map_q_eq_toFinset] at hTop hN0 ⊢
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = T at hmem hTop hN0 ⊢
  revert T
  have hqHu := 𝓜.qHu_mem_allowedBarFiveCharges
  generalize 𝓜.qHu = Q at hqHu ⊢
  revert Q
  decide

/-!

## Generic combiniation of qHu and Ten charges

The existence of a top Yuakwa term puts constraints on the possible
values of the charges of the ten-dimensional matter content, along with the
value of the charge of the up-type quark.
-/

def phenoConstraintHuTenSet : Finset (ℤ × Finset ℤ) :=
  let prod1 := CodimensionOneConfig.same.allowedBarFiveCharges.val
  let prod2 := prod1.product (CodimensionOneConfig.same.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)).val
  (prod2.filter fun (qHu, Q10) => phenoConstraintHuTen qHu Q10.val).toFinset

def phenoConstraintHuTenSetqHuExe (qHu : ℤ) : Finset (Finset ℤ) :=
  ((phenoConstraintHuTenSet.filter (fun x => x.1 = qHu)).val.map (fun x => x.2)).toFinset

-- #eval phenoConstraintHuTenSetqHuExe 3
-- One would expect for each qHu without conditions 63 options.
def phenoConstraintHuTenSetqHu (qHu : ℤ) : Finset (Finset ℤ) :=
  if qHu = - 3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, -1, 0}, {-2, -1, 0},
    {-2, -1, 1}, {-3, 0, 1}, {-2, -1, 2}, {-3, 0, 2}, {-2, -1, 3}, {-3, 0, 3}}
  else if qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-2, 0}, {-3, -2, 0}, {-1, 0},
    {-3, -1, 0}, {-2, -1, 0}, {-3, 1}, {-3, -2, 1}, {-1, 1}, {-3, -1, 1}, {-2, -1, 1}, {-3, 0, 1},
    {-2, 0, 1}, {-1, 0, 1}, {-1, 2}, {-3, -1, 2}, {-2, -1, 2}, {-2, 0, 2}, {-1, 0, 2}, {-3, 1, 2},
    {-1, 1, 2}, {-1, 3}, {-3, -1, 3}, {-2, -1, 3}, {-2, 0, 3}, {-1, 0, 3}, {-3, 1, 3}, {-1, 1, 3},
    {-1, 2, 3}}
  else if qHu = -1 then {{-1, 0}, {-3, -1, 0}, {-2, -1, 0}, {-2, 1},  {-3, -2, 1},  {-2, -1, 1},
    {-2, 0, 1}, {-1, 0, 1}, {-3, 2},  {-3, -2, 2},  {-3, -1, 2},  {-3, 0, 2}, {-1, 0, 2},
    {-3, 1, 2}, {-2, 1, 2}, {-1, 0, 3}, {-2, 1, 3}, {-3, 2, 3}}
  else if qHu = 0 then {{0}, {-3, 0}, {-2, 0}, {-3, -2, 0}, {-1, 0}, {-3, -1, 0}, {-2, -1, 0},
    {-1, 1}, {-3, -1, 1}, {-2, -1, 1}, {0, 1}, {-3, 0, 1}, {-2, 0, 1}, {-1, 0, 1}, {-2, 2},
    {-3, -2, 2}, {-2, -1, 2}, {0, 2}, {-3, 0, 2}, {-2, 0, 2}, {-1, 0, 2}, {-2, 1, 2}, {-1, 1, 2},
    {0, 1, 2}, {-3, 3}, {-3, -2, 3}, {-3, -1, 3}, {0, 3}, {-3, 0, 3}, {-2, 0, 3}, {-1, 0, 3},
    {-3, 1, 3}, {-1, 1, 3}, {0, 1, 3}, {-3, 2, 3}, {-2, 2, 3}, {0, 2, 3}}
  else if qHu = 1 then {{0, 1}, {-3, 0, 1}, {-2, 0, 1}, {-1, 0, 1}, {-1, 2},  {-3, -1, 2},
    {-2, -1, 2}, {-1, 0, 2}, {-1, 1, 2}, {0, 1, 2}, {-2, 3}, {-3, -2, 3},  {-2, -1, 3}, {-2, 0, 3},
    {-2, 1, 3}, {0, 1, 3},  {-2, 2, 3}, {-1, 2, 3}}
  else if qHu = 2 then {{1}, {-3, 1}, {-2, 1}, {-3, -2, 1}, {-1, 1}, {-3, -1, 1}, {-2, -1, 1},
    {0, 1}, {-3, 0, 1}, {-2, 0, 1}, {-1, 0, 1}, {0, 2}, {-3, 0, 2}, {-2, 0, 2}, {-1, 0, 2}, {1, 2},
    {-3, 1, 2}, {-2, 1, 2}, {-1, 1, 2}, {0, 1, 2}, {-1, 3}, {-3, -1, 3}, {-2, -1, 3}, {-1, 0, 3},
    {1, 3}, {-3, 1, 3}, {-2, 1, 3}, {-1, 1, 3}, {0, 1, 3}, {-1, 2, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHu = 3 then {{1, 2}, {-3, 1, 2}, {-2, 1, 2}, {-1, 1, 2}, {0, 1, 2},  {0, 3}, {-3, 0, 3},
    {-2, 0, 3}, {-1, 0, 3}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}
  else ∅

#eval (phenoConstraintHuTenSetqHu (0)).card
lemma phenoConstraintHuTenSetqHu_symm_one :
    phenoConstraintHuTenSetqHu 1 = ((phenoConstraintHuTenSetqHu (-1)).val.map
    (fun x => (x.val.map (fun y => -y)).toFinset)).toFinset := by
  decide

lemma phenoConstraintHuTenSetqHu_symm_two :
    phenoConstraintHuTenSetqHu 2 = ((phenoConstraintHuTenSetqHu (-2)).val.map
    (fun x => (x.val.map (fun y => -y)).toFinset)).toFinset := by
  decide

lemma mem_phenoConstraintHuTenSetqHu
    (𝓜 : MatterContent .same) (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (hTop : 𝓜.HasATopYukawa) :
    (𝓜.quantaTen.map QuantaTen.q).toFinset ∈ phenoConstraintHuTenSetqHu 𝓜.qHu := by
  rw [HasATopYukawa] at hTop
  have hmem := 𝓜.quantaTen_map_q_powerset_filter_card_three he h3
  rw [quantaTen_map_q_eq_toFinset] at hTop ⊢
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = Q10 at *
  revert hTop
  revert Q10
  have hqHu := 𝓜.qHu_mem_allowedBarFiveCharges
  generalize 𝓜.qHu = qHu at *
  revert qHu
  decide +kernel


def phenoConstraintHuTenSetqHdHuExe (qHd qHu : ℤ) : Finset (Finset ℤ) :=
  if qHd = qHu then ∅
  else
  (phenoConstraintHuTenSetqHu qHu).filter (fun Q10 => phenoConstraintHdHuTen qHd qHu Q10.val)

-- #eval phenoConstraintHuTenSetqHdHuExe (3) 2

def phenoConstraintHuTenSetqHdHu (qHd qHu : ℤ) : Finset (Finset ℤ) :=
  if qHd = -3 ∧ qHu = - 2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-2, 0}, {-3, -2, 0},
    {-1, 0}, {-3, -1, 0}, {-2, -1, 0}, {-2, 0, 2}, {-1, 3}, {-2, -1, 3}}
  else if qHd = -3 ∧ qHu = -1 then {{-1, 0}, {-3, -1, 0}, {-2, -1, 0}, {-3, 2},
    {-3, -2, 2}, {-3, 0, 2}}
  else if qHd = -3 ∧ qHu = 0 then {{0}, {-3, 0}, {-2, 0}, {-3, -2, 0}, {-1, 0}, {-3, -1, 0},
    {-2, -1, 0}, {-2, 2}, {-3, -2, 2}, {0, 2}, {-3, 0, 2}, {-2, 0, 2}}
  else if qHd = -3 ∧ qHu = 1 then {{-2, 3}, {-2, -1, 3}}
  else if qHd = -3 ∧ qHu = 2 then {{0, 2}, {-3, 0, 2}, {-2, 0, 2}, {-1, 3}, {-2, -1, 3}}
  else if qHd = -2 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, -1, 0},
    {-2, -1, 0}, {-2, -1, 1}, {-2, -1, 3}, {-3, 0, 3}}
  else if qHd = -2 ∧ qHu = -1 then {{-1, 0}, {-3, -1, 0}, {-2, -1, 0}, {-2, 1}, {-3, -2, 1},
    {-2, -1, 1}, {-3, 2}, {-3, -1, 2}, {-3, 1, 2}}
  else if qHd = -2 ∧ qHu = 0 then {{0}, {-3, 0}, {-2, 0}, {-3, -2, 0}, {-1, 0}, {-3, -1, 0},
    {-2, -1, 0}, {-1, 1}, {-3, -1, 1}, {-2, -1, 1}, {-3, 3}, {-3, -2, 3}, {-3, -1, 3}, {0, 3},
    {-3, 0, 3}, {-2, 0, 3}, {-3, 1, 3}, {-1, 1, 3}}
  else if qHd = -2 ∧ qHu = 1 then {{-1, 2}, {-3, -1, 2}, {-2, 3}, {-3, -2, 3}, {-2, -1, 3},
    {-2, 0, 3}, {-1, 2, 3}}
  else if qHd = -2 ∧ qHu = 2 then {{1}, {-3, 1}, {-2, 1}, {-3, -2, 1}, {-1, 1}, {-3, -1, 1},
    {-2, -1, 1}, {1, 2}, {-3, 1, 2}, {-1, 3}, {-3, -1, 3}, {-2, -1, 3}, {1, 3}, {-3, 1, 3},
    {-1, 1, 3}, {-1, 2, 3}, {1, 2, 3}}
  else if qHd = -2 ∧ qHu = 3 then {{1, 2}, {-3, 1, 2}, {0, 3}, {-3, 0, 3}, {-2, 0, 3}, {1, 2, 3}}
  else if qHd = -1 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, -1, 0},
    {-2, -1, 0}, {-2, -1, 2}, {-3, 0, 3}}
  else if qHd = -1 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-2, 0}, {-3, -2, 0},
    {-1, 0}, {-3, -1, 0}, {-2, -1, 0}, {-3, 1}, {-3, -2, 1}, {-1, 2}, {-2, -1, 2}, {-2, 0, 2}}
  else if qHd = -1 ∧ qHu = 0 then {{0}, {-3, 0}, {-2, 0}, {-3, -2, 0}, {-1, 0}, {-3, -1, 0},
    {-2, -1, 0}, {-2, 2}, {-2, -1, 2}, {0, 2}, {-2, 0, 2}, {-3, 3}, {-3, -2, 3}, {0, 3},
    {-3, 0, 3}, {-2, 2, 3}, {0, 2, 3}}
  else if qHd = -1 ∧ qHu = 1 then {{-1, 2}, {-2, -1, 2}, {-2, 3}, {-3, -2, 3}, {-2, 1, 3},
    {-2, 2, 3}}
  else if qHd = -1 ∧ qHu = 2 then {{1}, {-3, 1}, {-2, 1}, {-3, -2, 1}, {0, 2}, {-2, 0, 2}, {1, 2},
    {1, 3}, {-2, 1, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHd = -1 ∧ qHu = 3 then {{1, 2}, {0, 3}, {-3, 0, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHd = 0 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}}
  else if qHd = 0 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-3, 1}, {-1, 1},
    {-3, -1, 1}, {-1, 3}, {-3, -1, 3}, {-3, 1, 3}, {-1, 1, 3}}
  else if qHd = 0 ∧ qHu = -1 then {{-3, 2}, {-3, -2, 2}, {-3, 2, 3}}
  else if qHd = 0 ∧ qHu = 1 then {{-2, 3}, {-3, -2, 3}, {-2, 2, 3}}
  else if qHd = 0 ∧ qHu = 2 then {{1}, {-3, 1}, {-1, 1}, {-3, -1, 1}, {1, 2}, {-1, 3}, {-3, -1, 3},
    {1, 3}, {-3, 1, 3}, {-1, 1, 3}, {1, 2, 3}}
  else if qHd = 0 ∧ qHu = 3 then {{1, 2}, {1, 2, 3}}
  else if qHd = 1 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, 0, 3}}
  else if qHd = 1 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-2, 0}, {-3, -2, 0},
    {-1, 2}, {-3, -1, 2}, {-2, 0, 2}, {-1, 3}, {-1, 2, 3}}
  else if qHd = 1 ∧ qHu = -1 then {{-2, 1}, {-3, 2}, {-3, -2, 2}, {-3, -1, 2}, {-2, 1, 2},
    {-3, 2, 3}}
  else if qHd = 1 ∧ qHu = 0 then {{0}, {-3, 0}, {-2, 0}, {-3, -2, 0}, {0, 1}, {-2, 2}, {-3, -2, 2},
    {0, 2}, {-2, 0, 2}, {-2, 1, 2}, {0, 1, 2}, {-3, 3}, {0, 3}, {-3, 0, 3}, {0, 1, 3}, {-3, 2, 3},
    {0, 2, 3}}
  else if qHd = 1 ∧ qHu = 2 then {{1}, {-2, 1}, {0, 1}, {0, 2}, {-2, 0, 2}, {1, 2}, {-2, 1, 2},
    {0, 1, 2}, {-1, 3}, {1, 3}, {0, 1, 3}, {-1, 2, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHd = 1 ∧ qHu = 3 then {{1, 2}, {-2, 1, 2}, {0, 1, 2}, {0, 3}, {-3, 0, 3}, {0, 1, 3},
    {0, 2, 3}, {1, 2, 3}}
  else if qHd = 2 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, 0, 2}, {-2, -1, 3},
    {-3, 0, 3}}
  else if qHd = 2 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-3, 1}, {-3, -2, 1},
    {-1, 1}, {-3, -1, 1}, {-1, 2}, {-3, 1, 2}, {-1, 1, 2}, {-1, 3}, {-3, -1, 3}, {-2, -1, 3},
    {-3, 1, 3}, {-1, 1, 3}, {-1, 2, 3}}
  else if qHd = 2 ∧ qHu = -1 then {{-2, 1}, {-3, -2, 1}, {-3, 2}, {-3, 0, 2}, {-3, 1, 2}, {-2, 1, 3},
    {-3, 2, 3}}
  else if qHd = 2 ∧ qHu = 0 then {{0}, {-3, 0}, {-1, 1}, {-3, -1, 1}, {0, 1}, {0, 2}, {-3, 0, 2},
    {-1, 1, 2}, {0, 1, 2}, {-3, 3}, {-3, -1, 3}, {0, 3}, {-3, 0, 3}, {-3, 1, 3}, {-1, 1, 3},
    {0, 1, 3}, {-3, 2, 3}, {0, 2, 3}}
  else if qHd = 2 ∧ qHu = 1 then {{0, 1}, {-1, 2}, {-1, 1, 2}, {0, 1, 2}, {-2, 3}, {-2, -1, 3},
    {-2, 1, 3}, {0, 1, 3}, {-1, 2, 3}}
  else if qHd = 2 ∧ qHu = 3 then {{1, 2}, {-3, 1, 2}, {-1, 1, 2}, {0, 1, 2}, {0, 3}, {-3, 0, 3},
    {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHd = 3 ∧ qHu = -2 then {{-2, 0}, {-3, 1}, {-2, 0, 2}, {-3, 1, 2}, {-2, 0, 3}}
  else if qHd = 3 ∧ qHu = -1 then {{-3, 2}, {-3, 1, 2}}
  else if qHd = 3 ∧ qHu = 0 then {{0}, {-2, 0}, {0, 1}, {-2, 2}, {0, 2}, {-2, 0, 2}, {0, 1, 2},
    {0, 3}, {-2, 0, 3}, {0, 1, 3}, {-2, 2, 3}, {0, 2, 3}}
  else if qHd = 3 ∧ qHu = 1 then {{0, 1}, {0, 1, 2}, {-2, 3}, {-2, 0, 3}, {0, 1, 3}, {-2, 2, 3}}
  else if qHd = 3 ∧ qHu = 2 then {{1}, {-3, 1}, {0, 1}, {0, 2}, {-2, 0, 2}, {1, 2}, {-3, 1, 2},
    {0, 1, 2}, {1, 3}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}
  else ∅

lemma mem_phenoConstraintHuTenSetqHdHu
    (𝓜 : MatterContent .same) (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (hTop : 𝓜.HasATopYukawa)
    (hPheno : phenoConstraintHdHuTen 𝓜.qHd 𝓜.qHu (Multiset.map QuantaTen.q 𝓜.quantaTen)) :
    (𝓜.quantaTen.map QuantaTen.q).toFinset ∈ phenoConstraintHuTenSetqHdHu 𝓜.qHd 𝓜.qHu := by
  have hmem1 := 𝓜.mem_phenoConstraintHuTenSetqHu he h3 hTop
  have hneq := 𝓜.distinctly_charged_quantaBarFiveMatter.2.2.2
  have hmemQHd := 𝓜.qHd_mem_allowedBarFiveCharges
  have hmemQHu := 𝓜.qHu_mem_allowedBarFiveCharges
  rw [quantaTen_map_q_eq_toFinset] at hPheno
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = Q10 at *
  generalize 𝓜.qHd = qHd at *
  generalize 𝓜.qHu = qHu at *
  revert Q10
  revert qHu
  revert qHd
  decide +kernel


def phenoConstraintHuTenSetqHdHuFiveExe (qHd qHu : ℤ) (ncard : ℕ) : Finset (Finset ℤ) :=
  let P1 := phenoConstraintHuTenSetqHdHu qHd qHu
  let P2 := CodimensionOneConfig.same.allowedBarFiveCharges.powerset.filter (fun x => x.card = ncard)
  let P3 := P2.filter (fun x => phenoConstraintHuFive qHu qHd x.val)
  let P4 := (P1.product P3).filter (fun x => 0 ∉ chargeLambdaTerm x.2.val x.1.val)
  (P4.val.map Prod.fst).toFinset

#eval phenoConstraintHuTenSetqHdHuFiveExe (3) (-2) 2
def phenoConstraintHuTenSetqHdHuFiveTwo (qHd qHu : ℤ) : Finset (Finset ℤ) :=
  if qHd = -3 ∧ qHu = - 2 then {{-2, 0}, {-3, 1}, {-2, 0, 2}, {-3, 1, 2}, {-2, 0, 3}}
  else if qHd = -3 ∧ qHu = -1 then {{-3, 2}}
  else if qHd = -3 ∧ qHu = 0 then {{0}, {-3, 0}}
  else if qHd = -3 ∧ qHu = 1 then {{-2, 3}}
  else if qHd = -3 ∧ qHu = 2 then {{0, 2}}
  else if qHd = -2 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, 0, 3}}
  else if qHd = -2 ∧ qHu = -1 then {{-3, 2}}
  else if qHd = -2 ∧ qHu = 0 then {{0}, {-2, 0}, {-3, 3}}
  else if qHd = -2 ∧ qHu = 1 then {{-2, 3}}
  else if qHd = -2 ∧ qHu = 2 then {{1}, {-3, 1}, {1, 2}, {-1, 3}, {1, 3}, {1, 2, 3}}
  else if qHd = -2 ∧ qHu = 3 then {{1, 2}, {0, 3}, {-3, 0, 3}, {1, 2, 3}}
  else if qHd = -1 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, 0, 3}}
  else if qHd = -1 ∧ qHu = -2 then {{-1}, {-3, -1}}
  else if qHd = -1 ∧ qHu = 0 then {{0}, {-2, 2}, {-3, 3}}
  else if qHd = -1 ∧ qHu = 1 then {{-2, 3}}
  else if qHd = -1 ∧ qHu = 2 then {{1}, {0, 2}, {1, 2}, {1, 3}, {1, 2, 3}}
  else if qHd = -1 ∧ qHu = 3 then {{1, 2}, {0, 3}, {-3, 0, 3}, {1, 2, 3}}
  -- up to here.
  else if qHd = 0 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}}
  else if qHd = 0 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-3, 1}, {-1, 1},
    {-3, -1, 1}, {-1, 3}, {-3, -1, 3}, {-3, 1, 3}, {-1, 1, 3}}
  else if qHd = 0 ∧ qHu = -1 then {{-3, 2}, {-3, -2, 2}, {-3, 2, 3}}
  else if qHd = 0 ∧ qHu = 1 then {{-2, 3}, {-3, -2, 3}, {-2, 2, 3}}
  else if qHd = 0 ∧ qHu = 2 then {{1}, {-3, 1}, {-1, 1}, {-3, -1, 1}, {1, 2}, {-1, 3}, {-3, -1, 3},
    {1, 3}, {-3, 1, 3}, {-1, 1, 3}, {1, 2, 3}}
  else if qHd = 0 ∧ qHu = 3 then {{1, 2}, {1, 2, 3}}
  else if qHd = 1 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, -2, 0}, {-3, 0, 3}}
  else if qHd = 1 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-2, 0}, {-3, -2, 0},
    {-1, 2}, {-3, -1, 2}, {-2, 0, 2}, {-1, 3}, {-1, 2, 3}}
  else if qHd = 1 ∧ qHu = -1 then {{-2, 1}, {-3, 2}, {-3, -2, 2}, {-3, -1, 2}, {-2, 1, 2},
    {-3, 2, 3}}
  else if qHd = 1 ∧ qHu = 0 then {{0}, {-3, 0}, {-2, 0}, {-3, -2, 0}, {0, 1}, {-2, 2}, {-3, -2, 2},
    {0, 2}, {-2, 0, 2}, {-2, 1, 2}, {0, 1, 2}, {-3, 3}, {0, 3}, {-3, 0, 3}, {0, 1, 3}, {-3, 2, 3},
    {0, 2, 3}}
  else if qHd = 1 ∧ qHu = 2 then {{1}, {-2, 1}, {0, 1}, {0, 2}, {-2, 0, 2}, {1, 2}, {-2, 1, 2},
    {0, 1, 2}, {-1, 3}, {1, 3}, {0, 1, 3}, {-1, 2, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHd = 1 ∧ qHu = 3 then {{1, 2}, {-2, 1, 2}, {0, 1, 2}, {0, 3}, {-3, 0, 3}, {0, 1, 3},
    {0, 2, 3}, {1, 2, 3}}
  else if qHd = 2 ∧ qHu = -3 then {{-2, -1}, {-3, -2, -1}, {-3, 0}, {-3, 0, 3}}
  else if qHd = 2 ∧ qHu = -2 then {{-1}, {-3, -1}, {-2, -1}, {-3, -2, -1}, {-3, 1}, {-3, -2, 1},
    {-1, 1}, {-3, -1, 1}, {-1, 2}, {-3, 1, 2}, {-1, 1, 2}, {-1, 3}, {-3, -1, 3}, {-2, -1, 3},
    {-3, 1, 3}, {-1, 1, 3}, {-1, 2, 3}}
  else if qHd = 2 ∧ qHu = -1 then {{-2, 1}, {-3, -2, 1}, {-3, 2}, {-3, 0, 2}, {-3, 1, 2}, {-2, 1, 3},
    {-3, 2, 3}}
  else if qHd = 2 ∧ qHu = 0 then {{0}, {-3, 0}, {-1, 1}, {-3, -1, 1}, {0, 1}, {0, 2}, {-3, 0, 2},
    {-1, 1, 2}, {0, 1, 2}, {-3, 3}, {-3, -1, 3}, {0, 3}, {-3, 0, 3}, {-3, 1, 3}, {-1, 1, 3},
    {0, 1, 3}, {-3, 2, 3}, {0, 2, 3}}
  else if qHd = 2 ∧ qHu = 1 then {{0, 1}, {-1, 2}, {-1, 1, 2}, {0, 1, 2}, {-2, 3}, {-2, -1, 3},
    {-2, 1, 3}, {0, 1, 3}, {-1, 2, 3}}
  else if qHd = 2 ∧ qHu = 3 then {{1, 2}, {-3, 1, 2}, {-1, 1, 2}, {0, 1, 2}, {0, 3}, {-3, 0, 3},
    {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}
  else if qHd = 3 ∧ qHu = -2 then {{-2, 0}, {-3, 1}, {-2, 0, 2}, {-3, 1, 2}, {-2, 0, 3}}
  else if qHd = 3 ∧ qHu = -1 then {{-3, 2}, {-3, 1, 2}}
  else if qHd = 3 ∧ qHu = 0 then {{0}, {-2, 0}, {0, 1}, {-2, 2}, {0, 2}, {-2, 0, 2}, {0, 1, 2},
    {0, 3}, {-2, 0, 3}, {0, 1, 3}, {-2, 2, 3}, {0, 2, 3}}
  else if qHd = 3 ∧ qHu = 1 then {{0, 1}, {0, 1, 2}, {-2, 3}, {-2, 0, 3}, {0, 1, 3}, {-2, 2, 3}}
  else if qHd = 3 ∧ qHu = 2 then {{1}, {-3, 1}, {0, 1}, {0, 2}, {-2, 0, 2}, {1, 2}, {-3, 1, 2},
    {0, 1, 2}, {1, 3}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}
  else ∅


def MemPhenoConstraintHuTenSetqHdHuFiveTwo (qHu : ℤ) : Prop :=
   ∀ Q5 ∈ {x ∈ CodimensionOneConfig.same.allowedBarFiveCharges.powerset | x.card = 2},
    qHu ∉ Q5.val →
      ∀ qHd ∈ CodimensionOneConfig.same.allowedBarFiveCharges,

        qHd ∉ Q5.val →
          qHu ≠ qHd →
            ∀ Q10 ∈ phenoConstraintHuTenSetqHdHu qHd qHu,
            --0 ∉ chargeLambdaTerm Q5.val Q10.val
            ((Q5.product Q5).val.map (fun x => - (x.1 + x.2))) ∩ Q10.val ≠ ∅
            -- phenoConstraintTenFive Q5.val Q10.val
             → Q10 ∈ phenoConstraintHuTenSetqHdHu qHd qHu

instance (qHu : ℤ) : Decidable (MemPhenoConstraintHuTenSetqHdHuFiveTwo qHu) := List.decidableBAll _ _

set_option profiler true
lemma memPhenoConstraintHuTenSetqHdHuFiveTwo_neg_three :
   ∀ (x : CodimensionOneConfig.same.allowedBarFiveCharges),  MemPhenoConstraintHuTenSetqHdHuFiveTwo x := by
  decide

lemma mem_phenoConstraintHuTenSetqHdHuFiveTwo
    (𝓜 : MatterContent .same) (he : 𝓜.NoExotics) (h3 : 𝓜.ThreeChiralFamiles)
    (hTop : 𝓜.HasATopYukawa)
    (hPheno : phenoConstraintHdHuTen 𝓜.qHd 𝓜.qHu (Multiset.map QuantaTen.q 𝓜.quantaTen))
    (hPhenoHuF : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPhenoTenF : phenoConstraintTenFive  (𝓜.quantaBarFiveMatter.map QuantaBarFive.q) (𝓜.quantaTen.map QuantaTen.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) :
    (𝓜.quantaTen.map QuantaTen.q).toFinset ∈ phenoConstraintHuTenSetqHdHu 𝓜.qHd 𝓜.qHu := by
  -- membership of Q10
  have hmem1 := 𝓜.mem_phenoConstraintHuTenSetqHdHu he h3 hTop hPheno
  clear hPheno
  -- membership of Q5
  have hQ5mem:= 𝓜.quantaBarFiveMatter_map_q_mem_powerset_filter_card hcard
  -- membership of qHd
  have hmemQHd := 𝓜.qHd_mem_allowedBarFiveCharges
  -- membership of qHu
  have hmemQHu := 𝓜.qHu_mem_allowedBarFiveCharges
  -- non-equivalence of qHd and qHu
  have hneq := 𝓜.distinctly_charged_quantaBarFiveMatter.2.2.2
  -- qHd not in Q5
  have hqHdnotQ5 := hPhenoHuF.2.2.1
  -- qHu not in Q5
  have hqHunotQ5 := hPhenoHuF.2.1
  clear hPhenoHuF
  -- gerneralizing Q10
  rw [quantaTen_map_q_eq_toFinset] at hPhenoTenF
  generalize (𝓜.quantaTen.map QuantaTen.q).toFinset = Q10 at *
  revert hPhenoTenF
  revert Q10
  -- generalizing qHd
  generalize 𝓜.qHd = qHd at *
  revert hneq
  revert hqHdnotQ5
  revert qHd
  -- generalizing qHu
  generalize 𝓜.qHu = qHu at *
  revert qHu
  -- generalizing Q5
  rw [quantaBarFiveMatter_map_q_eq_toFinset] at  ⊢
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = Q5 at *
  revert Q5


  -- deciding
  -- decide



end MatterContent

end SU5U1
end FTheory
