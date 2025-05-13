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
import PhysLean.StringTheory.FTheory.SU5U1.PhenoConstraints.TenCharges
/-!

## Studying four 5-bar representations.

-/

namespace FTheory

namespace SU5U1
variable {I : CodimensionOneConfig}

namespace MatterContent

/-!

## Case when CodimensionOneConfig is `same`

-/

#eval
    ((CodimensionOneConfig.same.allowedBarFiveCharges.product
    (CodimensionOneConfig.same.allowedBarFiveCharges.powerset.filter (fun x => x.card =1))).val.filter
    (fun (qHu, F) => phenoConstraintHuFive qHu (3) F.val ∧
      fiveTest qHu (3) F.val )).card


def allowedBarFiveHuHdOfHd (qHd : ℤ) : Finset (ℤ × Multiset ℤ) :=
    (((CodimensionOneConfig.same.allowedBarFiveCharges.product
    (CodimensionOneConfig.same.allowedBarFiveCharges.powerset.filter (fun x => x.card = 2))).val.filter
    (fun (qHu, F) => phenoConstraintHuFive qHu qHd F.val ∧
      fiveTest qHu qHd F.val)).map (fun x => (x.1, x.2.val))).toFinset

def qHdMap (qHd : ℤ) : Finset (ℤ ×  Multiset ℤ) :=
  if qHd = -3 then
    {(-2, {0, 2}), (-2, {2, 3}),
    (-1, {-2, 0}), (-1, {0, 2}),
    (0, {-2, -1}), (0, {-2, 1}), (0, {-1, 1}), (0, {-2, 2}), (0, {-1, 2}), (0, {1, 2}),
    (1, {-2, 0}), (1, {0, 2}), (1, {-1, 3}),
    (2, {-2, 0}), (2, {-2, 3}),
    (3, {-2, -1}), (3, {-2, 0}), (3, {-1, 0}),
    (3, {-2, 1}), (3, {-1, 1}), (3, {0, 1}), (3, {-2, 2}), (3, {-1, 2}), (3, {0, 2}), (3, {1, 2})}
  else if qHd = -2 then
    {(-3, {-1, 0}), (-3, {0, 2}), (-3, {2, 3}),
    (-1, {-3, 1}), (-1, {-3, 2}), (-1, {1, 2}), (-1, {-3, 3}), (-1, {1, 3}), (-1, {2, 3}),
    (0, {-3, -1}), (0, {-1, 3}),
    (1, {-1, 0}), (1, {-1, 2}),
    (2, {-3, -1}), (2, {-3, 0}), (2, {-1, 0}), (2, {-3, 1}), (2, {-1, 1}),
      (2, {0, 1}), (2, {-3, 3}), (2, {-1, 3}), (2, {0, 3}), (2, {1, 3}),
    (3, {-3, 2}), (3, {0, 2})}
  else if qHd = -1 then
    {(-3, {-2, 0}), (-3, {0, 1}), (-3, {0, 2}), (-3, {1, 3}),
    (-2, {0, 1}), (-2, {0, 2}), (-2, {1, 2}), (-2, {0, 3}), (-2, {1, 3}), (-2, {2, 3}),
    (0, {-3, -2}), (0, {2, 3}),
    (1, {-3, -2}), (1, {-3, 0}), (1, {-2, 0}), (1, {-3, 2}), (1, {-2, 2}), (1, {0, 2}),
    (2, {-2, 1}), (2, {0, 1}),
    (3, {-2, 0}), (3, {-3, 1}), (3, {0, 2})}
  else if qHd = 0 then
    {(-3, {-2, -1}), (-3, {-2, 1}), (-3, {-1, 1}), (-3, {-2, 2}), (-3, {-1, 2}), (-3, {1, 2}),
      (-3, {-2, 3}), (-3, {-1, 3}), (-3, {1, 3}), (-3, {2, 3}),
    (-2, {-3, -1}), (-2, {-1, 3}), (-2, {2, 3}),
    (-1, {1, 3}), (-1, {2, 3}),
    (1, {-3, -2}), (1, {-3, -1}),
    (2, {-3, -2}), (2, {-3, 1}), (2, {1, 3}),
    (3, {-3, -2}), (3, {-3, -1}), (3, {-2, -1}), (3, {-3, 1}), (3, {-2, 1}), (3, {-1, 1}),
      (3, {-3, 2}), (3, {-2, 2}), (3, {-1, 2}), (3, {1, 2})}
  else if qHd = 1 then
    {(-3, {-2, 0}), (-3, {0, 2}), (-3, {-1, 3}),
    (-2, {-1, 0}), (-2, {-1, 2}),
    (-1, {-2, 0}), (-1, {-2, 2}), (-1, {0, 2}), (-1, {-2, 3}), (-1, {0, 3}), (-1, {2, 3}),
    (0, {-3, -2}), (0, {2, 3}),
    (2, {-3, -2}),  (2, {-3, -1}), (2, {-2, -1}), (2, {-3, 0}), (2, {-2, 0}), (2, {-1, 0}),
    (3, {-3, -1}),  (3, {-2, 0}), (3, {-1, 0}), (3, {0, 2})}
  else if qHd = 2 then
    {(-3, {-2, 0}), (-3, {-2, 3}),
    (-2, {-3, -1}), (-2, {-3, 0}), (-2, {-1, 0}), (-2, {-3, 1}), (-2, {-1, 1}), (-2, {0, 1}),
      (-2, {-3, 3}), (-2, {-1, 3}), (-2, {0, 3}), (-2, {1, 3}),
    (-1, {-2, 1}), (-1, {0, 1}),
    (0, {-3, 1}), (0, {1, 3}),
    (1, {-3, -2}), (1, {-3, -1}), (1, {-2, -1}), (1, {-3, 3}), (1, {-2, 3}),
      (1, {-1, 3}),
    (3, {-3, -2}), (3, {-2, 0}), (3, {0, 1})}
  else if qHd = 3 then
    {(-3, {-2, -1}), (-3, {-2, 0}), (-3, {-1, 0}), (-3, {-2, 1}), (-3, {-1, 1}), (-3, {0, 1}),
      (-3, {-2, 2}), (-3, {-1, 2}), (-3, {0, 2}), (-3, {1, 2}),
    (-2, {-3, 2}), (-2, {0, 2}),
    (-1, {-2, 0}), (-1, {-3, 1}), (-1, {0, 2}),
    (0, {-2, -1}), (0, {-2, 1}), (0, {-1, 1}), (0, {-2, 2}), (0, {-1, 2}), (0, {1, 2}),
    (1, {-2, 0}), (1, {0, 2}),
    (2, {-3, -2}), (2, {-2, 0})}
  else ∅



def qHdMap' (qHd qHu : ℤ) : Finset (Multiset ℤ) :=
  if qHd = -3 ∧ qHu = -2 then {{0, 2}, {2, 3}}
  else if qHd = -3 ∧ qHu = -1 then {{-2, 0}, {0, 2}}
  else if qHd = -3 ∧ qHu = 0 then {{-2, -1}, {-2, 1}, {-1, 1}, {-2, 2}, {-1, 2}, {1, 2}}
  else if qHd = -3 ∧ qHu = 1 then {{-2, 0}, {0, 2}, {-1, 3}}
  else if qHd = -3 ∧ qHu = 2 then {{-2, 0}, {-2, 3}}
  else if qHd = -3 ∧ qHu = 3 then {{-2, -1}, {-2, 0}, {-1, 0}, {-2, 1}, {-1, 1}, {0, 1}, {-2, 2},
      {-1, 2}, {0, 2}, {1, 2}}
  else if qHd = -2 ∧ qHu = -3 then {{-1, 0}, {0, 2}, {2, 3}}
  else if qHd = -2 ∧ qHu = -1 then  {{-3, 1}, {-3, 2}, {1, 2}, {-3, 3}, {1, 3}, {2, 3}}
  else if qHd = -2 ∧ qHu = 0 then  {{-3, -1},  {-1, 3}}
  else if qHd = -2 ∧ qHu = 1 then  {{-1, 0}, {-1, 2}}
  else if qHd = -2 ∧ qHu = 2 then  {{-3, -1}, {-3, 0}, {-1, 0}, {-3, 1}, {-1, 1},
      {0, 1}, {-3, 3}, {-1, 3}, {0, 3}, {1, 3}}
  else if qHd = -2 ∧ qHu = 3 then {{-3, 2}, {0, 2}}
  else if qHd = -1 ∧ qHu = -3 then {{-2, 0}, {0, 1}, {0, 2}, {1, 3}}
  else if qHd = -1 ∧ qHu = -2 then {{0, 1}, {0, 2}, {1, 2}, {0, 3}, {1, 3}, {2, 3}}
  else if qHd = -1 ∧ qHu = 0 then {{-3, -2}, {2, 3}}
  else if qHd = -1 ∧ qHu = 1 then {{-3, -2}, {-3, 0}, {-2, 0}, {-3, 2}, {-2, 2}, {0, 2}}
  else if qHd = -1 ∧ qHu = 2 then  {{-2, 1}, {0, 1}}
  else if qHd = -1 ∧ qHu = 3 then  {{-2, 0}, {-3, 1}, {0, 2}}
  else if qHd = 0 ∧ qHu = -3 then {{-2, -1}, {-2, 1}, {-1, 1}, {-2, 2}, {-1, 2}, {1, 2},
      {-2, 3}, {-1, 3},  {1, 3}, {2, 3}}
  else if qHd = 0 ∧ qHu = -2 then {{-3, -1}, {-1, 3}, {2, 3}}
  else if qHd = 0 ∧ qHu = -1 then  {{1, 3}, {2, 3}}
  else if qHd = 0 ∧ qHu = 1 then {{-3, -2}, {-3, -1}}
  else if qHd = 0 ∧ qHu = 2 then  {{-3, -2}, {-3, 1}, {1, 3}}
  else if qHd = 0 ∧ qHu = 3 then  {{-3, -2}, {-3, -1}, {-2, -1}, {-3, 1}, {-2, 1}, {-1, 1},
      {-3, 2}, {-2, 2}, {-1, 2}, {1, 2}}
  else if qHd = 1 ∧ qHu = -3 then  {{-2, 0}, {0, 2}, {-1, 3}}
  else if qHd = 1 ∧ qHu = -2 then  {{-1, 0}, {-1, 2}}
  else if qHd = 1 ∧ qHu = -1 then  {{-2, 0}, {-2, 2}, {0, 2}, {-2, 3}, {0, 3}, {2, 3}}
  else if qHd = 1 ∧ qHu = 0 then  {{-3, -2}, {2, 3}}
  else if qHd = 1 ∧ qHu = 2 then  {{-3, -2}, {-3, -1}, {-2, -1}, {-3, 0}, {-2, 0}, {-1, 0}}
  else if qHd = 1 ∧ qHu = 3 then  {{-3, -1},  {-2, 0}, {-1, 0}, {0, 2}}
  else if qHd = 2 ∧ qHu = -3 then {{-2, 0}, {-2, 3}}
  else if qHd = 2 ∧ qHu = -2 then  {{-3, -1}, {-3, 0}, {-1, 0}, {-3, 1}, {-1, 1}, {0, 1},
      {-3, 3}, {-1, 3}, {0, 3}, {1, 3}}
  else if qHd = 2 ∧ qHu = -1 then {{-2, 1}, {0, 1}}
  else if qHd = 2 ∧ qHu = 0 then {{-3, 1}, {1, 3}}
  else if qHd = 2 ∧ qHu = 1 then {{-3, -2}, {-3, -1}, {-2, -1}, {-3, 3}, {-2, 3}, {-1, 3}}
  else if qHd = 2 ∧ qHu = 3 then {{-3, -2}, {-2, 0}, {0, 1}}
  else if qHd = 3 ∧ qHu = -3 then {{-2, -1}, {-2, 0}, {-1, 0}, {-2, 1}, {-1, 1}, {0, 1},
      {-2, 2}, {-1, 2}, {0, 2}, {1, 2}}
  else if qHd = 3 ∧ qHu = -2 then {{-3, 2}, {0, 2}}
  else if qHd = 3 ∧ qHu = -1 then  {{-2, 0}, {-3, 1}, {0, 2}}
  else if qHd = 3 ∧ qHu = 0 then  {{-2, -1}, {-2, 1}, {-1, 1}, {-2, 2}, {-1, 2}, {1, 2}}
  else if qHd = 3 ∧ qHu = 1 then  {{-2, 0}, {0, 2}}
  else if qHd = 3 ∧ qHu = 2 then  {{-3, -2}, {-2, 0}}
  else ∅

lemma qHd_qHu_barFive_of_qHd_of_card_two_generic  (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (qHd : ℤ) (hqHd : 𝓜.qHd = qHd)
    (hdecide : ∀ F ∈ {x ∈ CodimensionOneConfig.same.allowedBarFiveCharges.powerset | x.card = 2},
      ∀ qHu ∈ CodimensionOneConfig.same.allowedBarFiveCharges, phenoConstraintHuFive qHu qHd F.val →
      fiveTest qHu qHd F.val →
      (qHd, qHu, F.val) ∈ Multiset.map (fun x => (qHd, qHu, x)) (qHdMap' qHd qHu).val := by decide) :
      (𝓜.qHd, 𝓜.qHu,
    𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈ ((qHdMap' 𝓜.qHd 𝓜.qHu).val.map
     (fun x => (𝓜.qHd, 𝓜.qHu, x))) := by
  have hmem := 𝓜.quantaBarFiveMatter_map_q_mem_powerset_filter_card hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at hPheno h5 ⊢
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at hmem hPheno h5 ⊢
  have hHu := 𝓜.qHu_mem_allowedBarFiveCharges
  generalize 𝓜.qHu = qHu at hHu hPheno h5 ⊢
  have hHd := 𝓜.qHd_mem_allowedBarFiveCharges
  generalize 𝓜.qHd = qHd' at hHd hPheno h5 hqHd ⊢
  subst hqHd
  revert qHu
  revert F
  exact hdecide

lemma qHd_qHu_barFive_of_qHd_of_card_two_neg_three (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = -3) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (-3) hqHd

lemma qHd_qHu_barFive_of_qHd_of_card_two_neg_two (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = -2) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (-2) hqHd

lemma qHd_qHu_barFive_of_qHd_of_card_two_neg_one (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = -1) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (-1) hqHd

lemma qHd_qHu_barFive_of_qHd_of_card_two_zero (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = 0) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (0) hqHd

lemma qHd_qHu_barFive_of_qHd_of_card_two_one (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = 1) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (1) hqHd

lemma qHd_qHu_barFive_of_qHd_of_card_two_two (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = 2) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (2) hqHd

lemma qHd_qHu_barFive_of_qHd_of_card_two_three (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) (hqHd : 𝓜.qHd = 3) :
    (𝓜.qHd, 𝓜.qHu, 𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈
      (qHdMap' 𝓜.qHd 𝓜.qHu).val.map (fun x => (𝓜.qHd, 𝓜.qHu, x)) := by
  exact 𝓜.qHd_qHu_barFive_of_qHd_of_card_two_generic h5 hPheno hcard (3) hqHd

end MatterContent

end SU5U1
end FTheory
