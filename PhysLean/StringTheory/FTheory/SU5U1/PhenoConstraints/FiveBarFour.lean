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

#eval
    ((CodimensionOneConfig.same.allowedBarFiveCharges.product
    (CodimensionOneConfig.same.allowedBarFiveCharges.powerset.filter (fun x => x.card = 2))).val.filter
    (fun (qHu, F) => phenoConstraintHuFive qHu (3) F.val ∧
      fiveTest qHu (3) F.val ))

def qHdMap (qHd : ℤ) : Finset (ℤ ×  Multiset ℤ) :=
  if qHd = -3 then
    {(-2, {0, 2}), (-2, {2, 3}),
    (-1, {-2, 0}), (-1, {0, 2}),
    (0, {-2, -1}), (0, {-2, 1}), (0, {-1, 1}), (0, {-2, 2}), (0, {-1, 2}), (0, {1, 2}),
    (1, {-2, 0}), (1, {0, 2}), (1, {-1, 3}),
    (2, {-2, 0}), (2, {-2, 3}), (3, {-2, -1}), (3, {-2, 0}), (3, {-1, 0}),
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

set_option maxRecDepth 20000 in
lemma test1
    (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) : (𝓜.qHd, 𝓜.qHu,
    𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈ ((qHdMap 𝓜.qHd).val.map
     (fun x => (𝓜.qHd, x.1, x.2))) := by
  have hmem := 𝓜.quantaBarFiveMatter_map_q_mem_powerset_filter_card hcard
  rw [𝓜.quantaBarFiveMatter_map_q_eq_toFinset] at hPheno h5 ⊢
  generalize (𝓜.quantaBarFiveMatter.map QuantaBarFive.q).toFinset = F at hmem hPheno h5 ⊢
  have hHu := 𝓜.qHu_mem_allowedBarFiveCharges
  generalize 𝓜.qHu = qHu at hHu hPheno h5 ⊢
  have hHd := 𝓜.qHd_mem_allowedBarFiveCharges
  generalize 𝓜.qHd = qHd at hHd hPheno h5 ⊢
  fin_cases hHd
  · revert qHu
    revert F
    native_decide
  · revert qHu
    revert F
    native_decide
  · revert qHu
    revert F
    native_decide
  · revert qHu
    revert F
    native_decide
  · revert qHu
    revert F
    native_decide
  · revert qHu
    revert F
    native_decide
  · revert qHu
    revert F
    native_decide


#eval
    (((CodimensionOneConfig.same.allowedTenCharges.powerset.filter (fun x => x.card ≤ 3)).product
    ((qHdMap (-3)).val.map (fun x => (-3, x.1, x.2))).toFinset).filter
    (fun (Q10, (qHd, qHu, Q5)) =>
    AnomalyFreeCharges CodimensionOneConfig.same qHd qHu Q10.val Q5
    ∧ 0 ∉ chargeBetaTerm Q5 qHu ∧
      0 ∉ chargeLambdaTerm Q5 Q10.val ∧
      0 ∉ chargeW2Term Q10.val qHd ∧
      0 ∉ chargeW4Term Q5 qHd qHu ∧
      0 ∉ chargeK1Term Q5 Q10.val ∧
      0 ∉ chargeK2Term Q10.val qHu qHd ∧
      0 ∉ chargeW1Term Q5 Q10.val ∧
      0 ∈ chargeYukawaTop Q10.val qHu)  )

set_option maxRecDepth 20000 in
lemma quantaBarFiveMatter_of_card_three_with_qHd
    (𝓜 : MatterContent .same)
    (h5 : fiveTest 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (hPheno : phenoConstraintHuFive 𝓜.qHu 𝓜.qHd (𝓜.quantaBarFiveMatter.map QuantaBarFive.q))
    (h : 𝓜.ProtonDecayU1Constrained)
    (hx : 𝓜.RParityU1Constrained)
    (hTop : 𝓜.HasATopYukawa) (hSpec : 𝓜.ValidMatterSpectrum)
    (hcard : 𝓜.quantaBarFiveMatter.card = 2) : (𝓜.quantaTen.map QuantaTen.q,  𝓜.qHd, 𝓜.qHu,
      𝓜.quantaBarFiveMatter.map QuantaBarFive.q) ∈ ({({0}, -3, 0, {-2, -1}), ({-3, 0}, -3, 0, {-2, -1}), ({-2, 3}, -3, 1, {-2, 0})} : Finset (Multiset ℤ × ℤ × ℤ ×  Multiset ℤ)) := by
  have hMem := 𝓜.test1 h5 hPheno hcard
  have hAxiom :  𝓜.qHd = -3 := by sorry
  simp [hAxiom] at hMem
  have hacc := 𝓜.anomalyFreeCharges_of_anomalyFree (by sorry) (by sorry) (by sorry) (by sorry) (by sorry )
  rw [RParityU1Constrained] at hx
  rw [ProtonDecayU1Constrained] at h
  generalize 𝓜.qHu = qHu at hMem h hx hacc ⊢
  generalize 𝓜.qHd = qHd at *
  subst hAxiom
  generalize 𝓜.quantaBarFiveMatter.map QuantaBarFive.q = qBarFive at hMem h hx hacc ⊢
  generalize ha : ( qHu, qBarFive) = a at hMem
  have ha2 : qHu = a.1 := by rw [← ha]
  have ha3 : qBarFive = a.2 := by rw [← ha]
  subst ha2 ha3
  have h10Mem := 𝓜.quantaTen_map_q_powerset_filter_card_three (by sorry) (by sorry)
  rw [quantaTen_map_q_eq_toFinset] at h hx hacc ⊢
  generalize (Multiset.map QuantaTen.q 𝓜.quantaTen).toFinset = qTen at *
  revert a
  revert qTen

  sorry

end MatterContent

end SU5U1
end FTheory
