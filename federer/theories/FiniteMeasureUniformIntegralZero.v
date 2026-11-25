(** Federer (1969), 4.1.1, p. 346: the
    integral of a compactly supported derivative
    vanishes. This supporting estimate says that
    one constant integral value must vanish when
    its integrands are arbitrarily uniformly small
    on a fixed finite-measure set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import MeasureUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  SummableRealArithmetic VectorDaniellPairingMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_measure_uniform_integral_zero]: a
    constant integral value of uniformly vanishing
    functions on one finite-measure support is
    zero, supporting Federer 4.1.1, p. 346. *)
Theorem finite_measure_uniform_integral_zero (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (S:set X) (m b:R):
  measure_measurable mu S ->mu S=m%:E ->
  (forall e:R,0<e ->exists F:X->R,
    is_measure_integral mu (real_total_integrand F) b%:E /\
    (forall x,S x ->`|F x|<=e) /\ (forall x,~S x ->F x=0)) ->b=0.
Proof.
move=>hS hMass hSmall.
pose chi:=@CharacteristicFunction.value R X S.
have hChi:=@CharacteristicFunction.laws R X S.
have hInt:=@measure_characteristic_integral R X mu hm S chi hChi hS.
rewrite hMass in hInt.
have hm0:0<=m by have h:=measure_nonnegative hm S; by rewrite hMass lee_fin in h.
have hBound e (he:0<e):`|b|<=e * m.
  have [F [hF [hOn hOff]]]:=hSmall e he.
  have hScale:=@real_total_integral_scale R X mu hm chi m e hInt.
  have hDom x:`|F x|<=e*chi x.
    rewrite /chi; case:(pselect (S x))=>hx.
    - by rewrite (characteristic_on_set hChi hx) mulr1; exact:hOn x hx.
    - by rewrite (hOff x hx) normr0 (characteristic_off_set hChi hx) mulr0.
  have [c [hc hcb]]:=real_total_dominated_integral hm hF.1 hScale hDom.
  have hEq:c=b:=congr1 (@fine R) (measure_integral_unique hc hF).
  by rewrite hEq in hcb.
case:(eqVneq b 0)=>// hNe.
have hb:0<`|b| by rewrite normr_gt0.
have hmp:0<m+1 by lra.
have he:0<`|b|/(m+1) by rewrite divr_gt0.
have hB:=hBound _ he.
have hEq:(`|b|/(m+1))*(m+1)=`|b| by rewrite divfK // gt_eqF.
clear hSmall hBound hInt hChi; nra.
Qed.
