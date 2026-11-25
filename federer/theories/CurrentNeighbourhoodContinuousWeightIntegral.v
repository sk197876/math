(** Federer (1969), 4.1.13, pp. 369–370, used
    in 4.1.14, p. 371: restricting to a
    support neighbourhood preserves the exact continuous
    variation-weight integral. Use the preceding original
    total-integral transport and finite compact carriage. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentMassSealed CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentOpenRestriction CurrentOpenRestrictionVariation
  CurrentCompactVariationContinuousIntegral MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_neighbourhood_continuous_weight_lower_value]:
    the original continuous weighted variation integral has
    exactly the same value on every support neighbourhood,
    supporting Federer 4.1.14, p. 371. Representations
    are arbitrary; all choices stay within the original
    Radon variation. No derivative locality premise is needed. *)
Theorem current_neighbourhood_continuous_weight_lower_value
    (R:realType) (h2:(1+1:R)!=0) n m
    (W U:set (R_n R n))
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hWU:forall x,W x->U x)
    (T:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (hSupport:@current_support R h2 n U hU m T `<=` W)
    (hSmall:@is_integration_representable_current R h2 n m W hW
      (@current_open_restriction R h2 n m W U hW hU hWU T))
    (hFinite:(@CurrentMass.value R h2 n m U hU T< +oo)%E)
    (hCompact:@compact
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (@current_support R h2 n U hU m T))
    (F:current_domain R n U->R^o) (hF:continuous F) :
  measure_lower_integral (@NormalisedCurrent.measure R h2 n m W hW
      (@current_open_restriction R h2 n m W U hW hU hWU T) hSmall)
    (real_total_integrand (fun x=>F (@current_open_domain_inclusion R n W U hWU x)))=
  measure_lower_integral (@NormalisedCurrent.measure R h2 n m U hU T hT)
    (real_total_integrand F).
Proof.
have[c hIntegral]:=@current_compact_variation_continuous_integral
  R h2 n m U hU T hT hFinite hCompact F hF.
have hRestricted:=(@current_neighbourhood_variation_total_integral_iff
  R h2 n m W U hW hU hWU T hT hSupport hSmall F c%:E).2 hIntegral.
have hLarge:=measure_lower_integral_unique hIntegral.2.2
  (measure_lower_integral_specification _ _).
have hSmallValue:=measure_lower_integral_unique hRestricted.2.2
  (measure_lower_integral_specification _ _).
exact:eq_trans (esym hSmallValue) hLarge.
Qed.
