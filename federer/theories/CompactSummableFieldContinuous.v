(** Federer (1969), 4.1.18, pp. 375–376: compact
    smooth fields belong to Omega. The earlier
    compact continuous L1 theorem of 4.1.5,
    p. 350, already gives the required summability.
    This adapter preserves their actual pointwise values
    behind the independently specified opaque field carrier. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology boolp.
From Federer Require Import PartialFunctionUP RealNormUP NormMetric VectorDaniellHypotheses
  PartialFunctionBasic PartialFunctionExtensionUP MeasureUP RadonMeasureUP
  MeasureLpMembershipUP CompactSupportFunctionUP CompactContinuousVectorFields
  CompactContinuousVectorMeasurable RadonCompactScalarIntegral
  CompactSummableFieldSealed CompactSummableFieldLaws
  CompactSummableFieldRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_summable_continuous_field_representative]:
    actual compact continuous, hence compact smooth,
    coefficient fields lie in Omega in Federer
    4.1.18, pp. 375–376, through the
    preceding L1 membership result of 4.1.5.
    The original field is preserved everywhere. *)
Theorem compact_summable_continuous_field_representative
    (R:realType) (X:topologicalType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N)
    (hSep:is_separable_normed_space hN)
    (mu:set X->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu)
    (f:X->V):
  compact_continuous_vector_fields hN f->
  exists w:@CompactSummableField.space R X V N hN mu hm,
    @compact_summable_field_value R X V N hN mu hm w=f.
Proof.
move=>hF.
have hLone:=@compact_continuous_vector_lone_member R X V N hN hSep mu hm hr
  (@radon_positive_compact_integral R X mu hm hr)
  (@radon_positive_compact_integral_laws R X mu hm hr) f hF.
pose K:=@real_function_support R X (fun x=>N (f x)).
have hOff:forall x y,partial_function_graph (partial_function_total f) x y->~K x->y=0.
  move=>x y hY hX.
  have hValue:f x=y:=hY.
  rewrite -hValue;exact:(@compact_continuous_vector_zero_off_norm_support R X V N hN f x hX).
have[w [hExtend _]]:=@compact_summable_partial_field_representative R X V N hN mu hm
  (partial_function_total f) hLone.2.1 hLone.2.2.1 K hF.2 hOff.
exists w;apply:funext=>x;exact:(@hExtend x (f x) (erefl (f x))).
Qed.
