(** Federer (1969), 4.1.25, p. 383: the
    variable-form auxiliary scalar quotient is Lebesgue measurable.
    Reuse the measured original numerator, the actual
    Jacobian's measurability, and the Borel scalar reciprocal
    with its zero value at zero. All these partial
    functions retain exactly the original differential domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormDifferentialDirectional GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness ExteriorGrading ExteriorMaps
  AlternatingForms AlternatingPairing EuclideanLinearJacobian Jacobian
  EuclideanJacobianMeasurable LipschitzUP EuclideanLebesgueDimensions
  PartialFunctionUP PartialFunctionPostcomposition PartialFunctionPair
  MeasurableFunctionUP MeasurablePostcomposition MeasurableRealArithmetic
  MeasurableGraphEquivalence BorelFunctionBasic RealMetricBackground RealReciprocalBorel
  ExtendedFiniteProjectionBorel MeasurableRealEmbedding
  MeasureUP MeasureIntegralUP CurrentLipschitzLebesgueActionIntegrand
  CurrentAreaPairingQuotientUP CurrentAreaPairingQuotientTestUP
  CurrentAreaPairingQuotientTestSealed ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_pairing_quotient_test_measurable]:
    the auxiliary scalar is measurable on its original
    conull differential domain, supporting 4.1.25, p. 383.
    The numerator's original summability theorem supplies
    its measurability for the actual Omega field. *)
Theorem current_area_pairing_quotient_test_measurable (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (xi:R_n R m->exterior_power (R_n R m) m)
    (phi:R_n R n->A_m (R_n R n) R^o m) :
  is_metric_lipschitz setT f ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (@current_lipschitz_lebesgue_action_integrand R m n m f xi phi) ->
  is_measure_measurable_function (@euclidean_lebesgue_measure R m)
    (@CurrentAreaPairingQuotientTest.value R m n f xi phi).
Proof.
move=>hLip hNumerator.
pose X:=R_n R m.
pose Y:=R_n R n.
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose numerator:=@current_lipschitz_lebesgue_action_integrand R m n m f xi phi.
pose NR:=partial_function_postcompose numerator
  (fun z:extended_real_line R=>(fine z:real_line_metric R)).
pose JR:=euclidean_jacobian m setT f.
pose IR:=partial_function_postcompose JR (fun j:real_line_metric R=>j^-1).
pose PR:=partial_real_function_multiply IR NR.
pose PE:=partial_function_postcompose PR
  (fun r:real_line_metric R=>(r%:E:extended_real_line R)).
have hNR:=@measurable_function_borel_postcomposition R X
  (extended_real_line R) [the topologicalType of real_line_metric R]
  mu hm numerator _ hNumerator (@extended_finite_projection_borel R).
have hIR:=@measurable_function_borel_postcomposition R X
  [the topologicalType of real_line_metric R] [the topologicalType of real_line_metric R]
  mu hm JR _ (@euclidean_top_jacobian_measurable R m n f hLip)
  (@real_reciprocal_borel R).
have hPR:=@measurable_real_function_multiply R X mu hm IR NR hIR hNR.
have hPE:=@measurable_function_borel_postcomposition R X
  [the topologicalType of real_line_metric R] (extended_real_line R)
  mu hm PR _ hPR (continuous_borel_function (@real_extended_embedding_continuous R)).
apply:(@measurable_function_graph_equivalent R X (extended_real_line R) mu PE
  (@CurrentAreaPairingQuotientTest.value R m n f xi phi) _ hPE)=>x z.
rewrite (@CurrentAreaPairingQuotientTest.laws R m n f xi phi x z).
split.
- move=>[r [hR hEmbed]].
  have [p [[hI hN] hProduct]]:=hR.
  have [j [hJ hInverse]]:=hI.
  have [v [hV hFine]]:=hN.
  have [D [hD hJacobian]]:=(euclidean_jacobian_graph m setT f x j).1 hJ.
  have [F [hF hPair]]:=
    (@current_lipschitz_lebesgue_action_integrand_graph R m n m f xi phi x v).1 hV.
  have hFD:F=D:=@norm_differential_unique R X Y
    (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) hNX hNY setT f x F D hF hD.
  subst F.
  exists D;split;first exact:hD.
  rewrite -hProduct -hInverse -hFine -hPair -hJacobian in hEmbed.
  exact:hEmbed.
- move=>[D [hD hValue]].
  exists (current_area_pairing_quotient_coefficient xi (phi (f x)) x D).
  split;last exact:hValue.
  exists ((euclidean_linear_jacobian m D)^-1,
    pairing (exterior_power_map (hom_as_linear D) m (xi x)) (phi (f x))).
  split;last reflexivity.
  split.
  + exists (euclidean_linear_jacobian m D);split;last reflexivity.
    apply:(euclidean_jacobian_graph m setT f x _).2.
    by exists D.
  + exists (pairing (exterior_power_map (hom_as_linear D) m (xi x)) (phi (f x)))%:E.
    split;last reflexivity.
    apply:(@current_lipschitz_lebesgue_action_integrand_graph R m n m f xi phi x _).2.
    by exists D;split.
Qed.
