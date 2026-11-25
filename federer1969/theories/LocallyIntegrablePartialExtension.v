(** Federer (1969), 4.1.2, p. 347: the
    locally integrable partial field has an actual
    measurable total extension with the same local
    norm integrals. The reduction uses precisely the
    null-extension convention of 2.3.2, p. 73. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialFunctionExtensionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableTotalExtension MeasureDensityTransfer
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralAlmostEquality SummableRealFunctionUP
  SmoothCompactSet LocallyIntegrableVectorFieldUP LocallyIntegrablePartialFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [locally_integrable_partial_total_extension]: the original
    smoothing hypothesis allows a conull partial domain,
    Federer 4.1.2, p. 347, by 2.3.2,
    p. 73. The extension preserves every originally
    defined value and satisfies the actual compact integral laws. *)
Theorem locally_integrable_partial_total_extension (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu)
    (f:partial_function X (real_norm_metric_space hNY)):
  is_locally_integrable_partial_vector_field hNX mu f ->
  exists F:X->Y,is_partial_function_total_extension f F /\
    measure_almost_equal mu f (partial_function_total F) /\
    @is_locally_integrable_vector_field R X Y NX NY hNX hNY mu F.
Proof.
move=>hField.
have [F [hExt [hAlmost hMeas]]]:=@measurable_function_total_extension R X
  (real_norm_metric_space hNY) mu hm f 0 (locally_integrable_partial_measurable hField).
exists F; split=>//; split=>//; constructor; first exact hMeas.
move=>K.
have [b hLocal]:=@locally_integrable_partial_compact_norm R X Y NX NY hNX hNY mu f hField K.
have hNormAlmost:measure_almost_equal mu
    (partial_function_postcompose f (fun y=>(NY y)%:E:extended_real_line R))
    (real_total_integrand (fun x=>NY (F x))).
  apply:(@measure_almost_everywhere_mono R X mu hm _ _ _ hAlmost)=>x [y [hy hF]].
  change (F x=y) in hF.
  exists (NY y)%:E; split; first by exists y.
  by rewrite real_total_integrand_graph hF.
have hRestricted:=@zero_extension_almost_equal R X (extended_real_line R) mu hm 0
  (smooth_compact_carrier K) _ _ hNormAlmost.
have hIntegral:=@measure_integral_almost_equal R X mu hm _ _ b%:E hLocal hRestricted.
exists b.
apply:(measure_integral_graph_equivalent _ hIntegral)=>x z.
rewrite real_total_integrand_graph.
case:(pselect (smooth_compact_carrier K x))=>hx.
- by rewrite (partial_function_zero_extension_on _ _ _ hx) !real_total_integrand_graph.
- rewrite (partial_function_zero_extension_off _ _ _ hx).
  change (z=(0:extended_real_line R) <-> (0:extended_real_line R)=z).
  split=>->; reflexivity.
Qed.
