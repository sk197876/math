(** Federer (1969), 4.1.2, p. 347: a
    measurable locally norm-integrable field may have a
    proper conull domain, under 2.3.1–2, pp. 72–73.
    This definition preserves that original domain before
    proving the total-representative reduction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition
  MeasureUP MeasurableFunctionUP MeasureSubsetIntegral SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_locally_integrable_partial_vector_field]: the
    exact measurable-function and compact norm-integral hypotheses
    of Federer 4.1.2, p. 347, with
    the partial-domain convention of 2.3.1–2 retained. *)
Record is_locally_integrable_partial_vector_field (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (f:partial_function X (real_norm_metric_space hNY)):Prop:={
  (** Source for [locally_integrable_partial_measurable]: the original
      measurable partial field of Federer 4.1.2, p. 347. *)
  locally_integrable_partial_measurable:is_measure_measurable_function mu f;
  (** Source for [locally_integrable_partial_compact_norm]: finite norm
      integral on every compact subset in Federer 4.1.2,
      p. 347, without extending the original partial domain. *)
  locally_integrable_partial_compact_norm:forall K:smooth_compact_set hNX (fun _=>True),
    exists b:R,is_measure_subset_integral mu (smooth_compact_carrier K)
      (partial_function_postcompose f (fun y=>(NY y)%:E:extended_real_line R)) b%:E
}.
