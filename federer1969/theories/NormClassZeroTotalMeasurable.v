(** Federer (1969), 4.1.2, p. 347: continuous
    kernel sections are measurable for the original Borel
    measure. This adapter combines the class-zero topology
    of 3.1.1 and the measurable composition law of 2.3.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground NormClassOneUP NormClassZeroTopology
  ScalarNormExtendedEmbedding PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalBasic BorelFunctionBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_total_measurable]: an actual
    continuous normed map is measurable when the source
    open sets are measurable, supporting the kernel
    integrals in Federer 4.1.2, p. 347. *)
Theorem norm_class_zero_total_measurable (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:set X->\bar R) (hm:is_measure mu)
    (hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A) (f:X->Y):
  norm_class_zero NX NY (fun _=>True) f ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hNY))).
Proof.
move=>hClass.
have hContinuous:continuous (fun x:real_norm_metric_space hNX=>(f x:real_norm_metric_space hNY)).
  move=>x; exact:(@norm_class_zero_continuous_at R X Y NX NY hNX hNY (fun _=>True) f x hClass Logic.I).
constructor.
- rewrite partial_function_total_domain; exact:measure_almost_everywhere_true hm.
- move=>A hA; rewrite partial_function_total_preimage; apply:hOpen.
  move:hContinuous; rewrite continuousP=>hRaw; exact:hRaw A hA.
Qed.

(** Source for [norm_class_zero_scalar_real_measurable]: the
    finite real kernel section is measurable in the
    original scalar topology, supporting Federer 4.1.2,
    p. 347. The norm and scalar topologies agree. *)
Theorem norm_class_zero_scalar_real_measurable (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (mu:set X->\bar R) (hm:is_measure mu)
    (hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A) (f:X->R):
  norm_class_zero NX (fun t:R^o=>`|t|) (fun _=>True) f ->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_line_metric R))).
Proof.
move=>hClass.
have hMeas:=@norm_class_zero_total_measurable R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) mu hm hOpen f hClass.
have h:=@measurable_total_borel_postcomposition R X
  (real_norm_metric_space (@scalar_absolute_value_norm R)) (real_line_metric R) mu hm
  (fun x=>(f x:real_norm_metric_space (@scalar_absolute_value_norm R)))
  (fun y=>(y:real_line_metric R)) hMeas
  (continuous_borel_function (@scalar_norm_real_identity_continuous R)).
exact h.
Qed.
