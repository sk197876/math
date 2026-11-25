(** Federer (1969), 4.1.14, pp. 371–372: the
    continuous real majorant on its actual source
    has the standard real order topology. Compose
    the preceding norm-domain restriction law of
    3.1.1, p. 211, with the exact scalar
    metric identification used in 2.4.14, p. 88. *)
From mathcomp Require Import all_boot all_order all_algebra functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  MetricSubsetBackground NormClassZeroTopology ScalarNormExtendedEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_scalar_restriction_continuous]:
    the original scalar continuity hypothesis of
    Federer 4.1.14, p. 371, gives continuity
    into the standard R topology after restricting
    to U. The identity of the two scalar
    metric presentations is proved earlier; it is
    not an added topology or separability premise. *)
Theorem norm_class_zero_scalar_restriction_continuous
    (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    (U:set X) (sigma:X->R^o):
  norm_class_zero NX (fun t:R^o=>`|t|) U sigma->
  continuous (fun x:metric_subset (fun y:real_norm_metric_space hNX=>U y)=>
    (sigma (set_val x):R^o)).
Proof.
move=>hSigma.
pose UT:=metric_subset (fun y:real_norm_metric_space hNX=>U y).
pose scalar:=real_norm_metric_space (@scalar_absolute_value_norm R).
have hOwn:continuous (fun x:UT=>(sigma (set_val x):scalar)).
  exact:(@norm_class_zero_restriction_continuous R X R^o NX
    (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R) U sigma hSigma).
move=>x.
exact:(@continuous_comp UT scalar R^o
  (fun y:UT=>sigma (set_val y)) (fun t:scalar=>(t:R^o)) x
  (@hOwn x) (@scalar_norm_real_identity_continuous R (sigma (set_val x)))).
Qed.

Arguments norm_class_zero_scalar_restriction_continuous : clear implicits.
