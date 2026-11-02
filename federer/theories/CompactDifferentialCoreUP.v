(** Federer (1969), 3.2.38, pp. 274--275: independent laws
    for a large compact good-point core used in the source cube proof. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialContinuityUP EuclideanUniformRemainderPoints.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_compact_differential_core]: supporting good-point
    specification for Federer 3.2.38, pp. 274--275. The proof uses
    the earlier Lusin theorem 2.3.5 to make the scalar Jacobian
    continuous on a large compact E, then sums its values only over
    E with the remaining cube mass as error. This replaces the printed
    uniform mean selection from 2.9.9; the cube and Steiner argument,
    original source, and final theorem hypotheses are retained. *)
Definition is_compact_differential_core (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (J:inner_metric_space (@euclidean_inner_productP R m)->real_line_metric R)
    (C:set (inner_metric_space (@euclidean_inner_productP R m))) (e budget d:R)
    (E:set (inner_metric_space (@euclidean_inner_productP R m))):Prop:=
  compact E /\E `<=` C /\
  (@euclidean_lebesgue_measure R m (C `\` E)<budget%:E)%E /\0<d /\
  E `<=`euclidean_uniform_remainder_points f e d /\
  partial_function_continuous_on E (partial_function_total J).
