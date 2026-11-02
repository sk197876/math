(** Federer (1969), 3.1.4, p. 214: the jointly parameterised
    coordinate quotient [f(x+t e_i)-f(x)]/t. The original graph and
    the nonzero scalar increment specify its exact domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerMetric EuclideanOneCoordinate RealMetricBackground PartialFunctionUP
  PartialFunctionBasic PartialFunctionPrecomposition PartialFunctionSourceRestriction
  PartialFunctionPair PartialFunctionPostcomposition MeasurableRealArithmetic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_joint_coordinate_quotient]: the quotient
    defining g_i in Federer 3.1.4, p. 214, before taking an approximate
    order limit. A pair belongs to its domain exactly when t is nonzero
    and both function values exist. The scalar parameter is represented
    by its one-dimensional Euclidean coordinate vector. *)
Definition euclidean_joint_coordinate_quotient (R : realType) n (i : 'I_n)
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R n)) (real_line_metric R)) :=
  partial_function_source_restrict
    [set p : inner_metric_space (@euclidean_inner_productP R n)*
      inner_metric_space (@euclidean_inner_productP R 1) | euclidean_one_project p.2 != 0]
    (partial_real_function_multiply
      (partial_function_total (fun p=>((euclidean_one_project p.2)^-1 : real_line_metric R)))
      (partial_real_function_subtract
        (partial_function_precompose (fun p=>p.1+euclidean_one_project p.2*:(@coordinate_basis R n i)) f)
        (partial_function_precompose (fun p=>p.1) f))).

(** Source for [euclidean_joint_coordinate_quotient_graph]: exact
    graph of the displayed quotient in Federer 3.1.4, p. 214. No value
    at t=0 or outside either input domain is assigned. *)
Lemma euclidean_joint_coordinate_quotient_graph (R : realType) n (i : 'I_n)
    (f : partial_function (inner_metric_space (@euclidean_inner_productP R n)) (real_line_metric R)) x t z :
  partial_function_graph (euclidean_joint_coordinate_quotient i f) (x,t) z <->
  euclidean_one_project t != 0 /\ exists u v,
    partial_function_graph f (x+euclidean_one_project t*:(@coordinate_basis R n i)) u /\
    partial_function_graph f x v /\ z=(euclidean_one_project t)^-1*(u-v).
Proof.
split.
- move=> [ht [[a b] [[ha [[u v] [[hu hv] hsub]]] hprod]]].
  split=> //; exists u,v; split=> //; split=> //.
  by rewrite -hprod -ha -hsub.
- move=> [ht [u [v [hu [hv ->]]]]]; split=> //.
  exists ((euclidean_one_project t)^-1,u-v); split; last by [].
  split; first by [].
  exists (u,v); by split=> //; split.
Qed.
