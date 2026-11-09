(** Federer (1969), 3.3.1, printed p. 287: X(a,r,V,s) is the set
    of x with s^(-1) dist(x-a,V) < |x-a| < r. Specify membership
    using the independent infimum laws for distance to V. In particular
    no selected distance witness or projected formula is a hypothesis
    about a cone. The printed range is 0<r<=infinity and 0<s<1;
    the specification itself also makes sense at the other parameters. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerMetric InnerNorm MetricSetDistanceUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_structure_measure]: the standing assumption of
    Federer 3.3.1, p. 287: phi measures R^n and every closed set is
    phi measurable. Neither local finiteness nor Borel regularity
    is included in this definition. *)
Definition is_structure_measure (R:realType) n
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R):Prop:=
  is_measure phi /\ forall S,closed S->measure_measurable phi S.

(** Source for [is_structure_cone]: the first display of Federer
    3.3.1, p. 287, in words: the displacement has distance from the
    given plane strictly less than s times its norm and has norm
    strictly below r. The inverse-s form is retained exactly.
    All realizations of distance satisfying its infimum laws give
    the same membership; existence and uniqueness are proved later. *)
Definition is_structure_cone (R:realType) n k
    (V:G (R_n R n) k)
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (r: \bar R) (s:R)
    (C:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  forall d:inner_metric_space (@euclidean_inner_productP R n)->R,
    is_metric_set_distance [set x:inner_metric_space (@euclidean_inner_productP R n)|grassmann_val V x] d ->
    forall x,C x <->
      s^-1*d (x-a)<inner_norm (@euclidean_inner_productP R n) (x-a) /\
      ((inner_norm (@euclidean_inner_productP R n) (x-a))%:E<r)%E.
