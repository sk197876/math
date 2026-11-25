(** Federer (1969), 3.3.19, p. 305: independent laws
    for the original partially defined radial direction eta_n.
    Our index j refers to parent level G_(j+3).
    Its domain is exactly the next original level union. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscTreeTopology CircularDiscRadialDirection PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Laws.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [is_circular_disc_radial_map]: the exact domain
    and pointwise original formula for eta_n, 3.3.19,
    p. 305. No direction at an undefined point, angular
    visitation, measure or density conclusion is assumed. *)
Record is_circular_disc_radial_map (H:nat->{fset E}) j
    (eta:partial_function E E):Prop:={
  (** Source for [circular_radial_map_domain]: eta_n has
      domain precisely union G_n in 3.3.19, p. 305. *)
  circular_radial_map_domain:forall x,
    partial_function_domain eta x <->circular_disc_level_union H j.+1 x;
  (** Source for [circular_radial_map_value]: the value at x
      in the original parent B(z,rho_(n-1)) is exactly
      (x-z)/|x-z|, 3.3.19, p. 305. *)
  circular_radial_map_value:forall x z v,z \in H j ->
    metric_closed_ball z (@FactorialDiscScales.radius R j) x ->
    partial_function_graph eta x v ->v=circular_disc_radial_direction z x
}.
End Laws.
