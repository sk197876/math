(** Federer (1969), 3.3.19, p. 303: independent
    laws for the radial retraction used in the original
    boundary argument. Existence is proved from Chapter 1
    nearest points, without assuming the Chapter 4 reference. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric MetricClosedBalls LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_radial_ball_retraction]: independent
    range, fixed-point, nonexpansion and radial-ray laws
    for the actual f in 3.3.19, p. 303.
    They do not assume any boundary-point selection,
    finite cover, hit count or measure conclusion. *)
Record is_radial_ball_retraction (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B)
    (z:inner_metric_space hB) (r:R)
    (P:inner_metric_space hB->inner_metric_space hB):Prop:={
  (** Source for [radial_ball_retraction_range]: original
      ball-valued range of f, 3.3.19, p. 303. *)
  radial_ball_retraction_range:forall x,metric_closed_ball z r (P x);
  (** Source for [radial_ball_retraction_fixed]: f(x)=x
      on the original ball, 3.3.19, p. 303. *)
  radial_ball_retraction_fixed:forall x,metric_closed_ball z r x ->P x=x;
  (** Source for [radial_ball_retraction_nonexpanding]: the
      printed Lipschitz bound one, 3.3.19, p. 303. *)
  radial_ball_retraction_nonexpanding:is_metric_lipschitz_bound setT P 1;
  (** Source for [radial_ball_retraction_ray]: the original
      radial formula on every outward unit ray,
      3.3.19, p. 303. *)
  radial_ball_retraction_ray:forall (u:inner_metric_space hB) (d:R),
    inner_norm hB u= 1 ->r<=d ->P (z+d*:u)=z+r*:u
}.
