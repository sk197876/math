(** Federer (1969), 3.4.4, p. 318: independent
    measure bounds supporting the printed real-degree product positivity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MetricClosedBalls RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_ball_growth_probability]: supporting probability
    measure formulation of the appeal to 2.10.27 and 2.10.28
    in 3.4.4, p. 318. Specify only the
    actual measure, its closed-set measurability, original source mass,
    and ball growth. A Hausdorff lower bound is a later theorem,
    not a defining field or a supplied hypothesis. *)
Record is_ball_growth_probability (R:realType) (X:metricType R)
    (A:set X) (K p:R) (mu:set X->\bar R):Prop:={
  (** Source for [ball_growth_measure]: the actual competing measure
      underlying the product bound in 3.4.4, p. 318. *)
  ball_growth_measure:is_measure mu;
  (** Source for [ball_growth_whole]: normalized finite whole mass in
      the product-measure proof of 3.4.4, p. 318. *)
  ball_growth_whole:mu setT= 1%E;
  (** Source for [ball_growth_closed_measurable]: closed-set measurability
      needed for actual product rectangles, 3.4.4, p. 318,
      through 2.6.2, p. 115. *)
  ball_growth_closed_measurable:forall C,closed C ->measure_measurable mu C;
  (** Source for [ball_growth_original_source_closed]: closedness of the
      original Cantor product source, supporting 3.4.4, p. 318. *)
  ball_growth_original_source_closed:closed A;
  (** Source for [ball_growth_original_source_mass]: positive original
      source mass before comparison with Hausdorff measure,
      supporting 3.4.4, p. 318. *)
  ball_growth_original_source_mass:mu A= 1%E;
  (** Source for [ball_growth_coefficient_positive]: a positive finite
      comparison coefficient in 3.4.4, p. 318. *)
  ball_growth_coefficient_positive:(0<K)%R;
  (** Source for [ball_growth_degree_nonnegative]: the nonnegative
      original real dimensions, 3.4.4, p. 318. *)
  ball_growth_degree_nonnegative:(0<=p)%R;
  (** Source for [ball_growth_bound]: the actual ball estimates derived
      from factor interval and volume bounds, supporting
      3.4.4, p. 318. Radius zero remains included. *)
  ball_growth_bound:forall x r,(0<=r)%R ->
    (mu (metric_closed_ball x r)<=(K*real_power r p)%R%:E)%E
}.
