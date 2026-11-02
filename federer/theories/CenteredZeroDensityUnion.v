(** Federer (1969), 3.1.7, p. 217: finite unions of
    density-zero exceptional sets permit restriction of derivative
    quotients to their actual domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureSplit MeasureSetDensity
  CenteredBallRelations MetricClosedBalls CenteredDensityTransport
  CenteredZeroDensityCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_zero_density_union]: the finite-exception
    step in Federer 3.1.7, p. 217, using the density
    definition of 2.9.12, p. 158. The metric statement
    applies to both the scalar quotient line and the ambient
    Euclidean space; it requires the actual positive finite ball laws. *)
Theorem centered_zero_density_union (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (A B : set X) a :
  is_measure mu ->
  (forall x r, (0<r)%R -> 0<mu (metric_closed_ball x r) /\
    mu (metric_closed_ball x r) \is a fin_num) ->
  partial_function_graph (measure_set_density mu
    (@centered_closed_ball_relation R X) A) a 0 ->
  partial_function_graph (measure_set_density mu
    (@centered_closed_ball_relation R X) B) a 0 ->
  partial_function_graph (measure_set_density mu
    (@centered_closed_ball_relation R X) (A `|` B)) a 0.
Proof.
move=> hm hballs hA hB.
apply: (centered_small_mass_zero_density hm hballs)=> c hc.
have hc2 : (0<c/2)%R by lra.
have [dA [hdA hsA]] := centered_zero_density_small_mass hm hballs hA hc2.
have [dB [hdB hsB]] := centered_zero_density_small_mass hm hballs hB hc2.
exists (Num.min dA dB)%R; split; first by rewrite lt_min hdA hdB.
move=> r hr; rewrite lt_min=> /andP [hrA hrB].
pose C := metric_closed_ball a r.
have hcover : (A `|` B) `&` C `<=` (A `&` C) `|` (B `&` C).
  by move=> x [[hx|hx] hxc]; [left|right]; split.
have hmass := @measure_binary_cover R X mu hm _ _ _ hcover.
have hsum := lteD (hsA r hr hrA) (hsB r hr hrB).
have hfin : mu C \is a fin_num := (hballs a r hr).2.
have he : (c/2)%R%:E*mu C+(c/2)%R%:E*mu C=c%:E*mu C.
  rewrite -(fineK hfin) -!EFinM -EFinD; congr (_%:E); lra.
by apply: le_lt_trans hmass _; rewrite -he.
Qed.
