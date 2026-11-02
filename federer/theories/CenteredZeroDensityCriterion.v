(** Federer (1969), 3.1.2, p. 212: the centered density-zero condition
    is an arbitrarily small relative-mass condition on small balls. This
    converse supports later measurable descriptions of the same condition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP MeasureUP MeasureBasic MeasureRestriction
  MeasureDerivates MeasureSetDensity CenteredBallRelations MetricClosedBalls
  CoveringRelationFineness CoveringFiniteLimitBounds MetricDiameter
  DerivationRatioDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_small_mass_zero_density]: supporting converse
    to the small-mass step in Federer 3.1.2, p. 212, from the definition
    of density in 2.9.12. The proof shrinks radius representations of
    small-diameter balls, so it also includes singleton metric spaces. *)
Theorem centered_small_mass_zero_density (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A : set X) a :
  is_measure phi ->
  (forall x r, (0<r)%R -> 0<phi (metric_closed_ball x r) /\
    phi (metric_closed_ball x r) \is a fin_num) ->
  (forall c : R, (0<c)%R -> exists d : R, (0<d)%R /\ forall r : R,
    (0<r)%R -> (r<d)%R -> phi (A `&` metric_closed_ball a r)<
      c%:E*phi (metric_closed_ball a r)) ->
  partial_function_graph (measure_set_density phi (@centered_closed_ball_relation R X) A) a 0.
Proof.
move=> hm hb hsmall.
have hdomain x S : centered_closed_ball_relation x S ->
    partial_function_domain (measure_ratio_function (measure_restrict phi A) phi) S.
  move=> [r [hr ->]]; have [hp hf] := hb x r hr.
  exists (measure_restrict phi A (metric_closed_ball x r)/phi (metric_closed_ball x r)).
  exact: measure_ratio_positive_finite_denominator hp hf.
apply: (@covering_finite_limit_of_small_values R X
  (@centered_closed_ball_relation R X) (measure_ratio_function (measure_restrict phi A) phi) a 0).
- apply: (@covering_relation_fine_mono R X (@centered_closed_ball_relation R X)
    (fun x S=>centered_closed_ball_relation x S /\
      partial_function_domain (measure_ratio_function (measure_restrict phi A) phi) S)
    a _ (@centered_closed_balls_fine R X a)).
  move=> S hS; split=> //; exact: hdomain a S hS.
- move=> e he; have [d [hd hs]] := hsmall e he.
  have hd2 : (0<d/2)%R by rewrite divr_gt0 // ltr0n.
  exists (d/2)%R; split=> // S y [r [hr ->]] hdiam hy.
  have hrep := closed_ball_small_radius_representation hr hd2 hdiam.
  have hminpos : (0<Num.min r (d/2))%R by rewrite lt_min hr hd2.
  have hminlt : (Num.min r (d/2)<d)%R.
    have hle : (Num.min r (d/2)<=d/2)%R by rewrite ge_min lexx orbT.
    lra.
  have hmass := hs _ hminpos hminlt; rewrite -hrep in hmass.
  have [hp hf] := hb a r hr.
  have hnum : phi (A `&` metric_closed_ball a r) \is a fin_num.
    rewrite (ge0_fin_numE (measure_nonnegative hm _)).
    apply: le_lt_trans (@measure_mono R _ _ hm
      (A `&` metric_closed_ball a r) (metric_closed_ball a r) (fun x hx=>hx.2)) _.
    by move: hf; rewrite (ge0_fin_numE (ltW hp)).
  have hq := @measure_ratio_positive_finite_denominator R X (measure_restrict phi A) phi
    (metric_closed_ball a r) hp hf.
  have hyE := partial_function_single_valued hy hq.
  have hy0 := @measure_ratio_nonnegative R X (measure_restrict phi A) phi _ y
    (measure_restrict_is_measure hm A) hm hy.
  split.
  + rewrite sub0r; apply: lt_le_trans _ hy0; by rewrite lte_fin oppr_lt0.
  + rewrite add0r hyE /measure_restrict.
    pose p := fine (phi (metric_closed_ball a r)).
    have hpe : phi (metric_closed_ball a r)=p%:E by rewrite /p fineK.
    have hp0 : (0<p)%R by move: hp; rewrite hpe lte_fin.
    rewrite -(fineK hnum) hpe inver (gt_eqF hp0) -EFinM lte_fin ltr_pdivrMr //.
    by move: hmass; rewrite -(fineK hnum) hpe -EFinM lte_fin.
Qed.
