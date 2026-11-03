(** Federer (1969), 3.2.41, printed p. 278, last proof paragraph:
    density-one hulls commute with translations. This supporting
    isometric finite-density transport retains the actual outer
    measures and partial quotient graphs. No measurability of the
    original set is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealConventions PartialFunctionUP MeasureUP MeasureRestriction
  MeasureDerivates MeasureSetDensity MetricClosedBalls CenteredBallRelations
  CoveringRelationFineness CoveringFiniteLimitBounds MetricDiameter
  MetricIsometricImageGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [centered_finite_density_isometric_preimage]: supporting
    translation of the density-one hull in Federer 3.2.41, p. 278.
    A measure-preserving bijective isometry transports every finite
    centered density, with its exact partial arithmetic domain. The
    hypotheses are independent geometric and outer-measure laws. *)
Theorem centered_finite_density_isometric_preimage (R:realType)
    (X Y:metricType R) (mu:set X->\bar R) (nu:set Y->\bar R)
    (f:X->Y) (g:Y->X) (A:set Y) (a:X) (c:R):
  (forall x,g (f x)=x) ->(forall y,f (g y)=y) ->
  (forall x z,mdist (f x) (f z)=mdist x z) ->
  (forall B,nu B=mu (f @^-1` B)) ->
  (forall x r,(0<r)%R ->0<mu (metric_closed_ball x r) /\
    mu (metric_closed_ball x r) \is a fin_num) ->
  (forall y r,(0<r)%R ->0<nu (metric_closed_ball y r) /\
    nu (metric_closed_ball y r) \is a fin_num) ->
  partial_function_graph (measure_set_density nu (@centered_closed_ball_relation R Y) A) (f a) c%:E ->
  partial_function_graph (measure_set_density mu (@centered_closed_ball_relation R X)
    (f @^-1` A)) a c%:E.
Proof.
move=> hgf hfg hIso hPush hMu hNu hA.
have hPre r:f @^-1` metric_closed_ball (f a) r=metric_closed_ball a r.
  apply/seteqP; split=> x; change (mdist (f a) (f x)<=r ->mdist a x<=r)%R ||
    change (mdist a x<=r ->mdist (f a) (f x)<=r)%R; by rewrite hIso.
have hImage r:f @` metric_closed_ball a r=metric_closed_ball (f a) r.
  apply/seteqP; split.
  - move=> y [x hx <-]; change (is_true (mdist (f a) (f x)<=r)%R); by rewrite hIso.
  - move=> y hy; exists (g y); last exact:hfg.
    change (is_true (mdist a (g y)<=r)%R); by rewrite -hIso hfg.
have hDomain x S:centered_closed_ball_relation x S ->
    partial_function_domain (measure_ratio_function (measure_restrict mu (f @^-1` A)) mu) S.
  move=> [r [hr ->]]; have [hp hf]:=hMu x r hr.
  exists (measure_restrict mu (f @^-1` A) (metric_closed_ball x r)/mu (metric_closed_ball x r)).
  exact:measure_ratio_positive_finite_denominator hp hf.
apply:(@covering_finite_limit_of_small_values R X (@centered_closed_ball_relation R X)
  (measure_ratio_function (measure_restrict mu (f @^-1` A)) mu) a c).
- apply:(@covering_relation_fine_mono R X (@centered_closed_ball_relation R X)
    (fun x S=>centered_closed_ball_relation x S /\partial_function_domain
      (measure_ratio_function (measure_restrict mu (f @^-1` A)) mu) S) a _
    (@centered_closed_balls_fine R X a)).
  move=> S hS; split=>//; exact:hDomain a S hS.
- move=> e he.
  have [d [hd hs]]:=@covering_finite_limit_small_values R Y
    (@centered_closed_ball_relation R Y) (measure_ratio_function (measure_restrict nu A) nu)
    (f a) c e hA he.
  exists d; split=>// S y [r [hr ->]] hDiam hy.
  have hS':centered_closed_ball_relation (f a) (metric_closed_ball (f a) r) by exists r.
  have hDiam':extended_metric_diameter (metric_closed_ball (f a) r)<d%:E.
    by rewrite -hImage (@metric_isometric_image_diameter R X Y f hIso).
  have hy':partial_function_graph (measure_ratio_function (measure_restrict nu A) nu)
      (metric_closed_ball (f a) r) y.
    change (extended_divide (nu (A `&` metric_closed_ball (f a) r))
      (nu (metric_closed_ball (f a) r))=Some y).
    rewrite !hPush preimage_setI !hPre.
    exact hy.
  exact:hs _ y hS' hDiam' hy'.
Qed.
