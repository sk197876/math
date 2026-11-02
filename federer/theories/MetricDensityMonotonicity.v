(** Federer (1969), 3.2.19, p. 256: transfer density bounds
    between restricted measures and between Hausdorff and spherical measure.
    These supporting order laws use the existing abstract radius limits. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds PositiveRadiusLimits MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_limits_monotone]: supporting order step
    in the restricted-density bounds of Federer 3.2.19, p. 256.
    Only positive radii enter either limit; infinite values are retained. *)
Lemma positive_radius_limits_monotone (R : realType) (f g : R -> \bar R) :
  (forall r : R, (0<r)%R -> f r<=g r) ->
  positive_radius_lower_limit f<=positive_radius_lower_limit g /\
  positive_radius_upper_limit f<=positive_radius_upper_limit g.
Proof.
move=> hfg; split.
- apply: extended_real_sup_least=> b [e [he ->]].
  apply: (le_trans _ (positive_radius_lower_ge_level g he)).
  apply: extended_real_inf_greatest=> y [r [hr ->]].
  have hf : positive_radius_values f e (f r) by exists r.
  exact: (le_trans (extended_real_inf_lower hf) (hfg r (andP hr).1)).
- apply: extended_real_inf_greatest=> b [e [he ->]].
  apply: (le_trans (positive_radius_upper_le_level f he) _).
  apply: extended_real_sup_least=> y [r [hr ->]].
  have hg : positive_radius_values g e (g r) by exists r.
  exact: (le_trans (hfg r (andP hr).1) (extended_real_sup_upper hg)).
Qed.

(** Source for [metric_densities_monotone]: supporting comparison of
    H^m restrictions and the spherical upper-density estimate in Federer
    3.2.19, p. 256. The denominator is positive at every radius
    used in the limit, independently of either measure's ball mass. *)
Lemma metric_densities_monotone (R : realType) (X : metricType R) m
    (mu nu : set X -> \bar R) a :
  (forall B, mu B<=nu B) ->
  lower_metric_density m mu a<=lower_metric_density m nu a /\
  upper_metric_density m mu a<=upper_metric_density m nu a.
Proof.
move=> hOrder; apply: positive_radius_limits_monotone=> r hr.
rewrite /metric_ball_density.
apply: lee_wpmul2r; last exact: hOrder.
rewrite inve_ge0 lee_fin; exact: ltW (metric_ball_density_denominator_positive m hr).
Qed.
