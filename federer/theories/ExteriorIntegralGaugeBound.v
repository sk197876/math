(** Federer (1969), 2.10.37, printed p. 198: take the supremum over all
    endpoint products in the convex source, then multiply by alpha(m)
    2^(-m). This yields the generator comparison defining the claimed
    T^m/Q_t^m measure inequality. All suprema and norms use their existing
    opaque specifications. The supporting Suslin premise is automatic for
    the open convex generators of Q_t. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex SuslinSetUP
  ExteriorDiameterUP ExteriorDiameterLaws ExteriorDiameter ExteriorMeasureGauge HausdorffDiameterCost
  IntegralGeometricGauge ConvexIntegralEndpointBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_exterior_diameter_integral_gauge_bound]: supporting
    supremum of the last endpoint inequality in
    2.10.37, p. 198. The auxiliary adjoined
    zero is bounded by gauge nonnegativity, so
    the empty convex source is also covered. *)
Theorem convex_exterior_diameter_integral_gauge_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> (1<=t)%E -> is_inner_convex S -> is_suslin_set R S ->
  (extended_exterior_diameter m S <=
    (m`!)%:R%:E*@integral_geometric_gauge R n m hmn t S)%E.
Proof.
move=> hm ht hS hs.
have hc : (0<=(m`!)%:R%:E :> \bar R)%E by rewrite lee_fin; exact: ler0n.
have hg := @integral_geometric_gauge_nonnegative R n m hmn t ht S hs.
apply: (@exterior_diameter_least_bound R n m S (extended_exterior_diameter m S)
  _ (extended_exterior_diameter_specification m S) (mule_ge0 hc hg)).
move=> a b ha hb; exact: (@convex_integral_geometric_endpoint_bound R n m hmn t S a b
  hm ht hS hs ha hb).
Qed.

(** Source for [convex_exterior_cost_integral_gauge_bound]: direct
    cost comparison implicit in the corollary
    2.10.37, p. 198, after taking the
    endpoint supremum. The coefficient is the
    existing alpha(m)/2^m normalization times m!;
    infinite gauge values are retained. *)
Theorem convex_exterior_cost_integral_gauge_bound (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (0<m)%N -> (1<=t)%E -> is_inner_convex S -> is_suslin_set R S ->
  (exterior_diameter_cost m S <=
    ((hausdorff_normalisation R m)*(m`!)%:R)%:E*
      @integral_geometric_gauge R n m hmn t S)%E.
Proof.
move=> hm ht hS hs.
have hc : (0<=(hausdorff_normalisation R m)%:E)%E.
  rewrite lee_fin; exact: ltW (@hausdorff_normalisation_positive R m).
have hh := lee_wpmul2l hc
  (@convex_exterior_diameter_integral_gauge_bound R n m hmn t S hm ht hS hs).
by rewrite muleA -EFinM in hh.
Qed.
