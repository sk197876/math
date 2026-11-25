(** General topology supporting the coordinate transfer of the
    counterexample in Federer (1969), 2.8.20, p. 152. Small sets containing
    a fixed point have small image diameters under a map continuous at that
    point. This transfers the based fineness definition of 2.8.16, p. 151,
    without imposing a uniform continuity hypothesis. Source context and the
    rectangle proof comparison: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ring lra.
From Federer Require Import MetricDiameterUP MetricDiameter MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_based_small_diameter_images]: supporting
    coordinate-transfer fact for Federer 2.8.20, p. 152,
    using the based fineness convention of 2.8.16, p. 151.
    The containing base point is essential; continuity at unrelated
    points would not control a small set's image. *)
Lemma continuous_based_small_diameter_images (R : realType) (X Y : metricType R)
    (f : X -> Y) (x : X) (e : R) :
  continuous f -> (0<e)%R -> exists d : R, (0<d)%R /\
    forall S : set X, S x -> extended_metric_diameter S<d%:E ->
      extended_metric_diameter (f @` S)<e%:E.
Proof.
move=> hf he.
pose eta := (e/3)%R.
have heta : (0<eta)%R by rewrite /eta divr_gt0 // ltr0n.
have hsmall : (eta+eta<e)%R.
  rewrite /eta -mulrDl ltr_pdivrMr ?ltr0n //.
  have he3 : (e*3=e+e+e)%R by ring.
  rewrite he3; lra.
pose W := [set y : Y | (mdist (f x) y<eta)%R].
have hW : nbhs (f x) W.
  apply: open_nbhs_nbhs; split; first exact: metric_open_ball_open.
  by rewrite /W /= mdistxx.
have hpre : nbhs x (f @^-1` W) := hf x W hW.
have [d hd hsub] := (metricType_numDomainType.nbhs_mdistP x _).1 hpre.
exists d; split=> // S hx hdiam.
have hball y : S y -> (mdist (f x) (f y)<eta)%R.
  move=> hy; apply: hsub.
  have hb := metric_diameter_upper (extended_metric_diameter_specification S) hx hy.
  by have hh := le_lt_trans hb hdiam; rewrite lte_fin in hh.
have hbound : extended_metric_diameter (f @` S)<=(eta+eta)%:E.
  apply: (metric_diameter_least (extended_metric_diameter_specification (f @` S))).
  - by rewrite lee_fin addr_ge0 ?ltW.
  - move=> y z [u hu <-] [v hv <-]; rewrite lee_fin.
    have h1 := ltW (hball u hu); have h2 := ltW (hball v hv).
    rewrite (metric_sym (f x) (f u)) in h1.
    exact: le_trans (metric_triangle (f u) (f x) (f v)) (lerD h1 h2).
apply: le_lt_trans hbound _; by rewrite lte_fin.
Qed.
