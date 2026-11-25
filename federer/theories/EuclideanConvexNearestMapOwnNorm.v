(** Federer (1969), 4.1.16, pp. 373–374: the original
    nonexpanding retraction, in the same norm-metric interface
    as the actual current spaces. The nearest-point law is
    unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerConvex HilbertFormCompactness NormMetric
  NormMetricScaleContinuity EuclideanConvexNearestMapUP
  EuclideanConvexNearestMapLaws LipschitzUP LipschitzBasic
  MetricSubsetBackground MetricSubsetCorestriction RetractionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section EuclideanConvexNearestMapOwnNorm.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation hN := (inner_norm_real_norm hB).
Local Notation XT := (real_norm_metric_space hN).
Variable C : set X.
Variable P : X -> X.
Hypothesis hP : is_euclidean_convex_nearest_map C P.
Hypothesis hConvex : is_inner_convex C.

(** Source for [euclidean_convex_nearest_map_own_norm_bound]:
    Lip(P)<= 1, Federer 4.1.16, p. 373. Both metric
    presentations use the literal Euclidean distance; this law
    supplies the precise metric type of the current theory. *)
Theorem euclidean_convex_nearest_map_own_norm_bound :
  @is_metric_lipschitz_bound R XT XT setT P 1.
Proof.
split; first exact: ler01.
move=> x y _ _; rewrite mul1r !real_norm_metric_distanceE.
exact: (@euclidean_convex_nearest_map_nonexpanding R n C P hP hConvex x y).
Qed.

(** Source for [euclidean_convex_nearest_map_own_norm_lipschitz]:
    the same map is Lipschitzian on every original subset K,
    supporting the retraction argument in 4.1.16, p. 374.
    Empty K and a zero least Lipschitz constant are allowed. *)
Lemma euclidean_convex_nearest_map_own_norm_lipschitz (K : set XT) :
  is_metric_lipschitz K (P : XT -> XT).
Proof.
apply: metric_lipschitz_of_bound.
exact: (metric_lipschitz_bound_restrict (fun _ _=>Logic.I)
  euclidean_convex_nearest_map_own_norm_bound).
Qed.

(** Source for [euclidean_convex_nearest_map_image]: the
    nearest retraction sends every K containing C onto
    exactly C, supporting Federer 4.1.16, p. 374. *)
Lemma euclidean_convex_nearest_map_image (K : set XT) :
  C `<=` K -> P @` K=C.
Proof.
move=> hCK; apply/seteqP; split.
- move=> y [x hx <-].
  exact: (@euclidean_convex_nearest_map_range R n C P hP x).
- move=> y hy; exists y; first exact: hCK y hy.
  exact: (@euclidean_convex_nearest_map_fixed R n C P hP y hy).
Qed.

(** Source for [euclidean_convex_nearest_map_compact_retraction]:
    the nearest map retracts every K containing C onto C,
    Federer 4.1.16, pp. 373–374. Neither C nor K is
    assumed bounded in this supporting statement. Continuity is
    on the actual subspaces, as required by 4.1.15. *)
Theorem euclidean_convex_nearest_map_compact_retraction
    (K : set XT) (hCK : C `<=` K) :
  is_metric_retraction K C (P : XT -> XT).
Proof.
pose hRange := fun (x:XT) (_:K x) =>
  @euclidean_convex_nearest_map_range R n C P hP x.
pose hFixed := fun (x:XT) (hx:C x) =>
  @euclidean_convex_nearest_map_fixed R n C P hP x hx.
refine (@Build_is_metric_retraction R XT K C P hCK hRange hFixed _).
apply: metric_subset_corestriction_continuous.
  apply: (@metric_fixed_lipschitz_continuous R (metric_subset K) XT
    (fun x=>P (val x)) 1 ler01).
  move=> x y; rewrite mul1r metric_subset_distanceE
    !real_norm_metric_distanceE.
  exact: (@euclidean_convex_nearest_map_nonexpanding R n C P hP hConvex
    (val x) (val y)).
Qed.
End EuclideanConvexNearestMapOwnNorm.
