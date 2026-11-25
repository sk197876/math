(** Federer (1969), 3.2.36, p. 273: transport actual distances
    and whole tube sets along distance-preserving maps. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets functions topology.
From Federer Require Import MetricSetDistanceUP RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_isometric_image_distance]: supporting the
    isometry invariance deduction in Federer 3.2.36, p. 273.
    The independent distance infimum laws prove d_(fA)(f x)=d_A(x)
    for every metric isometric embedding. No surjectivity, compactness,
    convexity or chosen nearest-point map is required. *)
Lemma metric_isometric_image_distance (R:realType) (X Y:metricType R)
    (f:X->Y) (A:set X) (d:X->R) (e:Y->R):
  (forall x y,mdist (f x) (f y)=mdist x y) ->
  is_metric_set_distance A d ->is_metric_set_distance (f @` A) e ->
  forall x,e (f x)=d x.
Proof.
move=>hMetric hd he x; apply/eqP; rewrite eq_le; apply/andP; split.
- apply:(@metric_set_distance_greatest R X A d hd x (e (f x)))=>a ha.
  rewrite -(hMetric x a); apply:(@metric_set_distance_lower R Y (f @` A) e he (f x) (f a)).
  by exists a.
- apply:(@metric_set_distance_greatest R Y (f @` A) e he (f x) (d x))=>y [a ha <-].
  rewrite hMetric; exact:(@metric_set_distance_lower R X A d hd x a ha).
Qed.

(** Source for [metric_bijective_isometry_tube_image]: the exact
    whole tube image used for isometry invariance of the Steiner
    coefficients in Federer 3.2.36, p. 273. Surjectivity and
    actual distance transport prove equality at every radius, without
    measurability or finiteness assumptions on either source set. *)
Lemma metric_bijective_isometry_tube_image (R:realType) (X Y:metricType R)
    (f:X->Y) (A:set X) (d:X->R) (e:Y->R) (r:R):
  (forall x y,mdist (f x) (f y)=mdist x y) ->(forall y,exists x,f x=y) ->
  is_metric_set_distance A d ->is_metric_set_distance (f @` A) e ->
  f @` [set x|d x<r]=[set y|e y<r].
Proof.
move=>hMetric hSurj hd he.
have hDistance:=metric_isometric_image_distance hMetric hd he.
apply/seteqP; split.
- move=>y [x hx <-]; change (is_true (e (f x)<r)); by rewrite hDistance.
- move=>y hy; have [x hx]:=hSurj y; exists x=>//.
  change (is_true (d x<r)); by rewrite -(hDistance x) hx.
Qed.
