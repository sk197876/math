(** Federer (1969), 2.10.43, printed p. 201: for any new source point a, the
    balls B(f(x),|x-a|), x in the original domain, have a common point.
    Compactness of one ball and the finite-ball result prove the assertion
    for an arbitrary, possibly uncountable domain. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp reals classical_sets cardinality topology.
From Federer Require Import EuclideanInnerProduct InnerNorm InnerMetric MetricClosedBalls
  EuclideanClosedBallCompact CompactClosedFamilyIntersection KirszbraunFiniteBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_one_point_value]: direct
    one-new-point assertion of 2.10.43, p. 201.
    The original domain may be empty or uncountable.
    The new target value satisfies all original
    distance bounds, with no compactness premise on the domain. *)
Theorem kirszbraun_one_point_value (R : realType) m n
    (S : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (a : inner_metric_space (@euclidean_inner_productP R m)) :
  (forall x, S x -> x!=a) ->
  (forall x y, S x -> S y -> inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
    inner_norm (@euclidean_inner_productP R m) (x-y)) ->
  exists b, forall x, S x -> inner_norm (@euclidean_inner_productP R n) (b-f x)<=
    inner_norm (@euclidean_inner_productP R m) (x-a).
Proof.
move=> hnew hLip.
case: (pselect (S !=set0))=> [[x0 hx0]|hempty]; last first.
  exists 0=> x hx; exfalso; apply: hempty; by exists x.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose U := inner_metric_space (@euclidean_inner_productP R m).
pose C (x : U) : set E := metric_closed_ball (f x) (inner_norm (@euclidean_inner_productP R m) (x-a)).
have hcompact : compact (C x0) := @euclidean_closed_metric_ball_compact R n (f x0)
  (inner_norm (@euclidean_inner_productP R m) (x0-a)).
have hclosed x : S x -> closed (C x) by move=> hx; exact: metric_closed_ball_closed.
have hfinite (F : {fset U}) (hFS : forall x, x \in F -> S x) :
    exists b, forall x, x \in F -> C x b.
  have hnewF x : [set` F] x -> x!=a by move=> hx; exact: hnew x (hFS x hx).
  have hLipF x y : [set` F] x -> [set` F] y ->
      inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
      inner_norm (@euclidean_inner_productP R m) (x-y).
    move=> hx hy; exact: hLip x y (hFS x hx) (hFS y hy).
  have [b hb] := @kirszbraun_finite_ball_intersection R m n [set` F] f a (finite_fset F) hnewF hLipF.
  exists b=> x hx.
  change (is_true (inner_norm (@euclidean_inner_productP R n) (f x-b)<=
    inner_norm (@euclidean_inner_productP R m) (x-a))).
  by rewrite -[f x-b]opprB inner_normN; exact: hb x hx.
have [b hb] := @compact_closed_family_intersection [the topologicalType of E]
  [the choiceType of U] S C x0 hx0 hcompact hclosed hfinite.
exists b=> x hx.
have hh := hb x hx.
change (is_true (inner_norm (@euclidean_inner_productP R n) (f x-b)<=
  inner_norm (@euclidean_inner_productP R m) (x-a))) in hh.
by rewrite -[b-f x]opprB inner_normN.
Qed.
