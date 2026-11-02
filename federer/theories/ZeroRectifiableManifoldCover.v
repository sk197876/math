(** Federer (1969), 3.2.29, p. 267:
    the zero-dimensional boundary uses the finite-set
    convention of 3.2.14, p. 252, and isolated
    point manifolds of 3.1.19, p. 231. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanSubmanifoldUP
  SubmanifoldBasicLaws ZeroSubmanifold RectifiableSetUP RectifiableZeroDimension
  RectifiableManifoldCoverUP HausdorffMeasure MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [singleton_zero_submanifold]: every singleton
    is a zero-dimensional submanifold of every finite
    class, supporting the boundary case of Federer
    3.2.29, p. 267, by 3.1.19, p. 231. *)
Lemma singleton_zero_submanifold (R:realType) n k (x:R_n R n):
  @is_euclidean_submanifold R n 0 k [set x].
Proof.
apply:isolated_points_zero_submanifold=>b hb.
split; first exact hb.
exists 1; split; first exact:ltr01.
move=>h _ hy; exact:eq_trans hy (esym hb).
Qed.

(** Source for [zero_rectifiable_manifold_cover]: the
    zero-dimensional forward implication of Federer
    3.2.29, p. 267. The countable family
    covers the supplied countably rectifiable carrier;
    only the already given null remainder of W is
    used, without replacing an almost cover by exact
    containment or adding a finite-mass hypothesis. *)
Theorem zero_rectifiable_manifold_cover (R:realType) n k (W:set (R_n R n)):
  is_countably_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) 0) 0 W ->
  has_countable_submanifold_measure_cover 0 k W.
Proof.
move=>[_ [S [hS hWS]]].
have hCount:countable S:=(@countably_zero_rectifiable_countable R
  (inner_metric_space (@euclidean_inner_productP R n)) S).1 hS.
pose C:=(fun x:R_n R n=>[set x]) @` S.
have hUnion:(\bigcup_(A in C) A)=S.
  apply/seteqP; split=>x.
  - move=>[A [y hy <-] hx]; by rewrite hx.
  - move=>hx; exists [set x]; first by exists x.
    reflexivity.
exists C; constructor.
- exact:sub_countable (card_image_le _ _) hCount.
- move=>A [x hx <-]; exact:singleton_zero_submanifold.
- by rewrite hUnion.
Qed.
