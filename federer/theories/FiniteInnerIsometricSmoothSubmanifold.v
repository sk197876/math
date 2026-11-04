(** Federer (1969), 3.2.47, p. 283: supporting the
    actual smooth isotropy manifold in its
    original finite Hilbert Hom ambient space. Public orthonormal
    charts transport the proved Euclidean isometric image theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric FiniteInnerChartUP FiniteInnerSubmanifoldUP
  EuclideanSubmanifoldUP EuclideanIsometricSmoothSubmanifold FiniteInnerSmoothSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_isometric_smooth_submanifold_image]:
    actual isometric images retain the original submanifold
    dimension and common local charts of every order, supporting the
    isotropy assertion in 3.2.47, p. 283. Both ambient
    coordinate systems stay local and preserve the actual metric. *)
Theorem finite_inner_isometric_smooth_submanifold_image (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    mu (S:set V) (F:V->W) N
    (eY:Hom (R_n R N) W) (pY:Hom W (R_n R N)):
  is_finite_inner_chart C eY pY ->is_inner_smooth_submanifold B mu S ->
  (forall x y,mdist (F x:inner_metric_space hC) (F y)=
    mdist (x:inner_metric_space hB) y) ->
  is_inner_smooth_submanifold C mu (F @` S).
Proof.
move=>hTarget [M [e [p [hSource hS]]]] hMetric.
pose A:=inner_metric_space (@euclidean_inner_productP R M).
pose D:=inner_metric_space (@euclidean_inner_productP R N).
pose T:=fun z:R_n R M=>pY (F (e z)).
have hTMetric (x y:A):mdist (T x:D) (T y)=mdist x y.
  have hTargetDistance:mdist (T x:D) (T y)=mdist (F (e x):inner_metric_space hC) (F (e y)).
    rewrite !inner_metric_distanceE /T.
    change (inner_norm (@euclidean_inner_productP R N) (pY (F (e x))-pY (F (e y)))=
      inner_norm hC (F (e x)-F (e y))).
    by rewrite -linearB (finite_inner_chart_inverse_norm hC hTarget).
  rewrite hTargetDistance hMetric !inner_metric_distanceE.
  change (inner_norm hB (e x-e y)=inner_norm (@euclidean_inner_productP R M) (x-y)).
  by rewrite -linearB (finite_inner_chart_norm hB hSource).
have hImage:T @` (p @` S)=pY @` (F @` S).
  apply/seteqP; split=>y.
  - move=>[z [x hx <-] <-]; exists (F x); first by exists x.
    by rewrite /T (finite_inner_chart_right_inverse hSource).
  - move=>[z [x hx <-] <-]; exists (p x); first by exists x.
    by rewrite /T (finite_inner_chart_right_inverse hSource).
exists N,eY,pY; split; first exact hTarget.
rewrite -hImage.
exact (@euclidean_isometric_smooth_submanifold_image R M N mu (p @` S) T hS hTMetric).
Qed.
