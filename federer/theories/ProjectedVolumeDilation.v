(** Supporting volume control for the closed convex comparison in Federer
    (1969), 2.10.4(2), p. 172. Homotheties multiply each projected Lebesgue
    volume by |t|^m. Use the actual translation and linear-image theorems of
    2.7.16(1), pp. 134–135, before passing to the gauge's least-upper-bound
    laws. Source context and the absence of a corresponding. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanLinearMaps EuclideanLebesgueTranslation
  EuclideanLebesgueDeterminant AffineDilation CoordinateProjection ProjectedVolumeGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_affine_dilation_volume]: supporting
    homothety case of Federer 2.7.16(1), pp. 134–135,
    for the generator comparison in 2.10.4(2), p. 172.
    Arbitrary sets and singular parameter zero are included
    with the existing Euclidean empty-product convention. *)
Lemma euclidean_affine_dilation_volume (R : realType) (m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R m)))
    (a : inner_metric_space (@euclidean_inner_productP R m)) (t : R) :
  euclidean_lebesgue_measure m ((@affine_dilation R (R_n R m) a t) @` A)=
    (((`|t|^+m)%:E)*euclidean_lebesgue_measure m A)%E.
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R m).
pose d := @euclidean_diagonal_map R m (fun _ => t).
have hsc (x : E) : d x=t*:x.
  by apply/ffunP=> i; rewrite /d /euclidean_diagonal_map /euclidean_diagonal !ffunE.
have hi : (@affine_dilation R (R_n R m) a t) @` A=
    [set (1-t)*:a+y | y in (d @` A : set E)].
  apply/seteqP; split=> y.
  - move=> [x hx <-]; exists (d x); first by exists x.
    by rewrite /affine_dilation hsc.
  - move=> [z [x hx <-] <-]; exists x=> //; by rewrite /affine_dilation hsc.
rewrite hi euclidean_lebesgue_translation euclidean_lebesgue_linear_image.
by rewrite /d euclidean_diagonal_det prodr_const card_ord normrX.
Qed.

(** Source for [projected_volume_gauge_dilation_bound]:
    supporting gauge bound for strict homothetic
    enlargements in Federer 2.10.4(2), p. 172.
    Projection commutes with the affine formula, and
    the nonnegative factor bounds the entire supremum. *)
Theorem projected_volume_gauge_dilation_bound (R : realType) (n m : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n)))
    (a : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
  (projected_volume_gauge m ((@affine_dilation R (R_n R n) a t) @` A)<=
    ((`|t|^+m)%:E)*projected_volume_gauge m A)%E.
Proof.
apply: projected_volume_gauge_least_bound=> p hp.
have hi : p @` ((@affine_dilation R (R_n R n) a t) @` A)=
    (@affine_dilation R (R_n R m) (p a) t) @` (p @` A).
  apply/seteqP; split=> y.
  - move=> [z [x hx <-] <-]; exists (p x); first by exists x.
    by rewrite /affine_dilation linearD !linearZ.
  - move=> [z [x hx <-] <-]; exists (affine_dilation a t x); first by exists x.
    by rewrite /affine_dilation linearD !linearZ.
rewrite hi euclidean_affine_dilation_volume.
apply: lee_wpmul2l; last exact: projected_volume_gauge_projection_bound.
by rewrite lee_fin exprn_ge0 // normr_ge0.
Qed.
