(** Supporting pointwise projected-volume identities for Federer (1969),
    2.10.5(2), p. 173: the closed convex alternative and continuity for
    bounded open convex generators. Retain each individual p, strengthening
    the already proved supremum-gauge identity of 2.10.4(2), p. 172.
    Projection commutes with homotheties, and strict homothetic enlargement
    of an open convex set contains its closure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionMetric EuclideanProjectionSpace EuclideanLebesgueDimensions MeasureUP
  ProjectedVolumeMeasurability ProjectedVolumeBounds ProjectedVolumeDilation
  AffineDilation RealDilationSlack ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projected_volume_function_dilation]:
    supporting individual-projection homothety law
    for Federer 2.10.5(2), p. 173, from
    the actual Lebesgue transformation theorem
    2.7.16(1), pp. 134–135. Arbitrary sets
    and infinite projected volumes are included. *)
Lemma projected_volume_function_dilation (R : realType) (n m : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m)
    (a : inner_metric_space (@euclidean_inner_productP R n)) (t : R) :
  projected_volume_function ((@affine_dilation R (R_n R n) a t) @` S) p =
    (`|t|^+m)%R%:E * projected_volume_function S p.
Proof.
have hi : euclidean_projection_linear p @` ((@affine_dilation R (R_n R n) a t) @` S) =
    (@affine_dilation R (R_n R m) (euclidean_projection_linear p a) t) @`
      (euclidean_projection_linear p @` S).
  apply/seteqP; split=> y.
  - move=> [z [x hx <-] <-]; exists (euclidean_projection_linear p x); first by exists x.
    by rewrite /affine_dilation linearD !linearZ.
  - move=> [z [x hx <-] <-]; exists (affine_dilation a t x); first by exists x.
    by rewrite /affine_dilation linearD !linearZ.
rewrite /projected_volume_function hi; exact: euclidean_affine_dilation_volume.
Qed.

(** Source for [projected_volume_function_open_convex_closure]:
    supporting unchanged individual volume on closing
    an open convex generator in Federer 2.10.5(2),
    p. 173. No boundedness assumption is needed
    for this identity; infinite values remain allowed. *)
Theorem projected_volume_function_open_convex_closure (R : realType) (n m : nat)
    (U : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : orthogonal_projection_metric_space R n m) :
  open U -> @is_inner_convex R (R_n R n) U ->
  projected_volume_function (closure U) p=projected_volume_function U p.
Proof.
move=> ho hc.
case: (pselect (U !=set0))=> [[a ha]|hno]; last first.
  have hU0 : U=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hno; by exists x.
  by rewrite hU0 closure0.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact: projected_volume_function_mono (@subset_closure _ U).
have hn := projected_volume_function_nonnegative U p.
case he: (projected_volume_function U p) hn=> [c| |] hn; last 2 first.
- exact: leey.
- by [].
rewrite leNgt; apply/negP=> hbad.
have [q [hcq hqcl]] := @extended_rationals_order_dense R c%:E
  (projected_volume_function (closure U) p) hbad.
have hcb : (c<ratr q)%R by move: hcq; rewrite lte_fin.
have [t [ht hcost]] := @real_positive_dilation_cost_slack R m c (ratr q) hcb.
have ht0 : (0<t)%R := lt_trans ltr01 ht.
have hsub := @open_convex_closure_dilation_cover R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) U a t ho hc ha ht.
have hh := @projected_volume_function_mono R n m (closure U)
  ((@affine_dilation R (R_n R n) a t) @` U) p hsub.
rewrite projected_volume_function_dilation he (ger0_norm (ltW ht0)) -EFinM in hh.
have hlt : (t^+m*c)%R%:E<(ratr q : R)%:E by rewrite lte_fin mulrC.
by have := lt_trans (le_lt_trans hh hlt) hqcl; rewrite ltxx.
Qed.
