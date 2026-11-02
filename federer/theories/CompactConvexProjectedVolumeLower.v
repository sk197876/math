(** Supporting lower continuity for Federer (1969), 2.10.5(2), p. 173, and
    its forward reference 3.2.36, p. 272. For compact convex K with positive
    projected volume, a projected affine basis supplies an actual section
    buffer. Images of strict contractions then lie in all nearby projection
    images. Their volumes approach the original volume by the homothety
    formula of 2.7.16(1), pp. 134–135. Zero projected volume is handled by
    nonnegativity. This gives the needed lower continuity without assuming
    Steiner's formula or joint Hausdorff-space continuity. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex
  EuclideanProjectionSpace ProjectedVolumeMeasurability EuclideanLebesgueDimensions
  EuclideanLebesgueBoxes PositiveProjectedVolumeBuffer ConvexProjectedContraction
  ProjectedVolumePointwiseClosure RealDilationSlack AffineDilation MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_convex_projected_volume_lower_neighbourhood]:
    supporting lower projection-volume neighbourhood
    for Federer 2.10.5(2), p. 173, and
    3.2.36, p. 272. Compact convex sets may
    have empty ambient interior; a positive
    projection supplies its own section buffer. *)
Theorem compact_convex_projected_volume_lower_neighbourhood (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n)))
    (p : euclidean_projection_space R n m) (b : R) :
  compact K -> @is_inner_convex R (R_n R n) K -> b%:E<projected_volume_function K p ->
  exists V : set (euclidean_projection_space R n m), open V /\ V p /\
    forall q, V q -> b%:E<projected_volume_function K q.
Proof.
move=> hK hc hb.
case: (ltP b 0%R)=> hb0.
- exists setT; split; first exact: openT.
  split=> // q _; apply: lt_le_trans _ (projected_volume_function_nonnegative K q).
  by rewrite lte_fin.
have hb0E : (0 : \bar R)<=b%:E by rewrite lee_fin.
have hpos : 0<projected_volume_function K p := le_lt_trans hb0E hb.
have hne : K !=set0.
  case: (pselect (K !=set0))=> hk //.
  exfalso; have hzero : K=set0.
    apply/seteqP; split=> x // hx; apply: hk; by exists x.
  by rewrite hzero projected_volume_function_empty ltxx in hpos.
have [a ha] := hne.
have [c [g [r [_ [hgp [hr hbuffer]]]]]] := @positive_projected_volume_convex_buffer R n m K p a hc ha hpos.
have hm := euclidean_lebesgue_is_measure R m.
have hvfin := @euclidean_compact_finite R m (euclidean_projection_linear p @` K)
  (@euclidean_projected_compact_image R n m p K hK).
have hnum : projected_volume_function K p \is a fin_num.
  by rewrite (ge0_fin_numE (projected_volume_function_nonnegative K p)).
pose v := fine (projected_volume_function K p).
have hv : projected_volume_function K p=v%:E by rewrite /v fineK.
have hbv : (b<v)%R by move: hb; rewrite hv lte_fin.
have [t [ht hcost]] := @real_positive_dilation_cost_slack R m b v hbv.
have ht0 : (0<t)%R := lt_trans ltr01 ht.
pose s := t^-1%R.
have hs : (0<s)%R by rewrite /s invr_gt0.
have hs1 : (s<1)%R by rewrite /s invf_lt1.
have hsp : b%:E<(s^+m)%R%:E*projected_volume_function K p.
  rewrite hv -EFinM lte_fin /s exprVn mulrC ltr_pdivlMr //.
  by rewrite exprn_gt0 //.
have [V [hV [hp hinc]]] := @compact_convex_projected_contraction_neighbourhood R n m K p c g r s
  hK hc hgp hr hs hs1 hbuffer.
exists V; split=> //; split=> // q hq.
have hmono := measure_mono hm (hinc q hq).
have he := @projected_volume_function_dilation R n m K p c s.
rewrite (ger0_norm (ltW hs)) in he.
have hle : (s^+m)%R%:E*projected_volume_function K p<=projected_volume_function K q.
  by rewrite -he.
exact: lt_le_trans hsp hle.
Qed.

(** Source for [compact_convex_projected_volume_open_superlevel]:
    supporting open strict superlevels of actual
    compact convex projected volume for Federer
    2.10.5(2), p. 173. This is precisely the
    lower-continuity consequence needed to identify
    essential supremum with supremum using the
    full support of theta-star. *)
Lemma compact_convex_projected_volume_open_superlevel (R : realType) (n m : nat)
    (K : set (inner_metric_space (@euclidean_inner_productP R n))) (b : R) :
  compact K -> @is_inner_convex R (R_n R n) K ->
  open [set p : euclidean_projection_space R n m | b%:E<projected_volume_function K p].
Proof.
move=> hK hc; rewrite openE=> p hp.
have [V [hV [hVp hbound]]] := @compact_convex_projected_volume_lower_neighbourhood R n m K p b hK hc hp.
have hn : nbhs p V by rewrite openE in hV; exact: hV p hVp.
apply: (@filterS _ (nbhs p) _ V _ _ hn)=> q hq; exact: hbound q hq.
Qed.
