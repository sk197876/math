(** Federer (1969), 3.2.41, printed p. 278: approximate
    the two original measurable sets from inside by compact
    sets. A common scalar contraction approaches their actual
    positive finite volume roots, and compact Brunn--Minkowski
    supplies the bound on the original sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  VectorSetSum VectorSetSumLaws EuclideanVolumeRootSum
  EuclideanCompactRootApproximation ExtendedPositivePower RealPower
  ExtendedContractionSqueeze MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_positive_brunn_minkowski_compact_reduction]:
    supporting positive finite measurable case of Federer
    3.2.41, p. 278. Compact subsets are proved to exist for
    each contraction; their choices remain local. Original
    non-Borel measurable sources are permitted, and the actual
    sum's volume need not be finite or its set measurable.
    This passage assumes the separately proved compact-case
    theorem and discharges no mathematical premise by an axiom. *)
Theorem finite_positive_brunn_minkowski_compact_reduction (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))) (a b:R):
  (0<n)%N ->
  (forall K L:set (inner_metric_space (@euclidean_inner_productP R n)),
    compact K ->compact L ->K !=set0 ->L !=set0 ->
    euclidean_volume_root_sum_bound K L) ->
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  measure_measurable (@euclidean_lebesgue_measure R n) B ->
  @euclidean_lebesgue_measure R n A=a%:E ->
  @euclidean_lebesgue_measure R n B=b%:E ->
  0<a ->0<b ->euclidean_volume_root_sum_bound A B.
Proof.
move=> hn hCompactCase hA hB hMA hMB ha hb.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
change (mu A=a%:E) in hMA.
change (mu B=b%:E) in hMB.
pose p:R:=n%:R.
pose alpha:=real_power a p^-1.
pose beta:=real_power b p^-1.
have hp:0<p by rewrite /p ltr0n.
have hi:0<p^-1 by rewrite invr_gt0.
have hAlpha:0<alpha:=real_power_strictly_positive _ ha.
have hBeta:0<beta:=real_power_strictly_positive _ hb.
have hm:=euclidean_lebesgue_is_measure R n.
change (is_true (extended_positive_power (mu A) p^-1+
  extended_positive_power (mu B) p^-1<=
  extended_positive_power (mu (vector_set_sum A B)) p^-1)%E).
rewrite hMA hMB /extended_positive_power -EFinD.
change (is_true ((alpha+beta)%:E<=
  extended_positive_power (mu (vector_set_sum A B)) p^-1)%E).
apply:(@extended_contraction_squeeze R (alpha+beta)%:E
  (extended_positive_power (mu (vector_set_sum A B)) p^-1)
  (extended_positive_power_nonnegative _ _))=> t /andP[ht0 ht1].
have hTA:0<=t*alpha:=ltW (mulr_gt0 ht0 hAlpha).
have hTB:0<=t*beta:=ltW (mulr_gt0 ht0 hBeta).
have hAF:(mu A < +oo)%E by rewrite hMA ltry.
have hBF:(mu B < +oo)%E by rewrite hMB ltry.
have hARoot:((t*alpha)%:E<extended_positive_power (mu A) p^-1)%E.
  rewrite hMA /extended_positive_power lte_fin.
  change (is_true (t*alpha<alpha)).
  by rewrite -[X in _<X]mul1r ltr_pM2r.
have hBRoot:((t*beta)%:E<extended_positive_power (mu B) p^-1)%E.
  rewrite hMB /extended_positive_power lte_fin.
  change (is_true (t*beta<beta)).
  by rewrite -[X in _<X]mul1r ltr_pM2r.
have [K [hK [hKA [hKNe hTK]]]]:=@euclidean_compact_inner_root_strict R n A p (t*alpha)
  hA hAF hp hTA hARoot.
have [L [hL [hLB [hLNe hTL]]]]:=@euclidean_compact_inner_root_strict R n B p (t*beta)
  hB hBF hp hTB hBRoot.
have hCompact:=hCompactCase K L hK hL hKNe hLNe.
change (is_true (extended_positive_power (mu K) p^-1+
  extended_positive_power (mu L) p^-1<=
  extended_positive_power (mu (vector_set_sum K L)) p^-1)%E) in hCompact.
have hSumSub:=@vector_set_sum_monotone E K L A B hKA hLB.
have hVolume:=@measure_mono R E mu hm _ _ hSumSub.
have hRootMono:=@extended_positive_power_monotone R _ _ p^-1
  (measure_nonnegative hm _) hVolume hi.
have hSmall:(((t*alpha)%:E+(t*beta)%:E)<=
  extended_positive_power (mu K) p^-1+extended_positive_power (mu L) p^-1)%E.
  exact:leeD (ltW hTK) (ltW hTL).
rewrite -EFinM mulrDr EFinD.
exact:(le_trans hSmall (le_trans hCompact hRootMono)).
Qed.
