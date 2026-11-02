(** Federer (1969), 3.2.38, p. 274: small Euclidean tubes of a
    compact source have arbitrarily small mass outside that source. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanCompactOpenVolume MetricOpenThickening MetricCompactNeighbourhood
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureSplit TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_euclidean_tube_excess_small]: supporting
    the first error term in the choice of delta in Federer 3.2.38,
    p. 274. Actual compact-source open approximation and a uniform
    metric neighbourhood prove the estimate, including empty sources
    and ambient dimension zero. No regularity of the image is assumed. *)
Theorem compact_euclidean_tube_excess_small (R:realType) n
    (C:set (inner_metric_space (@euclidean_inner_productP R n))) (e:R):
  compact C ->0<e ->exists d:R,0<d /\
    (@euclidean_lebesgue_measure R n (metric_open_thickening C d `\` C)<e%:E)%E.
Proof.
move=>hC he.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose hm:=euclidean_lebesgue_is_measure R n.
have hCfinite:mu C \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm C)); exact:euclidean_compact_finite hC.
have hCm:measure_measurable mu C.
  apply:euclidean_borel_measurable; exact:closed_borel_set (compact_closed (@metric_hausdorff R X) hC).
have hBudget:(mu C<(fine (mu C)+e)%:E)%E by rewrite -(fineK hCfinite) lte_fin ltrDl.
have [U [hU [hCU hVolume]]]:=euclidean_compact_open_volume_bound hC hBudget.
have [d [hd hTube]]:=compact_metric_open_thickening hC hU hCU.
have hUfinite:mu U \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm U)); exact:lt_trans hVolume (ltry _).
have hDsub:(U `\` C) `<=` U by move=>x [hx _].
have hDfinite:mu (U `\` C) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (U `\` C))).
  exact:le_lt_trans (measure_mono hm hDsub) (lt_trans hVolume (ltry _)).
have hIntersection:U `&` C=C.
  apply/seteqP; split=>[x [_ hx]//|x hx]; split=>//; exact:hCU x hx.
have hSplit:=hCm U; rewrite hIntersection in hSplit.
have hSplitR:fine (mu U)=fine (mu C)+fine (mu (U `\` C)).
  move:hSplit; rewrite -(fineK hUfinite) -(fineK hCfinite) -(fineK hDfinite) -EFinD.
  by move/eqP; rewrite eqe=>/eqP.
have hVolumeR:fine (mu U)<fine (mu C)+e.
  change (is_true (mu U<(fine (mu C)+e)%:E)%E) in hVolume.
  by rewrite -(fineK hUfinite) lte_fin in hVolume.
have hError:(mu (U `\` C)<e%:E)%E.
  rewrite -(fineK hDfinite) lte_fin; lra.
exists d; split=>//.
apply:le_lt_trans _ hError; apply:(@measure_mono R X mu hm).
by move=>x [hx hn]; split=>//; exact:hTube x hx.
Qed.
