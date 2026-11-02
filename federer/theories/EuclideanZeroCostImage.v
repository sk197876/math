(** Federer (1969), 3.2.30, p. 268: supporting the zero
    exterior-norm case of the image-measure inequality. Countably
    many small source pieces give a zero-cost target cover at
    every positive cutoff, even for unbounded source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric InnerMetricSeparability
  LipschitzUP HausdorffLengthUP MetricClosedSmallCover MetricDiameterUP MetricDiameter
  CaratheodoryLimitUP CaratheodoryLimitMeasure CaratheodoryBorelRegular MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws MetricScaleWeightedBound MetricScaleCutoffCost
  MeasureUP MeasureBasic MeasureAlmostBasic MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_zero_cost_lipschitz_image]: supporting
    zero-coefficient branch of Federer 3.2.30, p. 268, by
    the covering laws of 2.10.1, p. 170. If every nonempty
    image generator has zero actual cost, any globally Lipschitz
    Euclidean image has zero final measure. No finite source
    measure or boundedness is assumed. *)
Theorem euclidean_zero_cost_lipschitz_image (R:realType) s (Y:metricType R)
    (F:inner_metric_space (@euclidean_inner_productP R s)->Y) M
    (cost:set Y->\bar R) (mu:set Y->\bar R):
  is_metric_lipschitz_bound setT F M ->
  is_caratheodory_limit
    (fun j:@nonempty_metric_sets R Y=>val j) (fun j=>cost (val j)) mu ->
  (forall A:set Y,A!=set0 ->0<=cost A) ->
  (forall A:set (inner_metric_space (@euclidean_inner_productP R s)),
    A!=set0 ->cost (F @` A)=0) ->
  forall A,mu (F @` A)=0.
Proof.
move=>hLip hMu hCost hZero A.
pose X:=inner_metric_space (@euclidean_inner_productP R s).
have hNonnegative j:(0<=cost (val j)):=hCost _ (set_valP j).
have hMeasure:=caratheodory_limit_is_measure hMu hNonnegative.
apply/eqP; rewrite eq_le (measure_nonnegative hMeasure) andbT.
apply:(caratheodory_limit_least hMu)=>delta nu hDelta hNu.
have hNuM:=metric_scale_envelope_is_measure hNu hNonnegative.
have [j hj]:=reciprocal_metric_cutoffs_cofinal hDelta.
pose r:=(((j.+1)%:R:R)^-1)%R.
have hr:(0<r)%R by rewrite /r invr_gt0 ltr0n.
pose e:=(r/(M+1))%R.
have hGe:(1<=M+1)%R by rewrite lerDr; exact hLip.1.
have hMp:(0<M+1)%R:=lt_le_trans ltr01 hGe.
have he:(0<e)%R by rewrite /e divr_gt0.
have [D [hD hDense]]:=@finite_inner_metric_separable R (R_n R s) (@euclidean_inner_product R s)
  (@euclidean_inner_productP R s) [the finType of 'I_s] (@coordinate_basis R s) (@coordinate_basisP R s).
have [C [hC hCover]]:=separable_closed_small_cover_allow_empty hD hDense (@closedT X) he.
pose I:=[set i:nat|C i!=set0].
have hICount:countable I:=countableP I.
have hPiece i (hi:I i):nu (F @` C i)=0.
  have hImage:F @` C i!=set0 by have [x hx]:=hi; exists (F x); by exists x.
  pose q:@nonempty_metric_sets R Y:=@exist _ (fun B=>B \in [set B|B!=set0]) (F @` C i) (mem_set hImage).
  have hSize:extended_metric_diameter (val q)<=delta.
    apply:(metric_diameter_least (extended_metric_diameter_specification (val q)) (ltW hDelta)).
    move=>y z [x hx <-] [t ht <-].
    have hBound:=hLip.2 x t Logic.I Logic.I.
    have hSmall:((M*e)%R<r)%R.
      have hRatio:(M/(M+1)<1)%R.
        by rewrite (@ltr_pdivrMr R (M+1) 1 M hMp) mul1r ltrDl.
      have hEq:(M*e=r*(M/(M+1)))%R by rewrite /e mulrCA.
      by rewrite hEq -[ltRHS]mulr1 (ltr_pM2l hr).
    have hDist:(mdist (F x) (F t)<=M*e)%R.
      apply:le_trans hBound _; exact (ler_wpM2l hLip.1 ((hC i).2.2 x t hx ht)).
    exact (le_trans (lee_tofin (ltW (le_lt_trans hDist hSmall))) hj).
  have hh:=@metric_scale_generator_bound R Y (@nonempty_metric_sets R Y)
    (fun j=>val j) (fun j=>cost (val j)) delta nu q hNu (hCost _ hImage) hSize.
  rewrite (hZero (C i) hi) in hh.
  by apply/eqP; rewrite eq_le hh (measure_nonnegative hNuM).
have hSub:F @` A `<=` \bigcup_(i in I) (F @` C i).
  move=>y [x hx <-].
  have hCx:(\bigcup_i C i) x by rewrite -hCover.
  have [i _ hi]:=hCx; exists i; first by exists x.
  by exists x.
have hBound:=@measure_indexed_cover R Y [the choiceType of (nat:Type)] nu hNuM (F @` A) I
  (fun i=>F @` C i) hICount hSub.
by rewrite (nonnegative_sum_zero hPiece) in hBound.
Qed.
