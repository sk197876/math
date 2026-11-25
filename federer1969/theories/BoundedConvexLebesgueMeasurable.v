(** The arbitrary bounded convex sources used in Federer
    (1969), 3.2.45, p. 279, are Lebesgue measurable.
    Use the original convex closure and homothety results. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricBoundedClosureLaws EuclideanConvexInteriorAlternative ConvexInteriorContraction InnerConvexNeighbourhoods
  AffineDilation ProjectedVolumeDilation RealDilationSlack EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic MeasureFiniteClosure MeasureNullRemainder TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [bounded_convex_lebesgue_measurable]: supporting
    unrestricted convex-source Fubini in Federer 3.2.45,
    p. 279, using 3.2.35, pp. 271–272.
    The proved interior-or-null-closure split handles thin
    sources. In the interior case, actual compact
    contractions of the closure lie in the original
    source. Their exact homothety volumes and arbitrarily
    small dilation slack force the omitted boundary
    remainder to be null. Completeness then gives
    measurability, without assuming the original source
    Borel or Suslin. Ambient zero is retained. *)
Theorem bounded_convex_lebesgue_measurable (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  is_inner_convex S -> metric_set_bounded S ->
  measure_measurable (@euclidean_lebesgue_measure R n) S.
Proof.
move=> hConvex hBound.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R n.
pose hm := euclidean_lebesgue_is_measure R n.
case: (pselect (S !=set0))=> [hNonempty|hEmpty].
- have hClosureCompact := euclidean_bounded_closure_compact hBound.
  have hClosureMeasurable : measure_measurable mu (closure S).
    apply: euclidean_borel_measurable; exact: closed_borel_set (@closed_closure X S).
  case: (euclidean_convex_interior_or_null_closure hNonempty hConvex)=> [[a ha]|hClosureNull].
  + pose M := fine (mu (closure S)).
    have hMNum : mu (closure S) \is a fin_num.
      rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact: euclidean_compact_finite hClosureCompact.
    have hMValue : mu (closure S)=M%:E by rewrite /M fineK.
    pose D := closure S `\` S.
    have hDBound : (mu D<=M%:E)%E.
      rewrite -hMValue; apply: (@measure_mono R X mu hm D (closure S))=> x hx; exact hx.1.
    have hDNum : mu D \is a fin_num.
      rewrite (ge0_fin_numE (measure_nonnegative hm _)); exact: le_lt_trans hDBound (ltry M).
    pose d := fine (mu D).
    have hDValue : mu D=d%:E by rewrite /d fineK.
    have hd0 : 0<=d.
      have h : (0<=mu D)%E := @measure_nonnegative R X mu hm D.
      by rewrite hDValue lee_fin in h.
    have hDZero : d=0.
      apply/eqP; rewrite eq_le hd0 andbT leNgt; apply/negP=> hd.
      have hGap : M-d<M by lra.
      have [t [ht hSlack]] := @real_positive_dilation_cost_slack R n (M-d) M hGap.
      have ht0 : 0<t := lt_trans ltr01 ht.
      have hs0 : 0<t^-1 by rewrite invr_gt0.
      have hs1 : t^-1<1 by rewrite invf_lt1.
      pose T := (@affine_dilation R (R_n R n) a t^-1) @` closure S.
      have hTSubset : T `<=` S.
        move=> x [z hz <-].
        exact: convex_interior_contraction_closure hConvex ha hz hs0 hs1.
      have hTCompact : @compact X T.
        have hAffine : continuous (@affine_dilation R (R_n R n) a t^-1 : X -> X).
          have hFunction : (@affine_dilation R (R_n R n) a t^-1 : X -> X)=
              (fun x : X => t^-1*:x+(1-t^-1)*:a).
            by apply: funext=> x; rewrite /affine_dilation addrC.
          rewrite hFunction; exact: inner_affine_variable_continuous.
        exact: continuous_compact (continuous_subspaceT hAffine) hClosureCompact.
      have hTMeasurable : measure_measurable mu T.
        apply: euclidean_borel_measurable; apply: closed_borel_set.
        exact: compact_closed (@metric_hausdorff R X) hTCompact.
      have hIntersection : closure S `&` T=T.
        apply/seteqP; split; first by move=> x [_ hx].
        move=> x hx; split=> //; exact: subset_closure (hTSubset x hx).
      have hComplement : D `<=` closure S `\` T.
        move=> x [hx hOutside]; split=> //; move=> hT; exact: hOutside (hTSubset x hT).
      have hSplit := hTMeasurable (closure S); rewrite hIntersection in hSplit.
      have hRemainder : (mu D<=mu (closure S `\` T))%E :=
        @measure_mono R X mu hm D (closure S `\` T) hComplement.
      have hBudget : (mu T+mu D<=M%:E)%E.
        have h := leeD (lexx (mu T)) hRemainder.
        by rewrite -hSplit hMValue in h.
      have hTVolume : mu T=((t^-1)^+n*M)%:E.
        have hValue := @euclidean_affine_dilation_volume R n (closure S) a t^-1.
        change (mu T=((((`|t^-1|)^+n)%:E)*mu (closure S))%E) in hValue.
        by rewrite (ger0_norm (ltW hs0)) hMValue -EFinM in hValue.
      rewrite hTVolume hDValue -EFinD lee_fin in hBudget.
      have hPower : t^+n*(t^-1)^+n= 1 by rewrite -exprMn mulfV ?gt_eqF // expr1n.
      have htPower : 0<t^+n by rewrite exprn_gt0.
      have hScaled := ler_wpM2l (ltW htPower) hBudget.
      have hAlgebra : t^+n*((t^-1)^+n*M+d)=M+t^+n*d.
        by rewrite mulrDr mulrA hPower mul1r.
      rewrite hAlgebra in hScaled.
      have hOpposite : M<=(M-d)*t^+n by nra.
      have hImpossible := lt_le_trans hSlack hOpposite.
      by rewrite ltxx in hImpossible.
    have hNull : mu (closure S `\` S)=0%E by rewrite -/D hDValue hDZero.
    exact: (measurable_subset_null_remainder hm (@subset_closure X S) hClosureMeasurable hNull).1.
  + have hNull : mu S=0%E := @measure_null_subset R X mu hm S (closure S)
      (@subset_closure X S) hClosureNull.
    exact: (@measure_null_measurable R X mu hm S hNull).
- have hS : S=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hEmpty; by exists x.
  rewrite hS; exact: (@measure_measurable_empty R X mu hm).
Qed.
