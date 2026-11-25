(** Federer (1969), 3.2.47, p. 283: the
    use of 3.2.29 can retain the containing sphere.
    This supporting compact-manifold version assembles the actual
    local coordinate covers over finitely many compact cores.
    Original nonmeasurable finite rectifiable subsets are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp finmap classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  FiniteInnerSubmanifoldUP FiniteInnerCompactCoordinateCores RectifiableCoordinatePatchManifoldCover
  RectifiableManifoldCoverUP RectifiableSetUP MeasureRectifiableSubset
  MetricClosedBalls HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_submanifold_rectifiable_contained_cover]:
    the reduction by 3.2.29 within the original sphere
    in 3.2.47, p. 283, generalized to any
    compact containing class-one manifold. All covering members
    are actual ambient r-submanifolds contained in S;
    only a null remainder of the original E is omitted. *)
Theorem compact_submanifold_rectifiable_contained_cover (R:realType) N d r
    (S E:set (R_n R N)):
  is_inner_submanifold (@euclidean_inner_product R N) d 1%N S ->
  @compact (inner_metric_space (@euclidean_inner_productP R N)) S ->E `<=` S ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R N)) r) r E ->
  exists C:set (set (R_n R N)),is_countable_submanifold_measure_cover r 1%N E C /\
    (forall M,C M ->M `<=` S).
Proof.
move=>hS hCompact hES hRect.
pose X:=inner_metric_space (@euclidean_inner_productP R N).
pose Z:=R_n R d.
pose J:=((set (R_n R N))*(set Z*((R_n R N->Z)*(Z->R_n R N))))%type.
have [F [hF hCover]]:=@finite_inner_compact_coordinate_cores R (R_n R N) _
  (@euclidean_inner_productP R N) d S hS hCompact.
pose K:=fun p:(J*(R_n R N*R))%type=>S `&` @metric_closed_ball R X p.2.1 p.2.2.
pose Ep:=fun p:F=>E `&` K (val p).
have hLocal (p:F):exists C:set (set (R_n R N)),
    is_countable_submanifold_measure_cover r 1%N (Ep p) C /\(forall M,C M ->M `<=` S).
  have [hChart [hK hKT]]:=hF (val p) (valP p).
  have hKST:K (val p) `<=` S `&` (val p).1.1.
    move=>a ha; exact (conj ha.1 (hKT a ha)).
  have hERect:=@measure_rectifiable_subset R X (@hausdorff_measure R X r) r E (Ep p)
    (fun a ha=>ha.1) hRect.
  exact (@rectifiable_coordinate_patch_manifold_cover R N d r S (val p).1.1 (K (val p))
    (Ep p) (val p).1.2.1 (val p).1.2.2.1 (val p).1.2.2.2 hChart hK hKST
    (fun a ha=>ha.2) hERect).
have [C hC]:=choice hLocal.
pose D:=\bigcup_(p in (@setT (F:Type))) C p.
have hDCount:countable D.
  exact (bigcup_countable (countableP setT)
    (fun p _=>submanifold_measure_cover_countable (hC p).1)).
have hDMan M (hM:D M):@EuclideanSubmanifoldUP.is_euclidean_submanifold R N r 1%N M.
  have [p _ hp]:=hM; exact (submanifold_measure_cover_class (hC p).1 hp).
have hDS M (hM:D M):M `<=` S.
  have [p _ hp]:=hM; exact ((hC p).2 M hp).
have hNull:@hausdorff_measure R X r
    (\bigcup_(p in (@setT (F:Type))) (Ep p `\` \bigcup_(M in C p) M))=0%E.
  exact (@measure_null_countable_union R X [the choiceType of (F:Type)]
    (@hausdorff_measure R X r) (@hausdorff_measure_is_measure R X r) setT
    (fun p=>Ep p `\` \bigcup_(M in C p) M) (countableP setT)
    (fun p _=>submanifold_measure_cover_almost (hC p).1)).
have hRem:E `\` \bigcup_(M in D) M `<=`
    \bigcup_(p in (@setT (F:Type))) (Ep p `\` \bigcup_(M in C p) M).
  move=>x [hx hn].
  have [q hq hxK]:=hCover x (hES x hx).
  pose p:F:=[` hq]%fset.
  exists p; first exact I.
  split; first exact (conj hx hxK).
  move=>[M hM hxM]; apply:hn; exists M; last exact hxM.
  by exists p.
exists D; split; last exact hDS.
constructor.
- exact hDCount.
- exact hDMan.
- exact (@measure_null_subset R X (@hausdorff_measure R X r) (@hausdorff_measure_is_measure R X r)
    (E `\` \bigcup_(M in D) M) _ hRem hNull).
Qed.
