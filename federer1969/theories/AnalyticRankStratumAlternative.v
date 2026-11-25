(** Federer (1969), 3.2.33, p. 270: the exact
    rank-mu stratum is either null or relatively open and
    conull on connected analytic W. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormAnalyticRelativeUP AnalyticSubmanifoldUP RelativeLowImageLocus RelativeRankLocus
  AnalyticRelativeRankAlternative AnalyticRankStratumOpen EuclideanSubmanifoldUP
  HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [analytic_relative_rank_stratum_alternative]: the
    full printed alternative for S={dim im Df=mu},
    Federer 3.2.33, p. 270, with the corrected
    reference 3.1.24 (erratum p. 5, book p. 270
    line 25). Actual analytic threshold equations give
    the two adjacent rank bounds all-or-null. Derivative
    continuity gives relative openness at the upper bound.
    Degree zero uses its literal least-dimension convention.
    No source measurability or finite-mass premise is needed. *)
Theorem analytic_relative_rank_stratum_alternative (R:realType) n m v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  @is_euclidean_analytic_submanifold R n m W ->
  @norm_analytic_relative R (R_n R n) (R_n R v)
    (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R v))
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R v)) setT W F ->
  @connected (inner_metric_space (@euclidean_inner_productP R n)) W ->
  let H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  H (relative_rank_locus mu W F)=0%E \/
    (@relatively_open_set (inner_metric_space (@euclidean_inner_productP R n)) W
      (relative_rank_locus mu W F) /\H (W `\` relative_rank_locus mu W F)=0%E).
Proof.
move=>hW hF hConnected H.
pose hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
case:(@analytic_relative_rank_bound_alternative R n m v mu W F hW hF hConnected)=>[hAll|hNull]; last first.
- left; apply:(measure_null_subset hH _ hNull); by move=>x hx; exact hx.1.
case:mu hAll=>[|mu] hAll.
- right; split; first exact:(analytic_relative_maximal_rank_open hW hF hAll).
  have hS:relative_rank_locus 0 W F = W.
    apply/seteqP; split=>x hx; first exact hx.1.1.
    split; first by rewrite hAll.
    by move=>r hr; rewrite ltn0 in hr.
  rewrite hS setDv; exact:measure_empty hH.
- case:(@analytic_relative_rank_bound_alternative R n m v mu W F hW hF hConnected)=>[hLowerAll|hLowerNull].
  + left.
    have hS:relative_rank_locus mu.+1 W F=set0.
      apply/seteqP; split=>[x hx|x []].
      apply:(hx.2 mu (leqnn mu)); by rewrite hLowerAll; exact hx.1.1.
    rewrite hS; exact:measure_empty hH.
  + right; split; first exact:(analytic_relative_maximal_rank_open hW hF hAll).
    apply:(measure_null_subset hH _ hLowerNull)=>x [hx hn].
    case:(pselect (relative_low_image_locus mu W F x))=>[hLow|hNoLow]; first exact hLow.
    exfalso; apply:hn; split; first by rewrite hAll.
    move=>r hr hLow; apply:hNoLow.
    exact:(@relative_low_image_locus_monotone R n v r mu W F hr x hLow).
Qed.
