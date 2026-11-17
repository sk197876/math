(** Federer (1969), 3.4.8(13), p. 336:
    choose a closed bounded representative with null
    exceptional part. The original finite analytic variety
    is relatively closed. Intersect its closed extension
    with one sufficiently small actual closed ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness InnerNormTopologyAdapters
  FiniteNormCompactness NormDifferentialUP NormBoundedLinearTopology NormOpenDomainLaws
  SetGermUP SetGermExistence SetGermOrder FiniteAnalyticVarietyUP AnalyticVarietyGermUP
  FiniteAnalyticVarietyRelativeClosed HausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_compact_representative_null_remainder]:
    the closed representative S_lambda used in the proof
    of 3.4.8(13), p. 336. Only local
    containment in a manifold and a proved null set
    is needed. The original germ is preserved exactly. *)
Theorem analytic_compact_representative_null_remainder (R:realType) n m
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0)
    (Z N:set (R_n R n)):
  @is_analytic_variety_germ R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) 0 alpha ->
  @set_germ_subset (Topological.clone (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 alpha
    (@set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 (N `|` Z)) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m N=0%E ->
  exists S:set (R_n R n),
    @compact (inner_metric_space (@euclidean_inner_productP R n)) S /\
    @set_germ (Topological.clone (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R n))) _) 0 S=alpha /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (S `\` Z)=0%E.
Proof.
move=>[U [H [hU0 [hH hAlpha]]]] hContain hNull.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose E:=Topological.clone (real_norm_metric_space hNX) _.
pose M:=inner_metric_space (@euclidean_inner_productP R n).
have [C [hC hHC]]:=finite_analytic_variety_relative_closed_form hH.
have hLocal:@set_germ_subset E 0 (@set_germ E 0 H) (@set_germ E 0 (N `|` Z)).
  by rewrite hAlpha.
have [W [hW [hW0 hCover]]]:=(@set_germ_subset_original E 0 H (N `|` Z)).1 hLocal.
have hUW:@open E (U `&` W):=openI hH.1 hW.
have hUW0:(U `&` W) 0 by split.
have [r [hr hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX (U `&` W) 0).2
  (open_nbhs_nbhs (conj hUW hUW0)).
pose rho:=r/2.
have hRho:0<rho by rewrite /rho;by lra.
have hSmall:rho<r by rewrite /rho;by lra.
pose B:set X:=[set x|NX x<=rho].
have hBUW:B `<=` U `&` W.
  move=>x hx;have h:=hBall x (le_lt_trans hx hSmall);by rewrite add0r in h.
pose S:set X:=B `&` C.
have hBCompact:@compact M B:=@finite_norm_ball_compact R X
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) NX hNX
  n (@coordinate_basis R n) (@coordinate_basisP R n) rho.
have hCMetric:@closed M C:=(inner_norm_closedP (@euclidean_inner_productP R n) C).2 hC.
have hCompact:@compact M S:=compact_closedI hBCompact hCMetric.
pose O:set X:=[set x|NX x<rho].
have hO:@open E O.
  rewrite openE=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX O x).1.
  have h:=@norm_open_ball_domain_interior R X NX hNX 0 rho x.
  have hxBall:is_true (NX (x-0)<rho) by rewrite subr0.
  have hEqual:(fun y=>is_true (NX (y-0)<rho))=O by apply:funext=>y;rewrite subr0.
  by rewrite -hEqual;exact:h hxBall.
have hO0:O 0 by change (is_true (NX 0<rho));rewrite /NX inner_norm0.
have hSGerm:@set_germ E 0 S=alpha.
  rewrite -hAlpha;apply/set_germ_equality_original.
  exists O;split;first exact:hO.
  split;first exact:hO0.
  apply/seteqP;split.
  - move=>x [[hxB hxC] hxO];split;last exact:hxO.
    rewrite hHC;split;first exact:(hBUW x hxB).1;exact:hxC.
  - move=>x [hxH hxO];split;last exact:hxO.
    split;first exact:ltW hxO.
    rewrite hHC in hxH;exact:hxH.2.
exists S;split;first exact:hCompact.
split;first exact:hSGerm.
apply:(measure_null_subset (@hausdorff_measure_is_measure R M m) _ hNull)=>x [[hxB hxC] hxNotZ].
have hxUW:=hBUW x hxB.
have hxH:H x by rewrite hHC;split;[exact:hxUW.1|exact:hxC].
case:(hCover x hxH hxUW.2)=>[hxN|hxZ];first exact:hxN.
exact:False_ind _ (hxNotZ hxZ).
Qed.
