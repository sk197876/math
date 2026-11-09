(** Federer (1969), 3.4.3, pp. 316–317: fixed
    rank strata in the original arbitrary source dimension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormMetric NormDifferentialUP NormRegularity LinearRankUP
  CriticalRankStratumNullity RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_fixed_rank_nullity]: the
    fixed-rank part of 3.4.3, pp. 316–317, in
    the original R^m coordinates. The equality m=r+(m-r)
    only identifies the finite coordinate count; every source point
    and function value is retained. *)
Theorem critical_original_fixed_rank_nullity (R:realType) m r k:
  (r<m)%N ->(1<=k)%N ->
  forall (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A B:set (R_n R m)) (f:R_n R m->Y)
    (hp:0<=r%:R+(m-r)%:R/k%:R),
    norm_class (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY A f k ->
    B `<=` A ->
    (forall x,B x ->exists D:Hom (R_n R m) Y,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f x D /\
      has_linear_rank D r) ->
    @real_hausdorff_measure R (real_norm_metric_space hNY)
      (r%:R+(m-r)%:R/k%:R) hp (f @` B)=0%E.
Proof.
move=>hr hk.
have hSplit:m=(r+(m-r))%N by rewrite subnKC //;exact:ltnW hr.
rewrite hSplit addKn.
move=>Y NY hNY A B f hp hf hBA hRank.
have hl:(0<m-r)%N by rewrite subn_gt0.
exact:(@critical_fixed_rank_image_nullity R r (m-r) k Y NY hNY A B f hp hk hl hf hBA hRank).
Qed.
