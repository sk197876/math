(** Federer (1969), 3.4.3, p. 317: nullity of
    the original rank-threshold image near a full-threshold point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormClassOneUP NormRegularity NormRegularityOperations NormClassZeroTopology NormBoundedLinearTopology
  NormDiffeomorphismUP LinearRankUP CriticalTargetCoordinatesUP CriticalTargetCoordinates
  CriticalLocalSourceChart CriticalChartRankReduction RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_local_rank_nullity]: the neighbourhood
    U sought in the opening proof paragraph of 3.4.3,
    p. 317. Construct the bounded target coordinates and actual
    orthogonal joint chart, then apply the proved rank reduction.
    The rank equality occurs only at the centre; all other
    original source points require the printed upper rank bound. *)
Theorem critical_local_rank_nullity (R:realType) nu l k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A B:set (R_n R (nu+l))) (f:R_n R (nu+l)->Y) a
    (D:Hom (R_n R (nu+l)) Y) (hp:0<=nu%:R+l%:R/k%:R):
  (1<=k)%N ->(0<l)%N ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))) hNY A f k ->
  A a ->has_norm_differential (inner_norm (@euclidean_inner_productP R (nu+l))) NY A f a D ->
  has_linear_rank D nu ->B `<=` A ->
  (forall x,B x ->exists M:Hom (R_n R (nu+l)) Y,
    has_norm_differential (inner_norm (@euclidean_inner_productP R (nu+l))) NY A f x M /\
    exists r,has_linear_rank M r /\(r<=nu)%N) ->
  exists U:set (R_n R (nu+l)),
    @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (nu+l)))) U /\
    U a /\@real_hausdorff_measure R (real_norm_metric_space hNY)
      (nu%:R+l%:R/k%:R) hp (f @` (B `&` U))=0%E.
Proof.
move=>hk hl hf ha hD hRank hBA hRankB.
pose X:=R_n R (nu+l).
pose NX:=inner_norm (@euclidean_inner_productP R (nu+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (nu+l)).
have [L [J hCoordinates]]:=critical_target_coordinates_exists hNY hRank.
have [U [S [g [G [haU [hUA [hConvex [hChart hPrefix]]]]]]]]:=
  @critical_local_source_chart R nu l k Y NY hNY A f a D L J hk hf ha hD hCoordinates.
have hUInterior x (hx:U x):norm_domain_interior NX U x:=
  (norm_class_continuous (norm_diffeomorphism_forward_class hChart) hx).1.
have hUOpen:@open (real_norm_metric_space hNX) U.
  rewrite openE=>x hx.
  exact:(proj1 (@norm_domain_interior_neighbourhood R X NX hNX U x) (hUInterior x hx)).
have hfU:=@norm_class_open_restriction R X Y NX NY hNX hNY A U f k hUA hUInterior hf.
have hLocalRank x (hx:(B `&` U) x):exists M:Hom X Y,
    has_norm_differential NX NY U f x M /\exists r,has_linear_rank M r /\(r<=nu)%N.
  have [M [hM hR]]:=hRankB x hx.1.
  exists M;split;last exact:hR.
  exact:(@norm_differential_restrict R X Y NX NY A U f x M hUA (hUInterior x hx.2) hM).
have hNull:=@critical_chart_rank_reduction R nu l k Y NY hNY U S (B `&` U) f g G L hp
  hk hl hConvex hChart hfU (fun x hx=>hx.2) (critical_target_coordinates_bounded hCoordinates)
  (fun x _=>hPrefix x) hLocalRank.
exists U;by split;last split.
Qed.
