(** Federer (1969), 3.4.3, pp. 316–317: assemble
    local nullity on each original fixed-rank stratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormMetric NormDifferentialUP NormRegularity LinearRankUP
  EuclideanNormCountableBase CountableLocallyNullImage CriticalLocalRankNullity
  RealHausdorffMeasure RealHausdorffMeasureLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_fixed_rank_image_nullity]: the
    local-to-global step implicit in 3.4.3, p. 317,
    on the points of rank exactly nu. A countable open
    subcover suffices for the original arbitrary source. Constant
    rank is required only on this stratum, not on an
    ambient neighbourhood. *)
Theorem critical_fixed_rank_image_nullity (R:realType) nu l k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A B:set (R_n R (nu+l))) (f:R_n R (nu+l)->Y)
    (hp:0<=nu%:R+l%:R/k%:R):
  (1<=k)%N ->(0<l)%N ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))) hNY A f k ->
  B `<=` A ->
  (forall x,B x ->exists D:Hom (R_n R (nu+l)) Y,
    has_norm_differential (inner_norm (@euclidean_inner_productP R (nu+l))) NY A f x D /\
    has_linear_rank D nu) ->
  @real_hausdorff_measure R (real_norm_metric_space hNY)
    (nu%:R+l%:R/k%:R) hp (f @` B)=0%E.
Proof.
move=>hk hl hf hBA hRankB.
have [Base hBase]:=@euclidean_norm_countable_open_base R (nu+l).
apply:(@countable_locally_null_image R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R (nu+l))))
  (real_norm_metric_space hNY) (@real_hausdorff_measure R (real_norm_metric_space hNY)
    (nu%:R+l%:R/k%:R) hp) f B Base
  (@real_hausdorff_measure_is_measure R (real_norm_metric_space hNY)
    (nu%:R+l%:R/k%:R) hp) hBase).
move=>a ha;have [D [hD hRank]]:=hRankB a ha.
apply:(@critical_local_rank_nullity R nu l k Y NY hNY A B f a D hp hk hl hf (hBA a ha)
  hD hRank hBA).
move=>x hx;have [M [hM hMR]]:=hRankB x hx.
exists M;split;first exact:hM.
exists nu;by split.
Qed.
