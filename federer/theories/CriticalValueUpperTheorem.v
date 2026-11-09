(** Federer (1969), 3.4.3, pp. 316–317: the
    critical-value upper theorem for the original arbitrary source. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormMetric NormDifferentialUP NormDifferentialDirectional NormClassOneUP
  NormRegularity NormRegularityOperations LinearRankUP CriticalFixedRankTransport
  CriticalRankDegreeComparison CriticalImageDegreeLaws
  RealHausdorffMeasure RealHausdorffMeasureLaws MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_4_3]: the complete theorem
    3.4.3, pp. 316–317. For m>nu>=0, k>=1,
    an arbitrary subset B of the original open A has
    H^[nu+(m-nu)/k](f(B))=0 when the actual differential
    has rank at most nu on B. Hahn–Banach coordinates,
    the original orthogonal kernel projection, and 3.4.2(9)
    prove local nullity on each actual rank stratum. A
    countable open cover, degree comparison, and null unions
    assemble the original image. No finite target dimension,
    completeness, measurability, or constant-rank neighbourhood is assumed. *)
Theorem federer_3_4_3 (R:realType) m nu k
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A B:set (R_n R m)) (f:R_n R m->Y)
    (hp:0<=nu%:R+(m-nu)%:R/k%:R):
  (nu<m)%N ->(1<=k)%N ->
  (forall a,A a ->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a) ->
  B `<=` A ->
  norm_class (inner_norm_real_norm (@euclidean_inner_productP R m)) hNY A f k ->
  (forall x,B x ->exists D:Hom (R_n R m) Y,
    has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f x D /\
    exists r,has_linear_rank D r /\(r<=nu)%N) ->
  @real_hausdorff_measure R (real_norm_metric_space hNY)
    (nu%:R+(m-nu)%:R/k%:R) hp (f @` B)=0%E.
Proof.
move=>hNu hk hOpen hBA hf hRankB.
pose X:=R_n R m.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
have [D hD]:=(norm_class_firstP hNX hNY A f).1 (norm_class_lower hk hf).
pose B0 r:set X:=[set x|B x /\has_linear_rank (D x) r].
pose H:=@real_hausdorff_measure R (real_norm_metric_space hNY)
  (nu%:R+(m-nu)%:R/k%:R) hp.
have hH:is_measure H:=@real_hausdorff_measure_is_measure R (real_norm_metric_space hNY)
  (nu%:R+(m-nu)%:R/k%:R) hp.
pose I:set nat:=[set r|(r<=nu)%N].
have hNull r (hr:I r):H (f @` B0 r)=0%E.
  have hRM:(r<m)%N:=leq_ltn_trans hr hNu.
  have hPR:=@critical_rank_degree_nonnegative R m r k hk.
  have hNullR:=@critical_original_fixed_rank_nullity R m r k hRM hk Y NY hNY A (B0 r) f hPR
    hf (fun x hx=>hBA x hx.1)
    (fun x hx=>ex_intro _ (D x) (conj (norm_class_one_differential hD (hBA x hx.1)) hx.2)).
  exact:(@critical_real_hausdorff_null_higher_degree R (real_norm_metric_space hNY)
    (r%:R+(m-r)%:R/k%:R) (nu%:R+(m-nu)%:R/k%:R) hPR hp (f @` B0 r)
    (@critical_rank_degree_monotone R m r nu k hr (ltnW hNu) hk) hNullR).
have hNullUnion:=@measure_null_countable_union R (real_norm_metric_space hNY)
  [the choiceType of (nat:Type)] H hH I (fun r=>f @` B0 r) (countableP I) hNull.
apply:(measure_null_subset hH _ hNullUnion).
move=>y [x hx <-].
have [M [hM [r [hRank hr]]]]:=hRankB x hx.
have hSame:D x=M:=norm_differential_unique hNX hNY
  (norm_class_one_differential hD (hBA x hx)) hM.
exists r;first exact:hr.
exists x;last reflexivity.
split;first exact:hx.
by rewrite hSame.
Qed.
