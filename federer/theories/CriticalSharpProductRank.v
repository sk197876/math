(** Federer (1969), 3.4.4, p. 318: retain
    the original arbitrary source dimension in the exact rank conclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm
  InnerMetric EuclideanOneCoordinate CriticalSharpProductUP CriticalPrefixRank
  CriticalSharpProductDifferential LinearRankUP NormDifferentialUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_prefix_rank_original_dimension]: the
    exact rank nu of the prefix differential for every
    original m>=nu, 3.4.4, p. 318.
    The complementary block has its actual dimension m-nu. *)
Lemma critical_prefix_rank_original_dimension (R:realType) m nu:
  (nu<=m)%N ->has_linear_rank (@critical_prefix_linear_map R m nu) nu.
Proof.
move=>hNu.
have hDimension:(nu+(m-nu))%N=m by rewrite subnKC.
have hRank:=@critical_prefix_linear_rank R nu (m-nu)%N.
by rewrite hDimension in hRank.
Qed.

(** Source for [critical_sharp_product_rank]: dim im Df(x)=nu
    on the original critical product source in 3.4.4,
    p. 318. The actual coordinate differential and its
    actual range dimension are proved independently and then joined. *)
Theorem critical_sharp_product_rank (R:realType) m nu g
    (F:R_n R m->R_n R m) (x:R_n R m):
  (nu<=m)%N ->is_critical_sharp_product_map nu g F ->
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) F ->
  (forall i:'I_m,(nu<=i)%N ->has_norm_differential
    (inner_norm (@euclidean_inner_productP R 1)) (fun t:R^o=>`|t|)
    (fun _=>True) g (euclidean_one_embed (x i)) 0) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) (fun _=>True) F x
    (@critical_prefix_linear_map R m nu) /\
  has_linear_rank (@critical_prefix_linear_map R m nu) nu.
Proof.
move=>hNu hF hClass hFlat;split.
- exact:(@critical_sharp_product_actual_differential R m nu g F x hF hClass hFlat).
- exact:critical_prefix_rank_original_dimension hNu.
Qed.
