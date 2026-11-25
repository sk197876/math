(** Federer (1969), 4.1.8, p. 361: the original
    interchange maps A times B to B times A and
    is proper on every original current support.
    Reuse the existing inverse swap and continuous
    inverse-image compactness, including empty factors. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCartesianSwap EuclideanCartesianSwapLinear
  CurrentSpaces CurrentCartesianDomain CurrentProperSupport CurrentInvertibleMapProperSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_cartesian_swap_image]: w(x,y)=(y,x)
    maps the original open product to its interchanged
    product, supporting Federer 4.1.8, p. 361.
    No nonemptiness or positive dimension is assumed. *)
Lemma current_cartesian_swap_image (R:realType) m n
    (A:set (R_n R m)) (B:set (R_n R n)) z:
  @euclidean_cartesian_set R m n A B z->
    @euclidean_cartesian_set R n m B A (@euclidean_cartesian_swap_map R m n z).
Proof.
move=>hz.
change (B (@euclidean_first_block_map R n m (@euclidean_cartesian_swap_map R m n z)) /\
  A (@euclidean_last_block_map R n m (@euclidean_cartesian_swap_map R m n z))).
rewrite euclidean_cartesian_swap_first euclidean_cartesian_swap_last.
exact:conj hz.2 hz.1.
Qed.

Section SwapProperness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n d:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BA := (@euclidean_cartesian_set R n m B A).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBA := (@current_cartesian_domain_open R n m B A hB hA).
Local Notation swap := (@euclidean_cartesian_swap_map R m n).
Local Notation back := (@euclidean_cartesian_swap_map R n m).
Local Notation Image := (fun z hz=>@current_cartesian_swap_image R m n A B z hz).
Local Notation Back := (fun z hz=>@current_cartesian_swap_image R n m B A z hz).

(** Source for [current_cartesian_swap_proper_on_support]:
    w is proper on every actual support in A
    times B, so the signed product pushforward in
    Federer 4.1.8, p. 361 needs no extra
    properness hypothesis. The earlier inverse-swap and
    original support closedness prove it. *)
Theorem current_cartesian_swap_proper_on_support
    (C:@current_space R h2 (m+n) AB hAB d):
  @is_current_proper_on_support R h2 (m+n) (n+m) d AB hAB BA C swap Image.
Proof.
apply:(@current_invertible_map_proper_on_support R h2 (m+n) (n+m) d
  AB BA hAB C swap back Image Back).
- move=>z hz;exact:(@euclidean_cartesian_swapK R m n z).
- move=>z hz;exact:(@euclidean_cartesian_swapK R n m z).
- exact:(norm_class_continuous (@euclidean_cartesian_swap_smooth R n m BA hBA 0%N)).
Qed.
End SwapProperness.
