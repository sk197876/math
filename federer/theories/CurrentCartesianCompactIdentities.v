(** Federer (1969), 4.1.11, p. 365: use the preceding
    Cartesian swap and natural association on compact sources.
    These adapters retain the original proved current identities
    while permitting every smoothness and image proof of the
    same original coordinate maps. No product theorem is reproved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockLinearMaps
  EuclideanCartesianMap EuclideanCartesianSwapLinear EuclideanDimensionCastLinear
  CurrentSpaces CurrentCartesianDomain CurrentDegreeTransport CurrentProperSupport
  CurrentCartesianProductSealed CurrentCompactMapProper
  CurrentPushforwardSealed CurrentPushforwardMapAgreement CurrentCompactPushforwardAlgebra
  CurrentCartesianSwapDomain CurrentCartesianSwapPushforward CurrentCartesianProductSwap
  CurrentCartesianReassociationDomain CurrentCartesianReassociationPushforward
  CurrentCartesianProductAssociative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Swap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BA := (@euclidean_cartesian_set R n m B A).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBA := (@current_cartesian_domain_open R n m B A hB hA).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation swap := (@euclidean_cartesian_swap_map R m n).
Local Notation Image := (fun z hz=>@current_cartesian_swap_image R m n A B z hz).
Local Notation hSmooth := (@euclidean_cartesian_swap_smooth R m n AB hAB).
Variables i j:nat.
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Local Notation Product := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).
Hypothesis hProduct:@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R (m+n)%N)))
  (@current_support R h2 (m+n)%N AB hAB (i+j)%N Product).
Hypothesis hImage:forall z,AB z->BA (swap z).
Hypothesis hf:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R (m+n)%N))
  (inner_norm_real_norm (@euclidean_inner_productP R (n+m)%N)) AB swap.

(** Source for [current_cartesian_compact_swap]: the original
    graded Cartesian swap identity, with the compact-source
    pushforward and arbitrary proof parameters, supporting the
    reversing calculation of Federer 4.1.11, p. 365. The complete
    signed product theorem of 4.1.8, p. 361, is reused. *)
Theorem current_cartesian_compact_swap:
  @current_degree_transport R h2 (n+m)%N BA hBA (i+j)%N (j+i)%N (addnC i j)
    (@current_compact_map_pushforward R h2 (m+n)%N (n+m)%N
      AB BA hAB hBA swap hImage hf (i+j)%N Product hProduct)=
  (-1:R)^+(i*j)*:@CartesianCurrentProduct.value R h2 n m j i B A hB hA T S.
Proof.
have hCompare:=@current_pushforward_map_agreement R h2 (m+n)%N (n+m)%N (i+j)%N
  AB BA hAB hBA swap swap hImage Image hf hSmooth Product
  (@current_compact_map_proper R h2 (m+n)%N (n+m)%N (i+j)%N AB BA hAB Product
    swap hImage (norm_class_continuous (hf 0%N)) hProduct)
  (@current_cartesian_swap_proper_on_support R h2 m n (i+j)%N A B hA hB Product)
  (fun _ _=>erefl).
rewrite /current_compact_map_pushforward hCompare.
exact:(@current_cartesian_product_swap R h2 m n A B hA hB i j S T).
Qed.
End Swap.
Section Association.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n v:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)) (C:set (R_n R v)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Hypothesis hC:forall c,C c->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R v)) C c.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BC := (@euclidean_cartesian_set R n v B C).
Local Notation Left := (@euclidean_cartesian_set R (m+n) v AB C).
Local Notation Right := (@euclidean_cartesian_set R m (n+v) A BC).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBC := (@current_cartesian_domain_open R n v B C hB hC).
Local Notation hLeft := (@current_cartesian_domain_open R (m+n) v AB C hAB hC).
Local Notation hRight := (@current_cartesian_domain_open R m (n+v) A BC hA hBC).
Local Notation assoc := (@euclidean_dimension_cast_map R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v))).
Local Notation Image := (fun z hz=>@current_cartesian_reassociation_image R m n v A B C z hz).
Local Notation hSmooth := (@euclidean_dimension_cast_smooth R ((m+n)+v)%N (m+(n+v))%N
  (esym (addnA m n v)) Left hLeft).
Variables i j k:nat.
Variable S:@current_space R h2 m A hA i.
Variable T:@current_space R h2 n B hB j.
Variable U:@current_space R h2 v C hC k.
Local Notation Pair := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T).
Local Notation Product := (@CartesianCurrentProduct.value R h2 (m+n)%N v (i+j)%N k
  AB C hAB hC Pair U).
Hypothesis hProduct:@compact (real_norm_metric_space
  (inner_norm_real_norm (@euclidean_inner_productP R ((m+n)+v)%N)))
  (@current_support R h2 ((m+n)+v)%N Left hLeft ((i+j)+k)%N Product).
Hypothesis hImage:forall z,Left z->Right (assoc z).
Hypothesis hf:norm_class_all_orders
  (inner_norm_real_norm (@euclidean_inner_productP R ((m+n)+v)%N))
  (inner_norm_real_norm (@euclidean_inner_productP R (m+(n+v))%N)) Left assoc.

(** Source for [current_cartesian_compact_association]: the
    original natural Cartesian association, written with the
    compact-source pushforward and arbitrary proof parameters,
    supporting Federer 4.1.11, pp. 365–366. Reuse the full
    all-degree associativity theorem of 4.1.8, p. 361. *)
Theorem current_cartesian_compact_association:
  @current_degree_transport R h2 (m+(n+v))%N Right hRight ((i+j)+k)%N (i+(j+k))%N
    (esym (addnA i j k))
    (@current_compact_map_pushforward R h2 ((m+n)+v)%N (m+(n+v))%N
      Left Right hLeft hRight assoc hImage hf ((i+j)+k)%N Product hProduct)=
  @CartesianCurrentProduct.value R h2 m (n+v)%N i (j+k)%N A BC hA hBC S
    (@CartesianCurrentProduct.value R h2 n v j k B C hB hC T U).
Proof.
have hCompare:=@current_pushforward_map_agreement R h2 ((m+n)+v)%N (m+(n+v))%N ((i+j)+k)%N
  Left Right hLeft hRight assoc assoc hImage Image hf hSmooth Product
  (@current_compact_map_proper R h2 ((m+n)+v)%N (m+(n+v))%N ((i+j)+k)%N
    Left Right hLeft Product assoc hImage (norm_class_continuous (hf 0%N)) hProduct)
  (@current_cartesian_reassociation_proper_on_support R m n v A B C h2 hA hB hC
    ((i+j)+k)%N Product) (fun _ _=>erefl).
rewrite /current_compact_map_pushforward hCompare.
exact:(@current_cartesian_product_associative R h2 m n v A B C hA hB hC i j k S T U).
Qed.
End Association.
