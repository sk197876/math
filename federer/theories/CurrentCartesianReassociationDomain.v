(** Federer (1969), 4.1.8, p. 361: natural
    reassociation of three original factors maps precisely
    between their open products and is proper on each
    actual current support. Reuse the existing dimension
    cast and its original coordinate-list and inverse laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap EuclideanCoordinateLists
  EuclideanDimensionCastLinear EuclideanCartesianReassociation CurrentSpaces CurrentCartesianDomain
  CurrentProperSupport CurrentInvertibleMapProperSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianReassociationDomain.
Variable R:realType.
Variables m n v:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)) (C:set (R_n R v)).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation BC := (@euclidean_cartesian_set R n v B C).
Local Notation Left := (@euclidean_cartesian_set R (m+n) v AB C).
Local Notation Right := (@euclidean_cartesian_set R m (n+v) A BC).
Local Notation eDim := (esym (addnA m n v)).
Local Notation assoc := (@euclidean_dimension_cast_map R ((m+n)+v)%N (m+(n+v))%N eDim).
Local Notation back := (@euclidean_dimension_cast_map R (m+(n+v))%N ((m+n)+v)%N (esym eDim)).

(** Source for [current_cartesian_reassociation_image]: the
    original natural association carries (A times B) times C
    into A times (B times C), supporting Federer 4.1.8,
    p. 361, with every empty block retained. *)
Lemma current_cartesian_reassociation_image z:Left z->Right (assoc z).
Proof. exact:(@euclidean_cartesian_reassociate_domain R m n v A B C z).1. Qed.

(** Source for [current_cartesian_reassociation_inverse]: the
    original dimension cast and its reverse are inverse,
    supporting natural association in Federer 4.1.8, p. 361. *)
Lemma current_cartesian_reassociation_inverse z:back (assoc z)=z.
Proof. exact:(@euclidean_dimension_castK R ((m+n)+v)%N (m+(n+v))%N eDim z). Qed.

(** Source for [current_cartesian_reassociation_inverse_reverse]:
    the original reverse identification also has a right
    inverse, supporting Federer 4.1.8, p. 361.
    Coordinate lists remove equality-proof bookkeeping. *)
Lemma current_cartesian_reassociation_inverse_reverse z:assoc (back z)=z.
Proof.
apply:(@euclidean_coordinate_list_injective R (m+(n+v))%N).
change (euclidean_coordinate_list (euclidean_dimension_cast eDim
  (euclidean_dimension_cast (esym eDim) z))=euclidean_coordinate_list z).
by rewrite !euclidean_dimension_cast_list.
Qed.

(** Source for [current_cartesian_reassociation_back_image]:
    the original reverse identification preserves all three
    factor domains, supporting Federer 4.1.8, p. 361. *)
Lemma current_cartesian_reassociation_back_image z:Right z->Left (back z).
Proof.
move=>hz;apply:(@euclidean_cartesian_reassociate_domain R m n v A B C (back z)).2.
by rewrite current_cartesian_reassociation_inverse_reverse.
Qed.

Hypothesis h2:(1+1:R)!=0.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Hypothesis hC:forall c,C c->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R v)) C c.
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation hBC := (@current_cartesian_domain_open R n v B C hB hC).
Local Notation hLeft := (@current_cartesian_domain_open R (m+n) v AB C hAB hC).
Local Notation hRight := (@current_cartesian_domain_open R m (n+v) A BC hA hBC).
Local Notation Image := (fun z hz=>@current_cartesian_reassociation_image z hz).
Local Notation Back := (fun z hz=>@current_cartesian_reassociation_back_image z hz).

(** Source for [current_cartesian_reassociation_proper_on_support]:
    natural association is proper on every actual current
    support in the original three-factor domain, supporting
    the associativity identity of Federer 4.1.8, p. 361.
    No extra properness premise is imposed. *)
Theorem current_cartesian_reassociation_proper_on_support d
    (T:@current_space R h2 ((m+n)+v) Left hLeft d):
  @is_current_proper_on_support R h2 ((m+n)+v) (m+(n+v)) d Left hLeft Right T assoc Image.
Proof.
apply:(@current_invertible_map_proper_on_support R h2 ((m+n)+v) (m+(n+v)) d
  Left Right hLeft T assoc back Image Back).
- move=>z hz;exact:current_cartesian_reassociation_inverse.
- move=>z hz;exact:current_cartesian_reassociation_inverse_reverse.
- exact:(norm_class_continuous (@euclidean_dimension_cast_smooth R (m+(n+v))%N ((m+n)+v)%N
    (esym eDim) Right hRight 0%N)).
Qed.
End CurrentCartesianReassociationDomain.
