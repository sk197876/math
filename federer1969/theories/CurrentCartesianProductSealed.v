(** Federer (1969), 4.1.8, p. 360: the actual product
    current is opaque and specified by the original complete
    mixed-degree separated-test equations. Its construction
    serves only the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianProductUP CurrentCartesianTestProductSealed
  CurrentCartesianProductExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CartesianCurrentProductSignature.
(** Source for [value]: S times T on the original open
    factors, specified by both mixed-test equations of
    Federer 4.1.8, p. 360. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j),
  @current_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
    (@current_cartesian_domain_open R m n A B hA hB) (i+j).
(** Source for [laws]: the opaque product has exactly
    the two original separated-test values in every mixed
    degree, Federer 4.1.8, p. 360. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j),
  @is_current_cartesian_product R h2 m n A B hA hB
    (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l) i j S T
    (@value R h2 m n i j A B hA hB S T).
End CartesianCurrentProductSignature.
Module CartesianCurrentProduct:CartesianCurrentProductSignature.
(** Source for [value]: hide the witness of the proved
    original product-current existence theorem, supporting
    Federer 4.1.8, p. 360. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  @current_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
    (@current_cartesian_domain_open R m n A B hA hB) (i+j):=
  projT1 (cid (@current_cartesian_product_exists R h2 m n i j A B hA hB S T)).
(** Source for [laws]: the hidden witness satisfies the
    independently specified complete mixed-test characterisation,
    supporting Federer 4.1.8, p. 360. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  @is_current_cartesian_product R h2 m n A B hA hB
    (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l) i j S T
    (@value R h2 m n i j A B hA hB S T).
Proof.
exact:(projT2 (cid (@current_cartesian_product_exists R h2 m n i j A B hA hB S T))).1.
Qed.
End CartesianCurrentProduct.
