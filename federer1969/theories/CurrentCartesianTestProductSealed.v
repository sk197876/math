(** Federer (1969), 4.1.8, p. 360: the actual separated test
    is opaque and has the independently specified bilinear and
    pointwise laws. Its construction serves only the proved
    existence theorem. Consumers cannot unfold the chosen witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianTestProductUP
  CurrentCartesianTestProductExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Module Type CartesianTestProductSignature.
(** Source for [value]: the original separated test p#alpha
    wedge q#beta of Federer 4.1.8, p. 360. The opaque map
    takes the genuine factor tests to the genuine product test. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (k l:nat),
  @current_test_space R h2 m A hA k->
  @current_test_space R h2 n B hB l->
  @current_test_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
    (@current_cartesian_domain_open R m n A B hA hB) (k+l).

(** Source for [laws]: bilinearity and the displayed
    pointwise product characterize the actual separated tests
    of Federer 4.1.8, p. 360, on the original domains. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (k l:nat),
  @is_current_cartesian_test_product R h2 m n A B hA hB k l
    (@value R h2 m n A B hA hB k l).
End CartesianTestProductSignature.

Module CartesianTestProduct:CartesianTestProductSignature.
(** Source for [value]: hide the witness of the proved
    separated-test existence theorem for Federer 4.1.8,
    p. 360. No existence premise is introduced. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (k l:nat):
    @current_test_space R h2 m A hA k->
    @current_test_space R h2 n B hB l->
    @current_test_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
      (@current_cartesian_domain_open R m n A B hA hB) (k+l):=
  projT1 (cid (@current_cartesian_test_product_exists R h2 m n A B hA hB k l)).

(** Source for [laws]: the opaque test map satisfies the
    independent original value law for Federer 4.1.8,
    p. 360. The existence proof supplies both conjuncts. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (k l:nat):
  @is_current_cartesian_test_product R h2 m n A B hA hB k l
    (@value R h2 m n A B hA hB k l).
Proof.
exact:(projT2 (cid (@current_cartesian_test_product_exists R h2 m n A B hA hB k l))).
Qed.
End CartesianTestProduct.
