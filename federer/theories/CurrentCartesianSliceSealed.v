(** Federer (1969), 4.1.8, p. 360: the original
    linear slice operator phi to phi_S is opaque. Its
    independent all-point pairing law is public. Continuity,
    compact support bounds and product-current laws are proved
    from this interface, not assumed in its specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianSliceUP CurrentCartesianSliceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CartesianSliceSignature.
(** Source for [value]: the original phi to phi_S
    from Federer 4.1.8, p. 360, on the actual
    compact test spaces and for every original current S. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b),
  @current_space R h2 m A hA i->
  Hom (@current_test_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
    (@current_cartesian_domain_open R m n A B hA hB) (i+j))
    (@current_test_space R h2 n B hB j).
(** Source for [laws]: every original eta pairing of
    the actual slice has the displayed first-current action,
    Federer 4.1.8, p. 360. This law assumes no
    product-current theorem or topological vector-space structure on D. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i),
  @is_current_cartesian_slice R h2 m n i j A B hA hB S
    (@value R h2 m n i j A B hA hB S).
End CartesianSliceSignature.
Module CartesianSlice:CartesianSliceSignature.
(** Source for [value]: seal the proved actual linear
    slice witness, supporting Federer 4.1.8, p. 360.
    No constructor or representative is exposed downstream. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i):
  Hom (@current_test_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
    (@current_cartesian_domain_open R m n A B hA hB) (i+j))
    (@current_test_space R h2 n B hB j):=
  projT1 (cid (@current_cartesian_slice_exists R h2 m n i j A B hA hB S)).
(** Source for [laws]: the opaque witness satisfies the
    independently specified original pairing law, supporting Federer
    4.1.8, p. 360. Choices are confined to its implementation. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (m n i j:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    (S:@current_space R h2 m A hA i):
  @is_current_cartesian_slice R h2 m n i j A B hA hB S
    (@value R h2 m n i j A B hA hB S).
Proof. exact:(projT2 (cid (@current_cartesian_slice_exists R h2 m n i j A B hA hB S))). Qed.
End CartesianSlice.
