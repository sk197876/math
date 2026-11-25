(** Federer (1969), 4.1.8, p. 360: the actual
    first-variable slice test is opaque. Its independent
    pointwise and bilinear laws are public; the construction
    remains inside the proved existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap ExteriorGrading
  CurrentSpaces CurrentCartesianDomain CurrentCartesianSliceTestUP
  CurrentCartesianSliceTestExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CartesianSliceTestSignature.
(** Source for [value]: the original actual test on A
    to which S is applied in the displayed slice
    definition of Federer 4.1.8, p. 360. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (i j:nat),
  forall b:R_n R n,B b->exterior_power (R_n R n) j->
    @current_test_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
      (@current_cartesian_domain_open R m n A B hA hB) (i+j)->
    @current_test_space R h2 m A hA i.
(** Source for [laws]: the exact original slice values
    and bilinearity in eta and phi, Federer 4.1.8,
    p. 360, on the actual open factor domains. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (i j:nat),
  @is_current_cartesian_slice_test R h2 m n A B hA hB i j
    (@value R h2 m n A B hA hB i j).
End CartesianSliceTestSignature.
Module CartesianSliceTest:CartesianSliceTestSignature.
(** Source for [value]: hide the actual test witness
    supplied by the proved slice-test existence theorem,
    supporting Federer 4.1.8, p. 360. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (i j:nat):
  forall b:R_n R n,B b->exterior_power (R_n R n) j->
    @current_test_space R h2 (m+n) (@euclidean_cartesian_set R m n A B)
      (@current_cartesian_domain_open R m n A B hA hB) (i+j)->
    @current_test_space R h2 m A hA i:=
  projT1 (cid (@current_cartesian_slice_test_exists R h2 m n i j A B hA hB)).
(** Source for [laws]: the hidden witness satisfies
    the independently specified original law for the actual
    slice test in Federer 4.1.8, p. 360. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) (m n:nat)
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) B b) (i j:nat):
  @is_current_cartesian_slice_test R h2 m n A B hA hB i j
    (@value R h2 m n A B hA hB i j).
Proof.
exact:(projT2 (cid (@current_cartesian_slice_test_exists R h2 m n i j A B hA hB))).
Qed.
End CartesianSliceTest.
