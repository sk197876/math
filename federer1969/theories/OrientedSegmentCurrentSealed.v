(** Federer (1969), 4.1.8, p. 362: the original
    oriented segment current is opaque and specified by
    its actual scalar interval integral. Existence uses
    the proved original Radon-density construction only. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSegmentMapUP
  OrientedSegmentCurrentUP OrientedSegmentCurrentExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type OrientedSegmentCurrentSignature.
(** Source for [value]: the original [u,v] in D_1(A)
    when A contains the segment, Federer 4.1.8, p. 362. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) n (A:set (R_n R n))
    (hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x)
    (u v:R_n R n),@is_current_segment_domain R n A u v ->@current_space R h2 n A hA 1%N.
(** Source for [laws]: the original printed all-test
    interval integral specifies the segment current,
    Federer 4.1.8, p. 362. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0) n (A:set (R_n R n))
    (hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x)
    (u v:R_n R n) (hSegment:@is_current_segment_domain R n A u v),
  @is_oriented_segment_current R h2 n A hA u v (@value R h2 n A hA u v hSegment).
End OrientedSegmentCurrentSignature.
Module OrientedSegmentCurrent:OrientedSegmentCurrentSignature.
(** Source for [value]: seal the proved original
    integral-current witness, supporting Federer 4.1.8,
    p. 362. No boundary law is assumed. *)
Definition value (R:realType) (h2:(1+1:R)!=0) n (A:set (R_n R n))
    (hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x)
    (u v:R_n R n) (hSegment:@is_current_segment_domain R n A u v):@current_space R h2 n A hA 1%N:=
  projT1 (cid (@oriented_segment_current_exists R h2 n A hA u v hSegment)).
(** Source for [laws]: the opaque witness satisfies
    exactly its independent original integral condition,
    supporting Federer 4.1.8, p. 362. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0) n (A:set (R_n R n))
    (hA:forall x,A x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) A x)
    (u v:R_n R n) (hSegment:@is_current_segment_domain R n A u v):
  @is_oriented_segment_current R h2 n A hA u v (@value R h2 n A hA u v hSegment).
Proof. exact:(projT2 (cid (@oriented_segment_current_exists R h2 n A hA u v hSegment))). Qed.
End OrientedSegmentCurrent.
