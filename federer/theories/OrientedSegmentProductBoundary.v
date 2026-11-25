(** Federer (1969), 4.1.8, p. 362: both
    original boundary formulas for a segment times an
    arbitrary current. Substitute the proved endpoint
    boundary into the original product boundary laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentBoundary CurrentDirac CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianProductBilinear
  CurrentCartesianBoundaryPositive CurrentCartesianBoundaryFirstZero CurrentSegmentMapUP
  OrientedSegmentCurrentSealed OrientedSegmentCurrentBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSegmentProductBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Variables u v:X.
Hypothesis hSegment:@is_current_segment_domain R m A u v.
Local Notation S := (@OrientedSegmentCurrent.value R h2 m A hA u v hSegment).
Local Notation delta := (@dirac_current R h2 m A hA).
Local Notation Product := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).

(** Source for [oriented_segment_product_boundary_positive]:
    boundary([u,v] times T)=delta_v times T minus
    delta_u times T minus [u,v] times boundary T
    for positive-degree T, the first original segment
    product formula in Federer 4.1.8, p. 362. *)
Theorem oriented_segment_product_boundary_positive j (T:@current_space R h2 n B hB j.+1):
  @current_boundary R h2 (m+n) j.+1 AB hAB (Product 1%N j.+1 S T)=
    Product 0%N j.+1 (delta v) T-Product 0%N j.+1 (delta u) T-
    Product 1%N j S (@current_boundary R h2 n j B hB T).
Proof.
have h:=@current_cartesian_boundary_positive R h2 m n A B hA hB 0%N j S T.
rewrite !current_degree_transport_identity expr1 scaleN1r
  (@oriented_segment_current_boundary R h2 m A hA u v hSegment) in h.
rewrite (bilBl (@current_cartesian_product_bilinear R h2 m n 0%N j.+1 A B hA hB)) in h.
exact:h.
Qed.

(** Source for [oriented_segment_product_boundary_zero]:
    boundary([u,v] times T)=delta_v times T minus
    delta_u times T when T has degree zero,
    the second original segment-product formula in
    Federer 4.1.8, p. 362. No boundary of
    a zero-degree current is introduced. *)
Theorem oriented_segment_product_boundary_zero (T:@current_space R h2 n B hB 0%N):
  @current_boundary R h2 (m+n) 0%N AB hAB (Product 1%N 0%N S T)=
    Product 0%N 0%N (delta v) T-Product 0%N 0%N (delta u) T.
Proof.
have h:=@current_cartesian_boundary_first_zero R h2 m n A B hA hB 0%N S T.
rewrite current_degree_transport_identity
  (@oriented_segment_current_boundary R h2 m A hA u v hSegment) in h.
rewrite (bilBl (@current_cartesian_product_bilinear R h2 m n 0%N 0%N A B hA hB)) in h.
exact:h.
Qed.
End OrientedSegmentProductBoundary.
