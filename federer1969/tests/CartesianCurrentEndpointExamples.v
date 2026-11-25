(** Actual-space endpoint checks for Federer (1969), 4.1.8,
    p. 362: the empty product is nonzero E^0,
    while a zero-length segment in R^0 is zero.
    These cases distinguish zero factors from a single
    degenerate factor and retain the positive-degree boundary. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary OrientedSegmentCurrentSealed
  OrientedSegmentCurrentDegenerate OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentSealed EuclideanFundamentalCurrent EuclideanFundamentalCurrentNonzero.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CartesianCurrentEndpointExamples.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R 0%N)) x).

(** Source for [empty_cartesian_current_nonzero]: the original
    empty product is the nonzero Euclidean unit current,
    the zero-factor case of Federer 4.1.8, p. 362,
    with E^0 from 4.1.7, p. 357. *)
Example empty_cartesian_current_nonzero:
  @OrientedRectangleCurrent.value R h2 [::]<>0.
Proof.
rewrite ((@OrientedRectangleCurrent.laws R h2).1).
exact:(@euclidean_fundamental_current_nonzero R h2 0%N).
Qed.

(** Source for [zero_dimensional_segment_factor]: a single
    original degenerate endpoint pair in R^0,
    checking the zero-length convention of Federer
    4.1.8, p. 362, on the actual space. *)
Definition zero_dimensional_segment_factor:oriented_segment_factor R:={|
  oriented_segment_factor_dimension:=0%N;
  oriented_segment_factor_domain:=fun _=>True;
  oriented_segment_factor_open:=hFull;
  oriented_segment_factor_start:=0;
  oriented_segment_factor_end:=0;
  oriented_segment_factor_contains:=fun _ _=>Logic.I
|}.

(** Source for [single_zero_dimensional_rectangle_zero]: one
    degenerate factor gives zero, whereas the empty
    product above is nonzero, checking the actual
    conventions in Federer 4.1.8, p. 362. *)
Example single_zero_dimensional_rectangle_zero:
  @OrientedRectangleCurrent.value R h2 [::zero_dimensional_segment_factor]=0.
Proof.
rewrite ((@OrientedRectangleCurrent.laws R h2).2.1).
exact:oriented_segment_current_degenerate.
Qed.

(** Source for [single_zero_dimensional_rectangle_boundary_zero]: the
    positive-degree degenerate segment has zero boundary
    on the actual R^0 domain, checking the
    original endpoint formula of Federer 4.1.8, p. 362.
    No boundary of a degree-zero current is used. *)
Example single_zero_dimensional_rectangle_boundary_zero:
  @current_boundary R h2 0%N 0%N (fun _=>True) hFull
    (@OrientedRectangleCurrent.value R h2 [::zero_dimensional_segment_factor])=0.
Proof. by rewrite single_zero_dimensional_rectangle_zero linear0. Qed.
End CartesianCurrentEndpointExamples.
