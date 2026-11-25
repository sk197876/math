(** Federer (1969), 4.1.11, p. 366: assuming
    the lower-dimensional prism identities, compare the
    original Cartesian prism with its signed simplex
    sum by their boundaries. This is the printed
    induction before applying 4.1.10 in top degree. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  CurrentSpaces CurrentBoundary CurrentDirac CurrentCartesianPointInclusion CurrentSegmentMapUP
  OrientedSegmentCurrentSealed OrientedSegmentCurrentBoundary CurrentAmbientCartesianProduct
  CurrentAmbientProductBoundary CurrentAmbientProductFiniteSums CurrentAmbientLeftPointProduct
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentBoundary
  CurrentSimplexPrismSum CurrentPrismFaceSum CurrentPrismBoundary.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentSimplexPrismBoundaryComparison.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables p n m:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables a b:R_n R p.
Local Notation Lower := (@current_cartesian_point_inclusion R p n a).
Local Notation Upper := (@current_cartesian_point_inclusion R p n b).
Local Notation Segment := (@OrientedSegmentCurrent.value R h2 p (Full p) (hFull p)
  a b (fun (t:R) (_:t \in `[0,1])=>Logic.I)).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->R_n R n)=>@OrientedSimplexCurrent.value R h2 n d w).
Local Notation PSum := (fun (d:nat) (w:'I_(d.+1)->R_n R n)=>
  @current_simplex_prism_sum R h2 n (p+n)%N Lower Upper d w).
Local Notation Product := (fun d=>@current_ambient_cartesian_product R h2 p n 1%N d Segment).
Variable v:'I_(m.+2)->R_n R n.
Hypothesis hFaces:forall k:'I_(m.+2),
  Product m (F m (current_simplex_face v k))=PSum m (current_simplex_face v k).

(** Source for [current_simplex_prism_boundary_comparison]:
    the original prism and its signed simplex sum have
    the same boundary once the identities on the source
    faces are known, Federer 4.1.11, p. 366. The
    printed first-positive-degree case is included. The
    induction hypothesis is removed in the final prism theorem. *)
Theorem current_simplex_prism_boundary_comparison:
  @current_boundary R h2 (p+n)%N m.+1 (Full (p+n)%N) (hFull (p+n)%N)
    (Product m.+1 (F m.+1 v))=
  @current_boundary R h2 (p+n)%N m.+1 (Full (p+n)%N) (hFull (p+n)%N) (PSum m.+1 v).
Proof.
cbn beta.
have hCart:=@current_ambient_product_boundary_positive R h2 p n m Segment (F m.+1 v).
cbn beta in hCart.
have hSegment:=@oriented_segment_current_boundary R h2 p (Full p) (hFull p) a b
  (fun (t:R) (_:t \in `[0,1])=>Logic.I).
have hBilinear:=@current_ambient_cartesian_product_bilinear R h2 p n 0%N m.+1.
rewrite hSegment (bilBl hBilinear) in hCart.
rewrite (@current_ambient_left_point_simplex R h2 p n b m.+1 v) in hCart.
rewrite (@current_ambient_left_point_simplex R h2 p n a m.+1 v) in hCart.
rewrite (@oriented_simplex_current_boundary R h2 n m v) in hCart.
rewrite (@current_ambient_product_second_weighted_sum R h2 p n 1%N m
  (Finite.clone 'I_(m.+2) _) Segment (fun k=>(-1:R)^+k)
  (fun k=>F m (current_simplex_face v k))) in hCart.
have hFaceSum:(\sum_(k<m.+2) (-1:R)^+k*:
    Product m (F m (current_simplex_face v k)))=
    @current_prism_face_sum R h2 n (p+n)%N Lower Upper m v.
  rewrite /current_prism_face_sum;apply:eq_bigr=>k _.
  by rewrite (hFaces k).
cbn beta in hFaceSum.
rewrite hFaceSum in hCart.
have hSum:=@current_prism_sum_boundary R h2 n (p+n)%N Lower Upper m v.
cbn beta in hSum.
exact:(eq_trans hCart (esym hSum)).
Qed.
End CurrentSimplexPrismBoundaryComparison.
