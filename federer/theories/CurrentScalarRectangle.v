(** Federer (1969), 4.1.11, p. 366: the
    original scalar rectangular current, presented on
    its whole Euclidean domain and ambient degree.
    Retain the opaque finite product of 4.1.8;
    these adapters identify only equal domains and degrees. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentDomainTransport
  CurrentDomainTransportIdentity CurrentDomainTransportDegree CurrentCartesianProductSealed
  CurrentCartesianProductDegreeTransport CurrentAmbientCartesianProduct CurrentAmbientProductDomainTransport
  OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces OrientedRectangleCurrentSealed
  ScalarSegmentCoordinateValues ScalarSegmentFactors ScalarRectangleBoxCurrent EuclideanFundamentalCurrent EuclideanOneCoordinate
  OrientedSegmentCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentScalarRectangle.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factors := (@scalar_segment_factors R).
Local Notation D := (fun f=>oriented_rectangle_dimension (Factors f)).
Local Notation U := (fun f=>@oriented_rectangle_domain R (Factors f)).
Local Notation hU := (fun f=>@oriented_rectangle_domain_open R (Factors f)).
Local Notation P := (fun f=>@OrientedRectangleCurrent.value R h2 (Factors f)).
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).

(** Source for [current_scalar_rectangle_domain]: the
    original scalar product has the whole containing
    Euclidean domain, supporting the rectangular decomposition
    in Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_domain f:U f=Full (D f).
Proof.
apply:funext=>x;apply:propext;split=>_;first exact:Logic.I.
exact:(@scalar_rectangle_domain_whole R f x).
Qed.

(** Source for [current_scalar_rectangle]: the actual
    original finite rectangular current, with only equal
    degree and domain presentations identified, supporting
    Federer 4.1.11, p. 366. *)
Definition current_scalar_rectangle f:
    @current_space R h2 (D f) (Full (D f)) (hFull (D f)) (D f):=
  @current_domain_transport R h2 (D f) (U f) (hU f) (Full (D f))
    (current_scalar_rectangle_domain f) (hFull (D f)) (D f)
    (@current_degree_transport R h2 (D f) (U f) (hU f)
      (size (Factors f)) (D f) (@scalar_rectangle_current_degree R f) (P f)).

(** Source for [current_scalar_rectangle_empty]: the empty
    product is the original E^0, supporting the
    zero-dimensional decomposition in Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_empty:
  current_scalar_rectangle [::]=@euclidean_fundamental_current R h2 0%N.
Proof.
rewrite /current_scalar_rectangle current_degree_transport_identity.
rewrite ((@OrientedRectangleCurrent.laws R h2).1).
exact:current_domain_transport_identity.
Qed.

(** Source for [current_scalar_rectangle_single]: a single
    factor is its original oriented segment, supporting
    Federer 4.1.11, p. 366, including coincident endpoints. *)
Lemma current_scalar_rectangle_single (a:R*R):
  current_scalar_rectangle [::a]=
    @OrientedSegmentCurrent.value R h2 1%N (Full 1%N) (hFull 1%N)
      (@euclidean_one_embed R a.1) (@euclidean_one_embed R a.2)
      (fun (t:R) (_:t \in `[0,1])=>Logic.I).
Proof.
rewrite /current_scalar_rectangle current_degree_transport_identity.
rewrite ((@OrientedRectangleCurrent.laws R h2).2.1).
rewrite current_domain_transport_identity.
rewrite /oriented_segment_factor_current /scalar_segment_factor /=.
have hContains:(@scalar_segment_full_domain R a.1 a.2)=
    (fun (t:R) (_:t \in `[0,1])=>Logic.I):=Prop_irrelevance _ _.
by rewrite hContains.
Qed.

(** Source for [current_scalar_rectangle_attach]: attaching
    a first segment to a nonempty scalar rectangle
    is the original Cartesian current product, supporting
    the factorial induction in Federer 4.1.11, p. 366. *)
Lemma current_scalar_rectangle_attach (a b:R*R) t:
  current_scalar_rectangle (a::b::t)=
    @current_ambient_cartesian_product R h2 1%N (D (b::t)) 1%N (D (b::t))
      (@OrientedSegmentCurrent.value R h2 1%N (Full 1%N) (hFull 1%N)
        (@euclidean_one_embed R a.1) (@euclidean_one_embed R a.2)
        (fun (s:R) (_:s \in `[0,1])=>Logic.I))
      (current_scalar_rectangle (b::t)).
Proof.
have hDegree:(@scalar_rectangle_current_degree R (a::b::t))=
    congr2 addn (erefl 1%N) (@scalar_rectangle_current_degree R (b::t)):=Prop_irrelevance _ _.
rewrite /current_scalar_rectangle ((@OrientedRectangleCurrent.laws R h2).2.2) hDegree.
rewrite /oriented_rectangle_product current_cartesian_product_degree_transport
  current_degree_transport_identity.
rewrite (@current_ambient_product_domain_transport R h2 1%N (D (b::t))
  (Full 1%N) (U (b::t)) (hFull 1%N) (hU (b::t))
  (erefl (Full 1%N)) (current_scalar_rectangle_domain (b::t))
  (current_scalar_rectangle_domain (a::b::t)) 1%N (D (b::t))).
rewrite current_domain_transport_identity.
rewrite /oriented_segment_factor_current /scalar_segment_factor /=.
have hContains:(@scalar_segment_full_domain R a.1 a.2)=
    (fun (t:R) (_:t \in `[0,1])=>Logic.I):=Prop_irrelevance _ _.
by rewrite hContains.
Qed.
End CurrentScalarRectangle.
