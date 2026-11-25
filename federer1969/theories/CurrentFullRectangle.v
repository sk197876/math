(** Federer (1969), 4.1.11, p. 366: retain
    the actual original finite rectangular current with
    arbitrary-dimensional whole-space segment factors.
    Only the equal containing domain is identified. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDomainTransport CurrentDomainTransportIdentity CurrentAmbientCartesianProduct
  CurrentAmbientProductDomainTransport CurrentSegmentMapUP OrientedSegmentCurrentSealed
  OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces OrientedRectangleCurrentSealed
  EuclideanFundamentalCurrent CurrentSegmentFullDomainTransport CurrentFullRectangleDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFullRectangle.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).
Local Notation D := (@oriented_rectangle_dimension R).
Local Notation U := (fun f:seq Factor=>@oriented_rectangle_domain R f).
Local Notation hU := (fun f:seq Factor=>@oriented_rectangle_domain_open R f).
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).

(** Source for [current_full_rectangle]: the original
    opaque rectangular current on its equal whole
    Euclidean domain, supporting Federer 4.1.11, p. 366.
    Its degree is the number of segment factors,
    independently of their ambient dimensions. *)
Definition current_full_rectangle (f:seq Factor) (hf:is_current_full_rectangle_family f):
    @current_space R h2 (D f) (Full (D f)) (hFull (D f)) (size f):=
  @current_domain_transport R h2 (D f) (U f) (hU f) (Full (D f))
    (@current_full_rectangle_domain R f hf) (hFull (D f)) (size f)
    (@OrientedRectangleCurrent.value R h2 f).

(** Source for [current_full_rectangle_empty]: the original
    empty product is E^0, supporting the dimension-zero
    factorial decomposition in Federer 4.1.11, p. 366. *)
Lemma current_full_rectangle_empty (hf:is_current_full_rectangle_family ([::]:seq Factor)):
  @current_full_rectangle [::] hf=@euclidean_fundamental_current R h2 0%N.
Proof.
rewrite /current_full_rectangle ((@OrientedRectangleCurrent.laws R h2).1).
exact:current_domain_transport_identity.
Qed.

(** Source for [current_full_rectangle_single]: the single
    original factor is the original full-space segment,
    supporting Federer 4.1.11, p. 366. *)
Lemma current_full_rectangle_single (a:Factor) (hf:is_current_full_rectangle_family [::a]):
  @current_full_rectangle [::a] hf=
  @OrientedSegmentCurrent.value R h2 (oriented_segment_factor_dimension a)
    (Full (oriented_segment_factor_dimension a)) (hFull (oriented_segment_factor_dimension a))
    (oriented_segment_factor_start a) (oriented_segment_factor_end a)
    (fun (t:R) (_:t \in `[0,1])=>Logic.I).
Proof.
rewrite /current_full_rectangle ((@OrientedRectangleCurrent.laws R h2).2.1)
  /oriented_segment_factor_current.
exact:current_segment_full_domain_transport.
Qed.

(** Source for [current_full_rectangle_attach]: attaching
    the original first segment is its preceding Cartesian
    current product, supporting the factorial decomposition
    in Federer 4.1.11, p. 366. All original factor
    dimensions and degrees are retained. *)
Lemma current_full_rectangle_attach (a b:Factor) t
    (hf:is_current_full_rectangle_family (a::b::t)):
  @current_full_rectangle (a::b::t) hf=
  @current_ambient_cartesian_product R h2 (oriented_segment_factor_dimension a) (D (b::t))
    1%N (size (b::t))
    (@OrientedSegmentCurrent.value R h2 (oriented_segment_factor_dimension a)
      (Full (oriented_segment_factor_dimension a)) (hFull (oriented_segment_factor_dimension a))
      (oriented_segment_factor_start a) (oriented_segment_factor_end a)
      (fun (s:R) (_:s \in `[0,1])=>Logic.I))
    (@current_full_rectangle (b::t) hf.2).
Proof.
rewrite /current_full_rectangle ((@OrientedRectangleCurrent.laws R h2).2.2) /oriented_rectangle_product.
rewrite (@current_ambient_product_domain_transport R h2 (oriented_segment_factor_dimension a) (D (b::t))
  (@oriented_segment_factor_domain R a) (U (b::t)) (@oriented_segment_factor_open R a) (hU (b::t))
  hf.1 (@current_full_rectangle_domain R (b::t) hf.2)
  (@current_full_rectangle_domain R (a::b::t) hf) 1%N (size (b::t))).
by rewrite /oriented_segment_factor_current current_segment_full_domain_transport.
Qed.
End CurrentFullRectangle.
