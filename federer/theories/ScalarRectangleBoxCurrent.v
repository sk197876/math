(** Federer (1969), 4.1.8, p. 362: the
    finite ordered scalar segment product is the
    actual Euclidean current restricted to the original
    open coordinate box. The proof follows the
    original binary product and finite induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentOpenRestriction CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentCartesianProductDegreeTransport CurrentCartesianEuclideanCharacteristic
  OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces OrientedRectangleCurrentSealed
  ScalarSegmentFactors ScalarSegmentFactorInterval ScalarRectangleBox ScalarRectangleBoxMeasurable
  EuclideanFundamentalCurrent EuclideanCharacteristicCurrent EuclideanCharacteristicRestriction
  OpenEuclideanCharacteristicCurrent OpenEuclideanCharacteristicFull OpenEuclideanCharacteristicRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarRectangleBoxCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factors := (@scalar_segment_factors R).
Local Notation D := (fun f=>oriented_rectangle_dimension (Factors f)).
Local Notation U := (fun f=>@oriented_rectangle_domain R (Factors f)).
Local Notation hU := (fun f=>@oriented_rectangle_domain_open R (Factors f)).
Local Notation P := (fun f=>@OrientedRectangleCurrent.value R h2 (Factors f)).
Local Notation Box := (fun f:seq (R*R)=>@scalar_rectangle_box R f).
Local Notation hBox := (fun f:seq (R*R)=>@scalar_rectangle_box_measurable R f).
Local Notation C := (fun f=>@open_euclidean_characteristic_current R h2 (D f) (U f) (hU f) (Box f) (hBox f)).

(** Source for [scalar_rectangle_current_degree]: the original
    finite scalar product has exactly its original
    Euclidean ambient degree, supporting E^nu in
    Federer 4.1.8, p. 362. Mapping endpoint pairs
    to their original factors preserves their number. *)
Lemma scalar_rectangle_current_degree (f:seq (R*R)):
  size (Factors f)=D f.
Proof.
transitivity (size f).
- change (size [seq @scalar_segment_factor R p|p<-f]=size f).
  by rewrite size_map.
- exact:esym (@scalar_rectangle_dimension R f).
Qed.

(** Source for [scalar_rectangle_box_current]: the original
    finite ordered segment product equals E^nu
    contracted the open coordinate box, on its
    original containing Cartesian domain, Federer 4.1.8,
    p. 362. The sole transport identifies the
    proved equality nu=number of scalar coordinates.
    The empty family uses the original E^0. *)
Theorem scalar_rectangle_box_current (f:seq (R*R)):
  scalar_rectangle_ordered f->
  @current_degree_transport R h2 (D f) (U f) (hU f) (size (Factors f)) (D f)
    (@scalar_rectangle_current_degree f) (P f)=C f.
Proof.
elim:f=>[|a [|b t] IH].
- move=>_.
  rewrite current_degree_transport_identity ((@OrientedRectangleCurrent.laws R h2).1).
  rewrite open_euclidean_characteristic_current_full euclidean_characteristic_current_whole.
  by [].
- move=>ha.
  have /andP [ha' _]:(a.1<a.2)&&true:=ha.
  rewrite current_degree_transport_identity ((@OrientedRectangleCurrent.laws R h2).2.1).
  exact:(@scalar_segment_factor_interval R h2 a (hBox [::a]) ha').
- move=>hOrdered.
  have /andP [ha hTailOrdered]:(a.1<a.2)&&scalar_rectangle_ordered (b::t):=hOrdered.
  have hTail:=IH hTailOrdered.
  have hDegree:(@scalar_rectangle_current_degree (a::b::t))=
      congr2 addn (erefl 1%N) (@scalar_rectangle_current_degree (b::t)):=Prop_irrelevance _ _.
  rewrite ((@OrientedRectangleCurrent.laws R h2).2.2) hDegree.
  rewrite /oriented_rectangle_product current_cartesian_product_degree_transport
    current_degree_transport_identity hTail.
  rewrite (@scalar_segment_factor_interval R h2 a (hBox [::a]) ha).
  exact:(@current_cartesian_euclidean_characteristic R h2 1%N (D (b::t))
    (fun _=>True) (U (b::t))
    (fun x (_:True)=>@norm_full_domain_interior R (R_n R 1%N)
      (inner_norm (@euclidean_inner_productP R 1%N)) x) (hU (b::t))
    (Box [::a]) (Box (b::t)) (hBox [::a]) (hBox (b::t)) (hBox (a::b::t))).
Qed.

(** Source for [scalar_rectangle_euclidean_restriction]: on the
    original whole Euclidean space, the product of
    the ordered scalar segments is the actual
    original measurable restriction of E^nu to
    {x:u_k<x_k<v_k}, exactly the final display
    of Federer 4.1.8, p. 362. The original
    block domains are whole by scalar_rectangle_domain_whole;
    scalar_rectangle_box_coordinates gives every printed inequality. *)
Theorem scalar_rectangle_euclidean_restriction (f:seq (R*R)):
  scalar_rectangle_ordered f->
  @current_open_restriction R h2 (D f) (D f) (fun _=>True) (U f)
    (fun x (_:True)=>@norm_full_domain_interior R (R_n R (D f))
      (inner_norm (@euclidean_inner_productP R (D f))) x)
    (hU f) (fun x _=>@scalar_rectangle_domain_whole R f x)
    (@current_degree_transport R h2 (D f) (U f) (hU f) (size (Factors f)) (D f)
      (@scalar_rectangle_current_degree f) (P f))=
    @euclidean_fundamental_restricted_current R h2 (D f) (Box f) (hBox f).
Proof.
move=>hOrdered.
rewrite (scalar_rectangle_box_current hOrdered) open_euclidean_characteristic_restriction
  open_euclidean_characteristic_current_full.
exact:euclidean_characteristic_current_restriction.
Qed.
End ScalarRectangleBoxCurrent.
