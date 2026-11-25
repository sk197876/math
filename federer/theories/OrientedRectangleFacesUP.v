(** Federer (1969), 4.1.8, p. 362: the
    original faces replace exactly one segment by
    delta_(u_k)-delta_(v_k). Specify their original
    ordered-product recurrence independently of Stokes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedRectangleFacesUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).
Local Notation Face := (fun f=>@oriented_rectangle_space R h2 f (size f).-1).
Local Notation Product := (@oriented_rectangle_product R h2).
Local Notation P := (@OrientedRectangleCurrent.value R h2).
Local Notation S := (@oriented_segment_factor_current R h2).
Local Notation Delta := (@oriented_segment_factor_endpoint_difference R h2).

(** Source for [is_oriented_rectangle_faces]: the original
    k-th face is the ordered product with only
    its k-th segment replaced by delta_u-delta_v,
    supporting the Stokes display in Federer 4.1.8,
    p. 362. Indices here start at zero; the
    printed index is their successor. No boundary
    identity or sign assertion is assumed. *)
Definition is_oriented_rectangle_faces (F:forall f:seq Factor,'I_(size f)->Face f):Prop:=
  (forall a k,F [::a] k=Delta a) /\
  (forall a b t,F (a::b::t) ord0=Product a b t 0%N (size (b::t)) (Delta a) (P (b::t))) /\
  (forall a b t (k:'I_(size (b::t))),F (a::b::t) (lift ord0 k)=
    Product a b t 1%N (size (b::t)).-1 (S a) (F (b::t) k)).
End OrientedRectangleFacesUP.
