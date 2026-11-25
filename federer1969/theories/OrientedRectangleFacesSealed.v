(** Federer (1969), 4.1.8, p. 362: seal
    the original rectangular face family. The
    existence construction stays hidden; clients use
    its independent original ordered-product laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleFacesUP OrientedRectangleFacesExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type OrientedRectangleFacesSignature.
(** Source for [value]: the original face replacing
    segment k by delta_(u_k)-delta_(v_k),
    Federer 4.1.8, p. 362. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (f:seq (oriented_segment_factor R)),
  'I_(size f)->@oriented_rectangle_space R h2 f (size f).-1.
(** Source for [laws]: the original face-product
    specification in Federer 4.1.8, p. 362;
    no Stokes identity is assumed. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0),
  @is_oriented_rectangle_faces R h2 (fun f=>@value R h2 f).
End OrientedRectangleFacesSignature.
Module OrientedRectangleFaces:OrientedRectangleFacesSignature.
(** Source for [value]: hide the proved original
    face family, supporting Federer 4.1.8, p. 362. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (f:seq (oriented_segment_factor R))
    (k:'I_(size f)):@oriented_rectangle_space R h2 f (size f).-1:=
  projT1 (cid (@oriented_rectangle_faces_exists R h2)) f k.
(** Source for [laws]: the opaque original faces
    satisfy their independent product specification,
    supporting Federer 4.1.8, p. 362. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0):
  @is_oriented_rectangle_faces R h2 (fun f=>@value R h2 f).
Proof. exact:(projT2 (cid (@oriented_rectangle_faces_exists R h2))). Qed.
End OrientedRectangleFaces.
