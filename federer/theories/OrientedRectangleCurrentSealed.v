(** Federer (1969), 4.1.8, p. 362: hide
    the existence witness for the original finite
    oriented rectangular current. Consumers use only
    the independently specified finite-product laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  OrientedRectangleCurrentUP OrientedRectangleCurrentExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type OrientedRectangleCurrentSignature.
(** Source for [value]: the original ordered product
    [u_1,v_1] times ... times [u_nu,v_nu],
    Federer 4.1.8, p. 362. *)
Parameter value:forall (R:realType) (h2:(1+1:R)!=0) (f:seq (oriented_segment_factor R)),
  @oriented_rectangle_space R h2 f (size f).
(** Source for [laws]: the original empty, singleton
    and nonempty attachment laws, supporting the
    finite-product induction in Federer 4.1.8,
    p. 362. No boundary conclusion is postulated. *)
Parameter laws:forall (R:realType) (h2:(1+1:R)!=0),
  @is_oriented_rectangle_current R h2 (fun f=>@value R h2 f).
End OrientedRectangleCurrentSignature.
Module OrientedRectangleCurrent:OrientedRectangleCurrentSignature.
(** Source for [value]: seal only the proved
    original finite-product witness, supporting Federer
    4.1.8, p. 362. *)
Definition value (R:realType) (h2:(1+1:R)!=0) (f:seq (oriented_segment_factor R)):
    @oriented_rectangle_space R h2 f (size f):=
  projT1 (cid (@oriented_rectangle_current_exists R h2)) f.
(** Source for [laws]: the opaque product satisfies
    its original independent specification, supporting
    Federer 4.1.8, p. 362. *)
Lemma laws (R:realType) (h2:(1+1:R)!=0):
  @is_oriented_rectangle_current R h2 (fun f=>@value R h2 f).
Proof. exact:(projT2 (cid (@oriented_rectangle_current_exists R h2))). Qed.
End OrientedRectangleCurrent.
