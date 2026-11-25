(** Federer (1969), 4.1.11, p. 366: the opaque
    original prism vertex families. The public laws give
    exactly their lower and upper ordered vertex ranges;
    existence is proved before sealing the witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CurrentPrismVerticesUP CurrentPrismVerticesExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CurrentPrismVerticesSignature.
(** Source for [value]: the original kth ordered
    prism simplex vertex family, Federer 4.1.11, p. 366. *)
Parameter value:forall (X Y:Type) (A B:X->Y) m,
  ('I_(m.+1)->X)->'I_(m.+1)->'I_(m.+2)->Y.
(** Source for [laws]: the original lower A range
    and upper B range, Federer 4.1.11, p. 366.
    No assertion about currents or their boundaries is assumed. *)
Parameter laws:forall (X Y:Type) (A B:X->Y),
  is_current_prism_vertices A B (@value X Y A B).
End CurrentPrismVerticesSignature.
Module CurrentPrismVertices:CurrentPrismVerticesSignature.
(** Source for [family]: a private witness of the
    independent original ordered vertex laws, supporting
    Federer 4.1.11, p. 366. It is hidden by the signature. *)
Definition family (X Y:Type) (A B:X->Y):
    forall m,('I_(m.+1)->X)->'I_(m.+1)->'I_(m.+2)->Y:=
  projT1 (cid (@current_prism_vertices_exists X Y A B)).
(** Source for [value]: seal the proved original
    vertex witness, Federer 4.1.11, p. 366. *)
Definition value (X Y:Type) (A B:X->Y) m (v:'I_(m.+1)->X)
    (k:'I_(m.+1)):'I_(m.+2)->Y:=@family X Y A B m v k.
(** Source for [laws]: the opaque vertex family satisfies
    exactly its independently specified original ranges,
    supporting Federer 4.1.11, p. 366. *)
Lemma laws (X Y:Type) (A B:X->Y):
  is_current_prism_vertices A B (@value X Y A B).
Proof. exact:(projT2 (cid (@current_prism_vertices_exists X Y A B))). Qed.
End CurrentPrismVertices.
