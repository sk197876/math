(** Federer (1969), 3.2.1, p. 241: opaque partial Jacobians
    expose only their exact ordinary/approximate differential graph laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import GrassmannAbbreviations PartialFunctionUP JacobianUP JacobianConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type JACOBIANS.
(** Source for [value]: J_k f in Federer 3.2.1, p. 241,
    required together with its proved graph specification below. *)
Parameter value:forall (R:realType) (m n k:nat),
  (R_n R m->Prop)->(R_n R m->R_n R n)->partial_function (R_n R m) R.
(** Source for [approximate_value]: ap J_k f in Federer 3.2.1,
    p. 241, required together with its exact graph specification. *)
Parameter approximate_value:forall (R:realType) (m n k:nat),
  (R_n R m->Prop)->(R_n R m->R_n R n)->partial_function (R_n R m) R.
(** Source for [laws]: first display of Federer 3.2.1, p. 241.
    An implementation must prove this field from graph existence. *)
Parameter laws:forall (R:realType) (m n k:nat) (A:R_n R m->Prop) (f:R_n R m->R_n R n),
  is_euclidean_jacobian_graph k A f (@value R m n k A f).
(** Source for [approximate_laws]: second display of Federer
    3.2.1, p. 241; the implementation proves this field. *)
Parameter approximate_laws:forall (R:realType) (m n k:nat) (A:R_n R m->Prop) (f:R_n R m->R_n R n),
  is_approximate_jacobian_graph k A f (@approximate_value R m n k A f).
End JACOBIANS.
Module Jacobians:JACOBIANS.
(** Source for [value]: select a proved partial graph for
    J_k f, Federer 3.2.1, p. 241, hidden by the signature. *)
Definition value (R:realType) m n k (A:R_n R m->Prop) (f:R_n R m->R_n R n) :=
  projT1 (cid (@euclidean_jacobian_graph_exists R m n k A f)).
(** Source for [approximate_value]: select the proved approximate
    graph, Federer 3.2.1, p. 241, hidden by the signature. *)
Definition approximate_value (R:realType) m n k (A:R_n R m->Prop) (f:R_n R m->R_n R n) :=
  projT1 (cid (@approximate_jacobian_graph_exists R m n k A f)).
(** Source for [laws]: the selected graph satisfies exactly
    the first definition in Federer 3.2.1, p. 241. *)
Lemma laws (R:realType) m n k (A:R_n R m->Prop) (f:R_n R m->R_n R n) :
  is_euclidean_jacobian_graph k A f (@value R m n k A f).
Proof. exact (projT2 (cid (@euclidean_jacobian_graph_exists R m n k A f))). Qed.
(** Source for [approximate_laws]: the proved second definition
    in Federer 3.2.1, p. 241, for the chosen opaque graph. *)
Lemma approximate_laws (R:realType) m n k (A:R_n R m->Prop) (f:R_n R m->R_n R n) :
  is_approximate_jacobian_graph k A f (@approximate_value R m n k A f).
Proof. exact (projT2 (cid (@approximate_jacobian_graph_exists R m n k A f))). Qed.
End Jacobians.
