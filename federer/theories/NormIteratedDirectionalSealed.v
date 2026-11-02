(** Opaque recursive partial-derivative graph, Federer (1969),
    3.1.11, p. 223. The construction remains private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP PartialFunctionUP NormIteratedDirectionalGraphUP
  NormIteratedDirectionalConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type NormIteratedDirectionalSignature.
(** Source for [value]: the exact partial ordered derivative
    used for D_nu f in Federer 3.1.11, p. 223. *)
Parameter value : forall (R : realType) (X Y : lmodType R)
  (NY : Y->R) (hNY : is_real_norm NY) (A : X->Prop) (f : X->Y) (s : seq X),
  partial_function X Y.
(** Source for [laws]: the recursive limits characterize the
    graph exactly, Federer 3.1.11, p. 223. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NY : Y->R) (hNY : is_real_norm NY) (A : X->Prop) (f : X->Y) (s : seq X),
  is_norm_iterated_directional_graph NY A f s (@value R X Y NY hNY A f s).
End NormIteratedDirectionalSignature.

Module NormIteratedDirectional : NormIteratedDirectionalSignature.
(** Source for [value]: the proved exact graph witness for
    Federer 3.1.11, p. 223, hidden by opaque ascription. *)
Definition value (R : realType) (X Y : lmodType R)
  (NY : Y->R) (hNY : is_real_norm NY) (A : X->Prop) (f : X->Y) (s : seq X) :=
  projT1 (cid (@norm_iterated_directional_graph_exists R X Y NY hNY A f s)).
(** Source for [laws]: the witness satisfies its entire
    recursive specification, Federer 3.1.11, p. 223. *)
Lemma laws (R : realType) (X Y : lmodType R)
  (NY : Y->R) (hNY : is_real_norm NY) (A : X->Prop) (f : X->Y) (s : seq X) :
  is_norm_iterated_directional_graph NY A f s (@value R X Y NY hNY A f s).
Proof. exact: projT2 (cid (@norm_iterated_directional_graph_exists R X Y NY hNY A f s)). Qed.
End NormIteratedDirectional.
