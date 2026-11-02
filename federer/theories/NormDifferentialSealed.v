(** Opaque interface for Df in Federer (1969), 3.1.1, p. 209.
    Only the partial graph and its exact approximation laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP PartialFunctionUP
  NormDifferentialUP NormDifferentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type NormDifferentialSignature.
(** Source for [value]: abstract partial differential Df from
    Federer 3.1.1, p. 209. *)
Parameter value : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R), is_real_norm NX -> is_real_norm NY ->
  (X -> Prop) -> (X -> Y) -> partial_function X (Hom X Y).
(** Source for [laws]: exact graph specification for Df in
    Federer 3.1.1, p. 209. *)
Parameter laws : forall (R : realType) (X Y : lmodType R)
  (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
  (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y),
  is_norm_differential_graph NX NY A f (@value R X Y NX NY hNX hNY A f).
End NormDifferentialSignature.

Module NormDifferential : NormDifferentialSignature.
(** Source for [value]: private witness selection for the graph of
    Federer 3.1.1, p. 209, from its proved existence. *)
Definition value (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) :=
  projT1 (cid (norm_differential_graph_exists hNX hNY A f)).
(** Source for [laws]: the selected differential graph satisfies
    precisely the laws in Federer 3.1.1, p. 209. *)
Lemma laws (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y) :
  is_norm_differential_graph NX NY A f (@value R X Y NX NY hNX hNY A f).
Proof. exact: projT2 (cid (norm_differential_graph_exists hNX hNY A f)). Qed.
End NormDifferential.
