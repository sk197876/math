(** Opaque exact relative differential of Federer (1969),
    3.1.22, p. 235. The witness is hidden; downstream
    proofs use only the exact partial graph specification. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP PartialFunctionUP RelativeDifferentialUP RelativeDifferentialConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type RELATIVE_NORM_DIFFERENTIAL.
(** Source for [value]: Df(a) relative to S in Federer
    3.1.22, p. 235, as an exact partial function
    whose values have precisely the tangent cone as domain. *)
Parameter value : forall (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (A S:X->Prop) (f:X->Y),partial_function X (partial_function X Y).
(** Source for [laws]: the exact relative-differentiability
    graph of Df(a), Federer 3.1.22, p. 235.
    This law must be proved by the implementation. *)
Parameter laws : forall (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (A S:X->Prop) (f:X->Y),
  @is_relative_norm_differential_graph R X Y NX NY hNX A S f
    (@value R X Y NX NY hNX hNY A S f).
End RELATIVE_NORM_DIFFERENTIAL.

Module RelativeNormDifferential : RELATIVE_NORM_DIFFERENTIAL.
(** Source for [value]: select the proved exact partial graph
    of relative differentials in Federer 3.1.22, p. 235;
    the selection is hidden by opaque module ascription. *)
Definition value (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:X->Prop) (f:X->Y) :=
  projT1 (cid (@relative_norm_differential_graph_exists R X Y NX NY hNX hNY A S f)).
(** Source for [laws]: the selected graph satisfies the
    defining relative-differentiability law, Federer 3.1.22, p. 235. *)
Lemma laws (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:X->Prop) (f:X->Y) :
  @is_relative_norm_differential_graph R X Y NX NY hNX A S f
    (@value R X Y NX NY hNX hNY A S f).
Proof.
exact (projT2 (cid (@relative_norm_differential_graph_exists R X Y NX NY hNX hNY A S f))).
Qed.
End RelativeNormDifferential.
