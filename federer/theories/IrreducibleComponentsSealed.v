(** Federer (1969), 3.4.5, p. 321: opaque
    intrinsic irreducible component families. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP IrreducibleComponentsUP IrreducibleComponentsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type IrreducibleComponentsSignature.
(** Source for [value]: the original maximal irreducible
    component family, 3.4.5, p. 321. *)
Parameter value:forall (R:realType) (X:lmodType R) (NX:X->R)
  (hNX:is_real_norm NX) (a:X),
  @set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a->
    set (@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a).
(** Source for [laws]: exact intrinsic maximality,
    3.4.5, p. 321. Finiteness is a theorem. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R)
  (hNX:is_real_norm NX) (a:X) alpha,
  @is_irreducible_component_family R X NX hNX a alpha (@value R X NX hNX a alpha).
End IrreducibleComponentsSignature.
Module IrreducibleComponents:IrreducibleComponentsSignature.
(** Source for [value]: private witness after proved
    unique existence, 3.4.5, p. 321. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (a:X) alpha:=
  projT1 (cid (@irreducible_component_family_exists R X NX hNX a alpha)).
(** Source for [laws]: the witness satisfies the
    independent maximality specification, 3.4.5, p. 321. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R)
    (hNX:is_real_norm NX) (a:X) alpha:
  @is_irreducible_component_family R X NX hNX a alpha (@value R X NX hNX a alpha).
Proof. exact:(projT2 (cid (@irreducible_component_family_exists R X NX hNX a alpha))). Qed.
End IrreducibleComponents.
