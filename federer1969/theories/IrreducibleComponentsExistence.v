(** Federer (1969), 3.4.5, p. 321: the
    intrinsic maximal-component specification determines a unique
    family. Finiteness and the union identity are proved
    separately under the original Noetherian hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP IrreducibleComponentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [irreducible_component_family_exists]: the
    family characterized by maximal irreducible containment
    exists, supporting 3.4.5, p. 321. *)
Theorem irreducible_component_family_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):
  exists C,@is_irreducible_component_family R X NX hNX a alpha C.
Proof.
exists (@is_maximal_irreducible_germ_in R X NX hNX a alpha);constructor=>beta;by split.
Qed.

(** Source for [irreducible_component_family_unique]: the
    intrinsic original maximality law determines the component
    family uniquely, 3.4.5, p. 321. *)
Lemma irreducible_component_family_unique (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) alpha C D:
  @is_irreducible_component_family R X NX hNX a alpha C ->
  @is_irreducible_component_family R X NX hNX a alpha D ->C=D.
Proof.
move=>hC hD;apply/seteqP;split=>beta.
- by rewrite (irreducible_component_membership hC beta) (irreducible_component_membership hD beta).
- by rewrite (irreducible_component_membership hC beta) (irreducible_component_membership hD beta).
Qed.
