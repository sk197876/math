(** Federer (1969), 3.4.5, p. 321: the
    component family is specified intrinsically by maximal
    nonempty irreducible germs contained in the original germ. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP SetGermOrder AnalyticIrreducibleGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_maximal_irreducible_germ_in]: the
    maximal irreducible germs contained in alpha, called
    its irreducible components, 3.4.5, p. 321.
    Nonemptiness makes the empty original germ's component
    family empty and matches proper prime ideals. *)
Definition is_maximal_irreducible_germ_in (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  @is_nonempty_irreducible_analytic_germ R X NX hNX a beta /\set_germ_subset beta alpha /\
  forall gamma,@is_nonempty_irreducible_analytic_germ R X NX hNX a gamma ->
    set_germ_subset gamma alpha ->set_germ_subset beta gamma ->set_germ_subset gamma beta.

(** Source for [is_irreducible_component_family]: the
    original irreducible component family is characterized
    by maximality, before existence and finiteness are proved,
    3.4.5, p. 321. *)
Record is_irreducible_component_family (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (C:set (@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)):Prop:={
  (** Source for [irreducible_component_membership]: original
      membership is exactly maximal irreducible containment,
      3.4.5, p. 321. Finiteness and union identity
      are conclusions to prove, not fields assumed here. *)
  irreducible_component_membership:forall beta,C beta <->
    @is_maximal_irreducible_germ_in R X NX hNX a alpha beta
}.
