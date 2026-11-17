(** Federer (1969), 3.4.12, p. 339:
    irreducibility of the original holomorphic variety germs.
    Keep the printed union test separate from the nonempty
    convention needed when a prime ideal must be proper. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP ScalarRestriction ComplexScalarSealed NormMetric SetGermUP SetGermSealed HolomorphicVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_union_irreducible_holomorphic_germ]: the
    literal no-proper-two-piece decomposition test printed in
    3.4.12, p. 339. It also holds for
    the empty germ; this edge is not silently excluded. *)
Definition is_union_irreducible_holomorphic_germ (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  @is_holomorphic_variety_germ R X NX hNX a alpha /\
  forall beta gamma,@is_holomorphic_variety_germ R X NX hNX a beta ->
    @is_holomorphic_variety_germ R X NX hNX a gamma ->
    alpha=@SetGerms.join (Topological.clone (real_norm_metric_space hNX) _) a beta gamma ->
    alpha=beta \/alpha=gamma.

(** Source for [is_nonempty_irreducible_holomorphic_germ]: the
    nonempty convention corresponding to proper prime ideals
    and unique nonempty components in 3.4.12, p. 339.
    The literal printed union predicate remains separately available. *)
Definition is_nonempty_irreducible_holomorphic_germ (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:restricted_space (ComplexScalars.embed R) X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  @is_union_irreducible_holomorphic_germ R X NX hNX a alpha /\
  alpha<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0.
