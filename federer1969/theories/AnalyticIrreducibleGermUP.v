(** Federer (1969), 3.4.5, pp. 320–321:
    irreducibility of the original analytic variety germs.
    Keep the printed union test separate from the nonempty
    convention needed when a prime ideal must be proper. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP SetGermSealed AnalyticVarietyGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_union_irreducible_analytic_germ]: the
    literal no-proper-two-piece decomposition test printed in
    3.4.5, p. 320. It also holds for
    the empty germ; this edge is not silently excluded. *)
Definition is_union_irreducible_analytic_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  @is_analytic_variety_germ R X NX hNX a alpha /\
  forall beta gamma,@is_analytic_variety_germ R X NX hNX a beta ->
    @is_analytic_variety_germ R X NX hNX a gamma ->
    alpha=@SetGerms.join (Topological.clone (real_norm_metric_space hNX) _) a beta gamma ->
    alpha=beta \/alpha=gamma.

(** Source for [is_nonempty_irreducible_analytic_germ]: the
    nonempty convention corresponding to proper prime ideals
    and unique nonempty components in 3.4.5, pp. 320–321.
    The literal printed union predicate remains separately available. *)
Definition is_nonempty_irreducible_analytic_germ (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a):=
  @is_union_irreducible_analytic_germ R X NX hNX a alpha /\
  alpha<>@set_germ (Topological.clone (real_norm_metric_space hNX) _) a set0.
