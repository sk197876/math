(** Federer (1969), 3.4.5, p. 321: finite
    irreducible covers specified by the original union and
    actual nonempty irreducibility of every member. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP SetGermFiniteUnion AnalyticIrreducibleGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_finite_irreducible_germ_cover]: the
    finite irreducible decomposition preceding the maximality
    and uniqueness assertions in 3.4.5, p. 321.
    The empty germ has the empty cover; lists may
    repeat members until the maximal component set is formed. *)
Record is_finite_irreducible_germ_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (F:seq (@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)):Prop:={
  (** Source for [irreducible_germ_cover_members]: every
      actual member is nonempty and irreducible, supporting
      unique components in 3.4.5, p. 321. *)
  irreducible_germ_cover_members:forall beta,beta \in F ->
    @is_nonempty_irreducible_analytic_germ R X NX hNX a beta;
  (** Source for [irreducible_germ_cover_union]: the original
      germ is exactly their finite union, 3.4.5, p. 321. *)
  irreducible_germ_cover_union:@set_germ_finite_union
    (Topological.clone (real_norm_metric_space hNX) _) a F=alpha
}.
