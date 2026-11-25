(** Supporting finite linear topology for Federer (1969),
    3.1.21, p. 234: a linear range in a finite-dimensional
    normed target is closed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceSums LinearBasis RealNormUP NormMetric
  LinearRankUP FiniteNormSubspaceClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_norm_linear_range_closed]: supporting the
    closed range of Dpsi in the constant-rank local-image
    assertion of Federer 3.1.21, p. 234. A basis
    of the actual range is obtained by finite-dimensional linear
    algebra; no continuity hypothesis on the source is needed. *)
Lemma finite_norm_linear_range_closed (R:realType) (X Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) n (b:'I_n->Y) (hb:is_basis b) (L:Hom X Y) :
  @closed (real_norm_metric_space hNY) (range L).
Proof.
have [r [hr hrn]]:=linear_rank_exists L hb.
have he:range L=(range_subspace (hom_as_linear L):set Y).
  apply/seteqP; split=>y.
  - move=>[x _ hxy]; exists x; exact: esym hxy.
  - move=>[x hxy]; exists x; first exact I; exact: esym hxy.
rewrite he.
exact (@finite_norm_subspace_closed R Y NY hNY n b hb
  (range_subspace (hom_as_linear L)) r hr).
Qed.
