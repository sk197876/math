(** Federer (1969), 3.4.2(4), pp. 310–311: existence and uniqueness of
    the oscillation suprema from the project's abstract supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations RealNormUP
  ExtendedSupremumUP ExtendedSupremumSealed CriticalOscillationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_function_oscillation_exists]: the η supremum
    in 3.4.2(4), pp. 310–311, exists because its real value set contains
    zero. The existing opaque supremum supplies the witness. *)
Theorem critical_function_oscillation_exists (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) (lambda delta:R):
  exists v,is_critical_function_oscillation NY Z S C f lambda delta v.
Proof.
have hn:critical_function_oscillation_values NY Z S C f lambda delta !=set0.
  by exists 0;left.
exists (ExtendedSupremum.value hn);exact:ExtendedSupremum.laws.
Qed.

(** Source for [critical_tangent_oscillation_exists]: the ζ supremum
    in 3.4.2(4), p. 311, exists by the same nonempty real-supremum law.
    Its value set retains the genuine relative differential graphs. *)
Theorem critical_tangent_oscillation_exists (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) (f:R_n R m->Y) (lambda delta:R):
  exists v,is_critical_tangent_oscillation hNY Z S C f lambda delta v.
Proof.
have hn:critical_tangent_oscillation_values hNY Z S C f lambda delta !=set0.
  by exists 0;left.
exists (ExtendedSupremum.value hn);exact:ExtendedSupremum.laws.
Qed.

(** Source for [critical_function_oscillation_unique]: the η supremum
    in 3.4.2(4), pp. 310–311, is unique by its least-upper-bound laws. *)
Lemma critical_function_oscillation_unique (R:realType) m (Y:lmodType R)
    (NY:Y->R) (Z:subspace (R_n R m)) (S C:set (R_n R m))
    (f:R_n R m->Y) (lambda delta:R) v w:
  is_critical_function_oscillation NY Z S C f lambda delta v ->
  is_critical_function_oscillation NY Z S C f lambda delta w ->v=w.
Proof. exact:extended_supremum_unique. Qed.

(** Source for [critical_tangent_oscillation_unique]: the ζ supremum
    in 3.4.2(4), p. 311, is unique by its least-upper-bound laws. *)
Lemma critical_tangent_oscillation_unique (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) (Z:subspace (R_n R m))
    (S C:set (R_n R m)) (f:R_n R m->Y) (lambda delta:R) v w:
  is_critical_tangent_oscillation hNY Z S C f lambda delta v ->
  is_critical_tangent_oscillation hNY Z S C f lambda delta w ->v=w.
Proof. exact:extended_supremum_unique. Qed.
