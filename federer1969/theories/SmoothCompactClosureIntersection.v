(** Federer (1969), 4.1.12, p. 368: the
    localisation index is exactly K intersect Clos Z.
    A closed intersection of the original compact K
    is again an allowed compact subset of U. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Section SmoothCompactClosureIntersection.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable U:set X.

(** Source for [smooth_compact_closure_intersection]:
    the literal compact index K intersect Clos Z
    used in Federer 4.1.12, p. 368.
    The descriptor records the original set and
    its previously proved closed-intersection compactness. *)
Definition smooth_compact_closure_intersection (K:smooth_compact_set hNX U) (Z:set X):
    smooth_compact_set hNX U.
Proof.
refine (@Build_smooth_compact_set R X NX hNX U
  (smooth_compact_carrier K `&` @closure (real_norm_metric_space hNX) Z) _ _).
- move=>x [hx _];exact:smooth_compact_in_domain K x hx.
- exact:compact_closedI (smooth_compact_is_compact K) (@closed_closure (real_norm_metric_space hNX) Z).
Defined.

(** Source for [smooth_compact_closure_intersection_carrier]:
    the descriptor retains exactly K intersect Clos Z,
    with no enlargement, Federer 4.1.12, p. 368. *)
Lemma smooth_compact_closure_intersection_carrier (K:smooth_compact_set hNX U) (Z:set X):
  smooth_compact_carrier (smooth_compact_closure_intersection K Z)=
    smooth_compact_carrier K `&` @closure (real_norm_metric_space hNX) Z.
Proof. by []. Qed.
End SmoothCompactClosureIntersection.
