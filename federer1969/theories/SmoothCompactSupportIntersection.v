(** Federer (1969), 4.1.12, pp. 367–368: the
    compact index K intersect spt gamma is the
    literal original intersection. K lies in U,
    so intersection with relative support is intersection
    with a closed subset of the original source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SmoothCompactSet SmoothFunctionSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothCompactSupportIntersection.
Variable R:realType.
Variables X Y E:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable U:set X.
Variable ev:E->X->Y.

(** Source for [smooth_compact_support_intersection]:
    the original K intersect spt gamma is a
    compact subset of U, supporting the multiplier
    estimate and flat-chain closure in Federer 4.1.12,
    pp. 367–368. The support remains relative to U. *)
Definition smooth_compact_support_intersection (K:smooth_compact_set hNX U) (gamma:E):
    smooth_compact_set hNX U.
Proof.
refine (@Build_smooth_compact_set R X NX hNX U
  (smooth_compact_carrier K `&` @smooth_function_support R X Y NX hNX U E ev gamma) _ _).
- move=>x [hx _];exact:smooth_compact_in_domain K x hx.
- pose T:=real_norm_metric_space hNX.
  have hSet:[set x:T|smooth_compact_carrier K x /\
      @smooth_function_support R X Y NX hNX U E ev gamma x]=
      [set x:T|smooth_compact_carrier K x] `&` closure [set x:T|ev gamma x<>0].
    apply:funext=>x;apply:propext;split.
    + move=>[hx [_ hClosure]];by split.
    + move=>[hx hClosure];split;first exact:hx.
      split;last exact:hClosure.
      exact:smooth_compact_in_domain K x hx.
  rewrite hSet;exact:compact_closedI (smooth_compact_is_compact K) (@closed_closure T _).
Defined.

(** Source for [smooth_compact_support_intersection_carrier]:
    the compact descriptor has precisely the literal
    set K intersect spt gamma, as used in
    Federer 4.1.12, pp. 367–368. Consumers use
    this public identity rather than the descriptor's
    compactness construction. *)
Lemma smooth_compact_support_intersection_carrier (K:smooth_compact_set hNX U) (gamma:E):
  smooth_compact_carrier (smooth_compact_support_intersection K gamma)=
    smooth_compact_carrier K `&` @smooth_function_support R X Y NX hNX U E ev gamma.
Proof. by []. Qed.
End SmoothCompactSupportIntersection.
