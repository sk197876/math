(** Federer (1969), 2.5.20, p. 114: support of the product tests used to
    infer the fibre support inclusion. This extracts the support containment
    underlying the separated-product arrow of 2.6.4, p. 119. Source context:
    CompactFunctionSpaceUP.v. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [separated_function_support_subset]: the
    support of f(x)g(y) lies in spt f times spt g,
    supporting the disintegration support inference in Federer
    2.5.20, p. 114. Compactness is unnecessary for
    this elementary support containment. *)
Lemma separated_function_support_subset (R : realType) (X Y : topologicalType)
    (f : X -> R) (g : Y -> R) :
  real_function_support (fun p : X*Y => f p.1*g p.2) `<=`
    real_function_support f `*` real_function_support g.
Proof.
apply: real_function_support_in_closed_set.
- apply: closedI.
  + exact ((continuous_closedP (@fst X Y)).1 (@first_projection_continuous X Y) _ (@real_function_support_closed R X f)).
  + exact ((continuous_closedP (@snd X Y)).1 (@second_projection_continuous X Y) _ (@real_function_support_closed R Y g)).
- move=> [x y] hnot; case: (pselect (real_function_support f x))=> hx.
  + have hy : ~real_function_support g y by move=> hy; apply: hnot; split.
    by rewrite (real_function_zero_off_support hy) mulr0.
  + by rewrite (real_function_zero_off_support hx) mul0r.
Qed.
