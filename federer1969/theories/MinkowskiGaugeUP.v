(** Federer (1969), 3.2.35, p. 271:
    g(x) is the infimum of the positive t
    for which x/t belongs to the original
    open convex body. These laws precede any
    construction or selection of a gauge function. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_minkowski_gauge]: the defining
    infimum in the proof of Federer 3.2.35,
    p. 271, specified by its lower-bound and
    greatest-lower-bound laws. The supporting interface
    permits any absorbing set in a real vector
    space. Openness, convexity and boundedness are
    hypotheses of the relevant consequences, rather
    than hidden parts of this infimum definition. *)
Record is_minkowski_gauge (R:realType) (V:lmodType R)
    (S:set V) (g:V->R):Prop:={
  minkowski_gauge_lower:forall x t,0<t ->S (t^-1*:x) ->g x<=t;
  minkowski_gauge_greatest:forall x c,
    (forall t:R,0<t ->S (t^-1*:x) ->c<=t) ->c<=g x
}.
