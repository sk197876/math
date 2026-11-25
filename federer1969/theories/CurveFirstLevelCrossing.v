(** Supporting Federer (1969), 2.10.14, p. 177: a distance image of an
    arbitrary curve can miss intermediate levels only across one-sided
    jumps. The infimum of the times above a level supplies its first
    crossing, without continuity of the real function. This expands a proof
    route for the otherwise unproved printed generalisation; it is not a
    separately stated book theorem. The infimum facts are real-order
    background for 2.1.1, p. 51. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_first_curve_level_crossing]: supporting first-
    crossing laws for the distance-image argument in 2.10.14,
    p. 177. The value need not be above the level at x:
    every interval to its right merely contains a crossing time. *)
Definition is_first_curve_level_crossing (R : realType) (f : R -> R)
    (a b y x : R) :=
  a<=x<=b /\ (forall t, a<=t -> t<x -> f t<=y) /\
  forall d : R, 0<d -> exists t, x<=t<=b /\ t<x+d /\ y<f t.

(** Source for [first_curve_level_crossing_exists]: proved first-
    crossing witness supporting the jump formula of 2.10.14,
    p. 177. A nonempty bounded real set has an infimum;
    no one-sided limit or continuity of f is assumed. *)
Theorem first_curve_level_crossing_exists (R : realType) (f : R -> R)
    (a b y : R) : a<=b -> y<f b ->
  exists x, is_first_curve_level_crossing f a b y x.
Proof.
move=> hab hyb.
pose E := [set t : R | a<=t<=b /\ y<f t].
have hEb : E b by split=> //; rewrite hab lexx.
have hne : E !=set0 by exists b.
have hlower : lbound E a by move=> t [/andP[hat _] _].
have hbnd : has_lbound E by exists a.
have hi : has_inf E by split.
pose x := inf E.
have hax : a<=x := lb_le_inf hne hlower.
have hxb : x<=b := ge_inf hbnd hEb.
exists x; split; first by rewrite hax hxb.
split.
- move=> t hat htx; rewrite leNgt; apply/negP=> hyt.
  have htE : E t by split=> //; rewrite hat (le_trans (ltW htx) hxb).
  have hxt : x<=t := ge_inf hbnd htE.
  by move: htx; rewrite ltNge hxt.
- move=> d hd; have [t htE htx] := inf_adherent hd hi.
  have hxt : x<=t := ge_inf hbnd htE.
  exists t; split; first by have [/andP[_ htb] _] := htE; rewrite hxt htb.
  split; first exact htx.
  exact htE.2.
Qed.
