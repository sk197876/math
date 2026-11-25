(** Federer (1969), 2.3.2(2), p. 73: general order- topology background for
    the rational-ray measurability criterion. A countable order-dense family
    gives countably many interval neighborhoods, including unbounded
    endpoint neighborhoods. These are supporting topology facts, not
    additional assertions attributed to Federer. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope order_scope.
Local Open Scope classical_set_scope.

(** Source for [is_order_dense_family]: supporting abstract
    density condition for the rational-ray criterion in Federer
    2.3.2(2), p. 73. Every nonempty order interval contains
    a value of d. The family is not required to be injective. *)
Definition is_order_dense_family disp (T : orderType disp) (J : Type) (d : J -> T) :=
  forall a b, a < b -> exists j, a < d j /\ d j < b.

(** Source for [order_family_interval]: supporting interval
    neighborhood for Federer 2.3.2(2), p. 73. An absent
    endpoint imposes no bound, so infinite endpoints remain covered. *)
Definition order_family_interval disp (T : orderType disp) (J : Type)
    (d : J -> T) (c : option J * option J) : set T :=
  [set x | (if c.1 is Some j then d j < x else True) /\
           (if c.2 is Some j then x < d j else True)].

(** Source for [order_family_intervals_refine]: supporting order-
    topology basis fact for Federer 2.3.2(2), p. 73.
    Density refines both finite bounds; missing bounds are preserved. *)
Lemma order_family_intervals_refine disp (T : orderTopologicalType disp)
    (J : Type) (d : J -> T) : is_order_dense_family d ->
  forall V, open V -> forall x, V x -> exists c,
    order_family_interval d c x /\ order_family_interval d c `<=` V.
Proof.
move=> hd V ho x hx.
have hn : nbhs x V by rewrite openE in ho; exact: ho x hx.
rewrite itv_nbhsE in hn; have [it [hoi hxi] hiV] := hn.
case: it hoi hxi hiV=> [[[] a|[]]] [[] b|[]] //= _ hxi hiV; rewrite interval.in_itv /= ?andbT in hxi.
- have /andP[hax hxb] := hxi.
  have [i [hai hix]] := hd a x hax.
  have [j [hxj hjb]] := hd x b hxb.
  exists (Some i,Some j); split; first by split.
  move=> y [hiy hyj]; apply: hiV; rewrite /= interval.in_itv /= ?andbT.
  apply/andP; split; [exact: lt_trans hai hiy|exact: lt_trans hyj hjb].
- have [i [hai hix]] := hd a x hxi.
  exists (Some i,None); split; first by split.
  move=> y [hiy _]; apply: hiV; rewrite /= interval.in_itv /= ?andbT; exact: lt_trans hai hiy.
- have [j [hxj hjb]] := hd x b hxi.
  exists (None,Some j); split; first by split.
  move=> y [_ hyj]; apply: hiV; rewrite /= interval.in_itv /= ?andbT; exact: lt_trans hyj hjb.
- exists (None,None); split; first by split.
  move=> y _; apply: hiV; by rewrite /= interval.in_itv.
Qed.

(** Source for [order_strict_lower_ray_open]: supporting open
    order ray for Federer 2.3.2(2), p. 73. *)
Lemma order_strict_lower_ray_open disp (Y : orderTopologicalType disp) (t : Y) :
  open [set y | y < t].
Proof. exact: lray_open. Qed.

(** Source for [order_strict_upper_ray_open]: supporting open
    upper order ray for Federer 2.3.2(2), p. 73. *)
Lemma order_strict_upper_ray_open disp (Y : orderTopologicalType disp) (t : Y) :
  open [set y | t < y].
Proof.
have he : [set y | t < y] = `]t,+oo[%classic.
  by apply/seteqP; split=> y; rewrite /= interval.in_itv /= andbT.
rewrite he; exact: rray_open.
Qed.

(** Source for [order_closed_lower_ray_closed]: supporting closed
    lower order ray for Federer 2.3.2(2), p. 73. *)
Lemma order_closed_lower_ray_closed disp (Y : orderTopologicalType disp) (t : Y) :
  closed [set y | y <= t].
Proof. exact: lray_closed. Qed.

(** Source for [order_closed_upper_ray_closed]: supporting closed
    upper order ray for Federer 2.3.2(2), p. 73. *)
Lemma order_closed_upper_ray_closed disp (Y : orderTopologicalType disp) (t : Y) :
  closed [set y | t <= y].
Proof.
have he : [set y | t <= y] = `[t,+oo[%classic.
  by apply/seteqP; split=> y; rewrite /= interval.in_itv /= andbT.
rewrite he; exact: rray_closed.
Qed.
