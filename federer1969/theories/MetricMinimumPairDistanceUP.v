(** Federer (1969), 3.3.19, p. 302: independent
    meaning of an attained minimum distance between two
    nonempty original sets. No minimizer is globally chosen. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_minimum_pair_distance]: the
    lower-bound and attained-value meaning of the minimum
    distance between the original discs, 3.3.19, p. 302. *)
Definition is_metric_minimum_pair_distance (R:realType) (X:metricType R)
    (A B:set X) (d:R):Prop:=
  (forall x y,A x ->B y ->d<=mdist x y) /\
  exists x y,A x /\B y /\mdist x y=d.

(** Source for [metric_minimum_pair_distance_unique]:
    uniqueness of the scalar minimum supporting the literal
    distance formula of 3.3.19, p. 302. *)
Lemma metric_minimum_pair_distance_unique (R:realType) (X:metricType R)
    (A B:set X) (d e:R):
  is_metric_minimum_pair_distance A B d ->is_metric_minimum_pair_distance A B e ->d=e.
Proof.
move=>[hD [x [y [hx [hy hxy]]]]] [hE [u [v [hu [hv huv]]]]].
apply/eqP;rewrite eq_le;apply/andP;split.
- have hh:=hD u v hu hv;by rewrite huv in hh.
- have hh:=hE x y hx hy;by rewrite hxy in hh.
Qed.
