(** Federer (1969), 3.3.19, p. 302: independent
    meaning of a minimum distance between the distinct
    members of an original finite family of closed discs. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets topology.
From Federer Require Import MetricClosedBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_disc_level_minimum_gap]: all original
    distinct discs have every point-pair distance at least d,
    and some original pair attains d, interpreting the
    second displayed minimum in 3.3.19, p. 302.
    Neither existence nor the printed value is postulated. *)
Definition is_disc_level_minimum_gap (R:realType) (X:metricType R)
    (H:{fset X}) (r d:R):Prop:=
  (forall z w:X,z \in H ->w \in H ->z!=w ->
    forall x y:X,metric_closed_ball z r x ->metric_closed_ball w r y ->d<=mdist x y) /\
  exists z w:X,z \in H /\w \in H /\z!=w /\
    exists x y:X,metric_closed_ball z r x /\metric_closed_ball w r y /\mdist x y=d.

(** Source for [disc_level_minimum_gap_unique]: uniqueness
    of the actual scalar minimum between original discs,
    supporting 3.3.19, p. 302. *)
Lemma disc_level_minimum_gap_unique (R:realType) (X:metricType R)
    (H:{fset X}) (r d e:R):
  is_disc_level_minimum_gap H r d ->is_disc_level_minimum_gap H r e ->d=e.
Proof.
move=>[hD [z [w [hz [hw [hZW [x [y [hx [hy hXY]]]]]]]]]]
  [hE [a [b [ha [hb [hAB [u [v [hu [hv hUV]]]]]]]]]].
apply/eqP;rewrite eq_le;apply/andP;split.
- have hh:=hD a b ha hb hAB u v hu hv;by rewrite hUV in hh.
- have hh:=hE z w hz hw hZW x y hx hy;by rewrite hXY in hh.
Qed.
