(** Federer (1969), 3.3.19, p. 302: the auxiliary
    original unit root does not change A. The full-index
    abstract specification equals the literal intersection
    over the book's G_4,G_5,... alone. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets.
From Federer Require Import EuclideanInnerProduct InnerMetric CircularDiscTreeUP
  CircularDiscLimitUP CircularDiscTreeTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [circular_disc_limit_original_levels]:
    exact original A=intersection union G_n for n>=4,
    3.3.19, p. 302. The proved actual child containment
    discharges the extra auxiliary root automatically. *)
Theorem circular_disc_limit_original_levels (R:realType)
    (H:nat->{fset inner_metric_space (@euclidean_inner_productP R 2)})
    (A:inner_metric_space (@euclidean_inner_productP R 2)->Prop):
  is_circular_disc_tree H ->is_circular_disc_limit H A ->
  forall x,A x <->forall j,circular_disc_level_union H j.+1 x.
Proof.
move=>hH hA x;split.
- move=>hx j;exact:(hA x).1 hx j.+1.
- move=>hx;apply:(hA x).2=>[[|j]];last exact:hx j.
  exact:(@circular_disc_level_step_subset R H hH 0 x (hx 0%N)).
Qed.
