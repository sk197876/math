(** Federer (1969), 1.7.13, p. 37: completeness supplies a point in the
    intersection of the nonempty nested closed sets whose diameters tend to
    zero. This supporting general metric step is proved directly using the
    Cauchy-filter definition. No Hilbert projection theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From mathcomp Require Import boolp classical_sets topology.
From Federer Require Import InnerProductUP InnerMetric InnerNormedTopology HilbertSpaceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_closed_shrinking_intersection]: Federer
    1.7.13, p. 37, the conclusion that the intersection of
    the sets C_s for s>0 contains a point. Supporting general
    form: nonempty nested closed sets with arbitrarily small
    diameter have nonempty intersection in a Hilbert space. *)
Theorem inner_closed_shrinking_intersection (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (hH : is_hilbert_space hB) (C : R -> set (inner_metric_space hB))
    (hne : forall r, 0 < r -> C r !=set0)
    (hclosed : forall r, 0 < r -> closed (C r))
    (hnest : forall r s, 0 < r -> r <= s -> C r `<=` C s)
    (hsmall : forall eps, 0 < eps -> exists r, 0 < r /\
      forall x y, C r x -> C r y -> @inner_distance R V B hB x y < eps) :
  exists x, forall r, 0 < r -> C r x.
Proof.
pose F := filter_from (fun r : R => 0 < r) C.
have FF : Filter F.
  apply: filter_from_filter; first by exists 1; exact: ltr01.
  move=> r s hr hs; case: (leP r s) => hrs.
  - exists r => // x hx; split=> //; exact: (hnest r s hr hrs x hx).
  - exists s => // x hx; split=> //; exact: (hnest s r hs (ltW hrs) x hx).
have PF : ProperFilter F := filter_from_proper FF hne.
have hca : cauchy F.
  apply: cauchy_exP => eps heps.
  have [r [hr hd]] := hsmall eps heps.
  have [x hx] := hne r hr.
  exists x; exists r => // y hy.
  exact (hd x y hx hy).
have hc := hH F PF hca.
exists (lim F) => r hr.
have hFC : F (C r) by exists r.
exact (@closed_cvg (inner_metric_space hB) (inner_metric_space hB)
  F PF idfun (C r) (hclosed r hr) hFC (lim F) (cvg_trans cvg_id hc)).
Qed.

(** Source for [inner_shrinking_intersection_unique]: Federer
    1.7.13, p. 37, the intersection consists of a single
    point: two points belonging to every shrinking set have
    distance less than every positive number, hence distance zero. *)
Theorem inner_shrinking_intersection_unique (R : realType)
    (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B)
    (C : R -> set (inner_metric_space hB))
    (hsmall : forall eps, 0 < eps -> exists r, 0 < r /\
      forall x y, C r x -> C r y -> @inner_distance R V B hB x y < eps)
    x y (hx : forall r, 0 < r -> C r x) (hy : forall r, 0 < r -> C r y) : x = y.
Proof.
apply: inner_distance_separates.
have [hd|hd] := eqVneq (@inner_distance R V B hB x y) 0; first exact hd.
have hp : 0 < @inner_distance R V B hB x y.
  by rewrite lt_def hd inner_distance_nonnegative.
have [r [hr hdiam]] := hsmall _ hp.
have hh := hdiam x y (hx r hr) (hy r hr).
by rewrite ltxx in hh.
Qed.
