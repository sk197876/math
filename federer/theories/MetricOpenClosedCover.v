(** Federer (1969), 2.2.1, p. 60: in a metric space every open set is a
    countable union of closed sets. The proof below uses only general
    pseudometric neighborhoods and the locally proved Archimedean reciprocal
    bound. It even applies to pseudometric spaces. The interiors of balls
    accommodate MathComp's general ball interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology pseudometric_structure.
From Federer Require Import ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_open_countable_closed_cover]: Federer 2.2.1, p. 60,
    metric instance of the countable closed-cover hypothesis The nth closed
    subset is the complement of the union of radius 1/(n+1) ball interiors
    centered outside U. Small neighborhoods prove exhaustion. The
    construction only serves to prove this existence statement. *)
Theorem metric_open_countable_closed_cover (R : realType) (T : pseudoMetricType R)
    (U : set T) : open U -> exists C : nat -> set T,
  (forall n, closed (C n) /\ C n `<=` U) /\ U = \bigcup_n C n.
Proof.
move=> hU; pose e n : R := ((n.+1)%:R)^-1.
have he n : 0 < e n by rewrite /e invr_gt0 ltr0n.
pose C n := ~` (\bigcup_(y in ~` U) (ball y (e n))°).
have hC n : closed (C n).
  apply: open_closedC; apply: bigcup_open=> y _; exact: open_interior.
have hCU n : C n `<=` U.
  move=> x hx; apply: contrapT=> hn; apply: hx; exists x=> //.
  exact: nbhsx_ballx (he n).
exists C; split; first by move=> n; split; [exact: hC|exact: hCU].
apply/seteqP; split.
- move=> x hx; have ho := hU; rewrite openE in ho.
  have [r hr hball] := proj1 (nbhs_ballP x U) (ho x hx).
  have [n hn] := positive_reciprocal_nat_small hr.
  exists n; first exact Logic.I.
  move=> [y hny hy]; apply: hny; apply: hball.
  apply: (@le_ball R T x (e n) r (ltW hn)).
  apply: ball_sym; exact: interior_subset hy.
- move=> x [n _ hx]; exact: hCU n x hx.
Qed.
