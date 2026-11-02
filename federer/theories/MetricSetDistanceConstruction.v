(** Federer (1969), 2.2.10, p. 66: existence of the distance to a nonempty
    set, used for the complement of a proper open subset. This private
    witness uses only the complete real-field infimum background already
    present in the project. Source context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import MetricSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_set_distance_exists]: supporting existence for the
    distance in Federer 2.2.10, p. 66. For each point, the nonempty set of
    its distances to A is bounded below by zero, so its real infimum
    satisfies the abstract laws. *)
Theorem metric_set_distance_exists (R : realType) (T : metricType R)
    (A : set T) : A !=set0 -> exists d, is_metric_set_distance A d.
Proof.
move=> hn; pose S x := (fun a => mdist x a) @` A.
have hS x : S x !=set0 by have [a ha] := hn; exists (mdist x a); exists a.
have hl x : has_lbound (S x).
  exists 0=> r [a _ <-]; exact: mdist_ge0.
exists (fun x => inf (S x)); constructor.
- move=> x a ha; apply: (ge_inf (hl x)); by exists a.
- move=> x r hr; apply: (lb_le_inf (hS x)).
  by move=> s [a ha <-]; exact: hr a ha.
Qed.
