(** Federer (1969), 3.2.17, p. 254:
    the two Hausdorff mass inequalities used
    to compare source and image densities.
    They apply to every subset of the
    parameter domain, without measurability assumptions. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import LipschitzUP MetricBiLipschitzUP MetricBiLipschitzInverse
  HausdorffMeasure HausdorffRestrictedLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [metric_bilipschitz_hausdorff_bounds]:
    the factors lambda^m in the source/image
    measure comparison of Federer 3.2.17,
    p. 254. The inverse is used only
    on the actual image of the subset. *)
Theorem metric_bilipschitz_hausdorff_bounds (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L : R) (x0 : X) m (A : set X) :
  is_metric_bilipschitz_bound K f L -> A `<=` K ->
  @hausdorff_measure R Y m (f @` A)<=(L^+m)%R%:E* @hausdorff_measure R X m A /\
  @hausdorff_measure R X m A<=(L^+m)%R%:E* @hausdorff_measure R Y m (f @` A).
Proof.
move=> hB hAK; split.
- exact: hausdorff_lipschitz_on_bound hB.1 hAK.
- have [g [hgf hg]] := metric_bilipschitz_inverse_exists x0 hB.
  have hsub : f @` A `<=` f @` K.
    move=> y [x hx <-]; by exists x; first exact: hAK x hx.
  have hImage : g @` (f @` A)=A.
    apply/seteqP; split=> x.
    + move=> [y [z hz <-] <-]; by rewrite (hgf z (hAK z hz)).
    + move=> hx; exists (f x); first by exists x.
      exact: hgf x (hAK x hx).
  have hh := @hausdorff_lipschitz_on_bound R Y X (f @` K) g L m (f @` A) hg hsub.
  by rewrite hImage in hh.
Qed.
