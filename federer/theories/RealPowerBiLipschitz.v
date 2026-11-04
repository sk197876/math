(** Federer (1969), 3.2.46, p. 281: both real-degree
    Hausdorff comparisons follow from the actual two-sided
    local metric bounds. This expands the covering argument
    of 2.10.11, p. 176, without an assumed multiplicity theorem. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import LipschitzUP MetricBiLipschitzUP
  MetricBiLipschitzInverse RealHausdorffMeasure RealPower RealPowerRestrictedLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_bilipschitz_bounds]: the two
    real-degree image/source bounds supporting 3.2.46,
    p. 281. Inverses are local auxiliary representatives
    used only on the exact image; arbitrary nonmeasurable
    source sets and infinite masses are retained. *)
Theorem real_hausdorff_bilipschitz_bounds (R : realType) (X Y : metricType R)
    (K : set X) (f : X -> Y) (L p : R) (hp : (0<=p)%R) (x0 : X) (B : set X) :
  (0<L)%R -> is_metric_bilipschitz_bound K f L -> B `<=` K ->
  @real_hausdorff_measure R Y p hp (f @` B) <=
    (real_power L p)%:E * @real_hausdorff_measure R X p hp B /\
  @real_hausdorff_measure R X p hp B <=
    (real_power L p)%:E * @real_hausdorff_measure R Y p hp (f @` B).
Proof.
move=> hL hBound hBK; split.
- exact: real_hausdorff_on_positive_lipschitz hL hBound.1 hBK.
- have [q [hInverse hQ]] := metric_bilipschitz_inverse_exists x0 hBound.
  have hSub : f @` B `<=` f @` K.
    move=> y [x hx <-]; by exists x; first exact: hBK x hx.
  have hImage : q @` (f @` B)=B.
    apply/seteqP; split=> x.
    + move=> [y [z hz <-] <-]; by rewrite (hInverse z (hBK z hz)).
    + move=> hx; exists (f x); first by exists x.
      exact: hInverse x (hBK x hx).
  have h := @real_hausdorff_on_positive_lipschitz R Y X (f @` K) q L p hp
    (f @` B) hL hQ hSub.
  by rewrite hImage in h.
Qed.
