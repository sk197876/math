(** Federer 2.10.11, p. 176: the Hausdorff image estimate in every
    nonnegative real degree. Extend the existing positive-constant
    real-power estimate only at its missing zero-constant endpoint.
    Degree zero retains 0^0=1. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealPower RealPowerPositiveLipschitz
  RealPowerSingletonBound RealHausdorffNormalisation RealHausdorffMeasure
  LipschitzUP LipschitzBasic MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_positive_degree_singleton_zero]: supporting
    boundary fact for Federer 2.10.11, p. 176, from the singleton cover
    of 2.10.1-2, pp. 170-171. A singleton has zero Hausdorff mass in every
    positive real degree, with the actual Gamma coefficient. *)
Lemma real_hausdorff_positive_degree_singleton_zero (R : realType)
    (X : metricType R) (p : R) (hp : (0<=p)%R) (x : X) :
    (0<p)%R -> @real_hausdorff_measure R X p hp [set x]=0.
Proof.
move=> hpos.
have hb := @real_power_singleton_bound R X
  (real_hausdorff_normalisation hp) p (@real_hausdorff_measure R X p hp) x
  (@real_hausdorff_measure_specification R X p hp)
  (ltW (real_hausdorff_normalisation_positive hp)).
rewrite real_power_zero_base ?gt_eqF // mulr0 in hb.
apply/eqP; rewrite eq_le hb /=.
exact: (@measure_nonnegative R X (@real_hausdorff_measure R X p hp)
  (@real_hausdorff_measure_is_measure R X p hp) [set x]).
Qed.

(** Source for [real_hausdorff_lipschitz_image_bound]: direct real-degree
    image estimate used in Federer 2.10.11, p. 176. Every nonnegative
    real degree and every finite Lipschitz bound, including zero, is
    retained. No measurability, completeness or separability is needed
    for this image estimate. *)
Theorem real_hausdorff_lipschitz_image_bound (R : realType)
    (X Y : metricType R) (f : X -> Y) (L p : R) (hp : (0<=p)%R) :
    is_metric_lipschitz_bound setT f L -> forall A,
    @real_hausdorff_measure R Y p hp (f @` A)<=
      (real_power L p)%:E * @real_hausdorff_measure R X p hp A.
Proof.
move=> hf A; case: (ltP 0%R L)=> [hL|hL].
  exact: (@real_hausdorff_positive_lipschitz R X Y f L p hp hL hf A).
have hz : L=0%R by apply/eqP; rewrite eq_le hL hf.1.
rewrite hz; rewrite hz in hf.
case: (eqVneq p 0%R)=> [he|hp0].
- have hpow : real_power 0%R p = 1%R by rewrite he real_power_zero_exponent.
  rewrite hpow mul1e.
  have h1 := @metric_lipschitz_bound_increase R X Y setT f 0%R 1%R hf ler01.
  have hh := @real_hausdorff_positive_lipschitz R X Y f 1%R p hp ltr01 h1 A.
  by rewrite real_power_one_base mul1e in hh.
- rewrite real_power_zero_base // mul0e.
  have hpp : (0<p)%R by rewrite lt_def hp0 hp.
  case: (pselect (A !=set0))=> [[a ha]|hempty]; last first.
    have he : A=set0.
      apply/seteqP; split=> x hx //; exfalso; apply: hempty; by exists x.
    by rewrite he image_set0 (measure_empty (@real_hausdorff_measure_is_measure R Y p hp)).
  have hsub : f @` A `<=` [set f a].
    move=> y [x hx <-]; apply: (@mdist_positivity R Y (f x) (f a)).
    apply/eqP; rewrite eq_le mdist_ge0 andbT.
    by have hh := hf.2 x a I I; rewrite mul0r in hh.
  have hb := @measure_mono R Y (@real_hausdorff_measure R Y p hp)
    (@real_hausdorff_measure_is_measure R Y p hp) (f @` A) [set f a] hsub.
  by rewrite (@real_hausdorff_positive_degree_singleton_zero R Y p hp (f a) hpp) in hb.
Qed.
