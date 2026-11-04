(** Federer (1969), 3.2.14, pp. 251–252, and
    3.2.47(3), p. 283: Lipschitz maps preserve
    finite Hausdorff rectifiability of arbitrary original sets.
    Both the countable almost-cover and the finite outer-mass
    requirement are proved, without completed image measurability. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import RectifiableSetUP LipschitzUP LipschitzRectifiableImages
  HausdorffMeasure HausdorffRestrictedLipschitz MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_measure_rectifiable_lipschitz_image]:
    the finite-mass form of the Lipschitz image observation
    in 3.2.14, p. 252, supporting the converse
    rectifiability argument in 3.2.47(3), p. 283.
    The actual original image need not be measurable. *)
Theorem hausdorff_measure_rectifiable_lipschitz_image (R:realType)
    (X Y:metricType R) m (S:set X) (f:X->Y):
  is_metric_lipschitz S f ->
  is_measure_m_rectifiable (@hausdorff_measure R X m) m S ->
  is_measure_m_rectifiable (@hausdorff_measure R Y m) m (f @` S).
Proof.
move=>hLip hRect; split.
- exact:(countably_hausdorff_rectifiable_lipschitz_image hLip hRect.1).
- have [L [_ hBound]]:=hLip.
  have hEstimate:=@hausdorff_lipschitz_on_bound R X Y S f L m S hBound (fun x hx=>hx).
  have hFinite:@hausdorff_measure R X m S \is a fin_num.
    rewrite ge0_fin_numE; first exact hRect.2.
    exact (@measure_nonnegative R X (@hausdorff_measure R X m)
      (@hausdorff_measure_is_measure R X m) S).
  have hValue:@hausdorff_measure R X m S=(fine (@hausdorff_measure R X m S))%:E.
    by rewrite fineK.
  have hUpperFinite:((L^+m)%R%:E* @hausdorff_measure R X m S< +oo)%E.
    by rewrite hValue -EFinM ltry.
  exact:(le_lt_trans hEstimate hUpperFinite).
Qed.
