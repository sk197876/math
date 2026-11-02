(** Federer (1969), 2.6.2(2), p. 115, proof p. 116: every measurable
    rectangle cover of A times B has total cost at least alpha(A) beta(B).
    Here its nonnegative comparison is applied directly to the rectangle
    cover, before the general repeated-integrability class is developed.
    This is a variation of proof order; no finite-measure hypothesis is
    added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureIndexedCover MeasureAlmostUP MeasureAlmostBasic
  CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureIntegralUP MeasureIntegralComparison MeasureExtendedCharacteristicIntegral
  TotalNonnegativeSeriesIntegral NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_rectangle_cover_cost_lower]: supporting
    inequality in Federer 2.6.2(2), proof p. 116: the repeated
    integral of the covered rectangle is bounded by the sum of
    the repeated integrals of the covering rectangles. This uses
    2.4.8, p. 84, for the nonnegative series, including infinite
    weights. The factors and covering sequence need not be finite. *)
Lemma product_rectangle_cover_cost_lower (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (A : set X) (B : set Y) (C : nat -> set X) (D : nat -> set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  (forall n, measure_measurable alpha (C n) /\ measure_measurable beta (D n)) ->
  A `*` B `<=` (\bigcup_n (C n `*` D n)) ->
  alpha A * beta B <= nonnegative_sum setT (fun n => alpha (C n)*beta (D n)).
Proof.
move=> hA hB hm hcover.
pose s := @CharacteristicFunction.value R X A.
pose t n := @CharacteristicFunction.value R X (C n).
have hs : is_characteristic_function A s := CharacteristicFunction.laws R A.
have ht n : is_characteristic_function (C n) (t n) := CharacteristicFunction.laws R (C n).
pose u n x : extended_real_line R := beta (D n)*(t n x)%:E.
have hu n x : 0 <= u n x.
  exact: mule_ge0 (measure_nonnegative hb _) (characteristic_extended_nonnegative (ht n) x).
have hi n : is_measure_integral alpha (partial_function_total (u n)) (beta (D n)*alpha (C n)).
  exact (@measure_nonnegative_extended_characteristic_integral R X alpha ha (C n) (t n)
    (beta (D n)) (ht n) (hm n).1 (measure_nonnegative hb _)).
have hsum := @total_nonnegative_series_integral R X alpha ha u _ hu hi.
have hleft := @measure_nonnegative_extended_characteristic_integral R X alpha ha A s
  (beta B) hs hA (measure_nonnegative hb B).
have hpoint x : beta B*(s x)%:E <= nonnegative_sum setT (fun n => u n x).
  case: (pselect (A x))=> hx.
  - rewrite (characteristic_on_set hs hx) mule1.
    pose F n : set Y := if pselect (C n x) then D n else set0.
    have hcov : B `<=` \bigcup_n F n.
      move=> y hy; have [n _ [hcx hdy]] := hcover (x,y) (conj hx hy).
      exists n=> //; by rewrite /F; case: pselect=> // hn; exfalso; exact: hn hcx.
    have hbound := @measure_indexed_cover R Y [the choiceType of (nat : Type)]
      beta hb B setT F (countableP setT) hcov.
    have he : nonnegative_sum setT (fun n => beta (F n)) = nonnegative_sum setT (fun n => u n x).
      apply: nonnegative_sum_ext=> n _; rewrite /F /u.
      case: pselect=> hn.
      + by rewrite (characteristic_on_set (ht n) hn) mule1.
      + by rewrite (characteristic_off_set (ht n) hn) mule0 (measure_empty hb).
    by rewrite -he.
  - rewrite (characteristic_off_set hs hx) mule0; exact: nonnegative_sum_nonnegative.
have hle := @measure_integral_monotone R X alpha ha _ _ _ _ hleft hsum.
have hcomp : beta B*alpha A <= nonnegative_sum setT (fun n => beta (D n)*alpha (C n)).
  apply: hle.
  apply: (@measure_almost_everywhere_mono R X alpha ha setT _ _ (measure_almost_everywhere_true ha)).
  move=> x _; exists (beta B*(s x)%:E), (nonnegative_sum setT (fun n => u n x)).
  split=> //; split=> //; exact: hpoint.
rewrite muleC in hcomp; apply: le_trans hcomp _.
apply: nonnegative_sum_mono=> n _; by rewrite muleC.
Qed.
