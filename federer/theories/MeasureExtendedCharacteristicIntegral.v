(** Federer (1969), 2.6.2, p. 116: the repeated characteristic integral of a
    rectangle is the product of its factor measures, including infinite
    factors. This supporting calculation uses 2.4.5, p. 83, and 2.4.8, p.
    84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  CharacteristicFunctionUP MeasureStepIntegralIdentification NonnegativeSum MeasureIntegralUP MeasureCharacteristicIntegral
  MeasureFiniteCharacteristicIntegral MeasureConullZeroIntegral MeasureIntegralGraphEquivalence
  TotalNonnegativeSeriesIntegral NonnegativeSeriesConstant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_extended_nonnegative]: supporting
    nonnegativity of the characteristic function in Federer 2.6.2,
    pp. 115–116, by its zero/one definition in 2.2.14, p. 70. *)
Lemma characteristic_extended_nonnegative (R : realType) (X : Type)
    (A : set X) (s : X -> R) :
  is_characteristic_function A s -> forall x, 0 <= (s x)%:E.
Proof.
move=> hs x; case: (pselect (A x))=> hx.
- by rewrite (characteristic_on_set hs hx); exact: lee01.
- by rewrite (characteristic_off_set hs hx).
Qed.

(** Source for [measure_total_characteristic_integral]: supporting
    total extended-valued presentation of Federer 2.4.5, p. 83,
    used for the repeated integral in 2.6.2, p. 116. *)
Lemma measure_total_characteristic_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (s : X -> R) :
  is_characteristic_function A s -> measure_measurable mu A ->
  is_measure_integral mu (partial_function_total (fun x => (s x)%:E)) (mu A).
Proof.
move=> hs hA.
apply: (@measure_integral_graph_equivalent R X mu
  (partial_real_function_embed (partial_function_total (fun x => (s x : real_line_metric R)))) _ (mu A)).
- move=> x y; split.
  + by move=> [r [<- <-]].
  + move=> <-; exists (s x); by split.
- exact (@measure_characteristic_integral R X mu hm A s hs hA).
Qed.

(** Source for [measure_nonnegative_extended_characteristic_integral]:
    supporting single-factor integral for the rectangle formula of Federer
    2.6.2, p. 116 A nonnegative extended weight c has integral c times the
    measure of the set. For c=infinity we apply 2.4.8 to repeated
    characteristic functions, so the null-set case retains infinity times
    zero = zero. *)
Lemma measure_nonnegative_extended_characteristic_integral
    (R : realType) (X : choiceType) (mu : set X -> \bar R)
    (hm : is_measure mu) (A : set X) (s : X -> R) (c : \bar R) :
  is_characteristic_function A s -> measure_measurable mu A -> 0 <= c ->
  is_measure_integral mu (partial_function_total (fun x => c*(s x)%:E)) (c*mu A).
Proof.
move=> hs hA; case: c=> [r| |] hc; last by [].
- have hr : (0 <= r)%R by move: hc; rewrite lee_fin.
  have [->|hrpos] := eqVneq r 0%R.
  + rewrite mul0e; apply: (measure_almost_zero_integral hm).
    apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm)).
    by move=> x _; rewrite /partial_function_total /= mul0e.
  + have hp : (0 < r)%R by rewrite lt_def hrpos hr.
    have hi := @measure_positive_characteristic_integral R X mu hm A s r hs hA hp.
    apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi).
    move=> x y; split.
    * move=> [z [hz <-]]; by rewrite -(hz : (r*s x)%R = z) EFinM.
    * move=> hy; exists (r*s x)%R; split=> //; by rewrite EFinM.
- have hi := @total_nonnegative_series_integral R X mu hm
    (fun _ : nat => fun x => ((s x)%:E : extended_real_line R)) (fun _ => mu A)
    (fun _ x => characteristic_extended_nonnegative hs x)
    (fun _ => @measure_total_characteristic_integral R X mu hm A s hs hA).
  rewrite (nonnegative_series_constant (measure_nonnegative hm A)) in hi.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ hi).
  move=> x y; change (nonnegative_sum setT (fun _ : nat => (s x)%:E) = y <-> +oo*(s x)%:E = y).
  by rewrite (nonnegative_series_constant (characteristic_extended_nonnegative hs x)).
Qed.
