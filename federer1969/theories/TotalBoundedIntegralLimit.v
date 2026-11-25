(** Federer (1969), 2.4.9, p. 85, applied twice in 2.6.2, pp. 115–116:
    passage to a decreasing intersection when the first repeated integral is
    finite. This total-function adapter derives limit measurability from
    almost-everywhere convergence; it adds no new integration axiom. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  ExtendedLowerLimitUP ExtendedLowerLimit ExtendedConvergentLowerLimit TotalExtendedLowerLimit
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci PartialAbsolutePartsGraph
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP
  MeasurableAlmostModification MeasureIntegralUP MeasureIntegralUniqueness
  PartialDominatedConvergence MeasureBoundedConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_nonnegative_bounded_integral_limit]:
    supporting total, nonnegative case of Federer 2.4.9,
    p. 85, used for the decreasing-set calculation in
    2.6.2, pp. 115–116. The first function dominates
    all later ones and has finite integral; pointwise convergence
    is needed only almost everywhere. The supplied limit of the
    integral values is identified with the actual limit integral. *)
Lemma total_nonnegative_bounded_integral_limit (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (u : nat -> X -> extended_real_line R) (g : X -> extended_real_line R)
    (a : nat -> \bar R) (b : \bar R) :
  (forall n x, 0 <= u n x) -> (forall n x, u n x <= u 0%N x) ->
  (forall n, is_measure_integral mu (partial_function_total (u n)) (a n)) ->
  a 0%N \is a fin_num ->
  measure_almost_everywhere mu [set x | extended_order_limit (fun n => u n x) (g x)] ->
  extended_order_limit a b -> is_measure_integral mu (partial_function_total g) b.
Proof.
move=> hp hdom hi hfin hlim halim.
pose f n := partial_function_total (u n).
have hf n : is_measure_measurable_function mu (f n) := (hi n).1.
have hlm := @total_extended_lower_limit_measurable R X mu hm u hf.
have he : measure_almost_equal mu (partial_function_total (total_extended_lower_limit u)) (partial_function_total g).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlim)=> x hx.
  have ex : total_extended_lower_limit u x = g x.
    exact (@extended_lower_limit_unique R (fun n => u n x) _ _ (extended_lower_limit_laws _) (extended_convergent_lower_limit hx)).
  exists (g x); by split.
have hg : is_measure_measurable_function mu (partial_function_total g).
  exact (@measurable_function_almost_equal R X (extended_real_line R) mu hm _ _ hlm he).
have hs : is_measure_summable mu (f 0%N).
  exists (fine (a 0%N)); rewrite fineK //; exact: hi.
have hbnd n : measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (f n)) (f 0%N)).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|u n x|), (u 0%N x); split.
  - exists (u n x); by split.
  - split=> //; by rewrite (gee0_abs (hp n x)); exact: hdom.
have hconv : measure_almost_everywhere mu (partial_extended_convergence_locus f (partial_function_total g)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hlim)=> x hx.
  exists (fun n => u n x), (g x); by split=> //; split.
have [a' [e [b' [hai [hgi [_ [_ hlim']]]]]]] := @measure_bounded_convergence R X mu hm
  f (partial_function_total g) (f 0%N) hs hf hg hbnd hconv.
have heq : (fun n => (a' n)%:E) = a.
  apply: funext=> n; exact (@measure_integral_unique R X mu (f n) _ _ (hai n) (hi n)).
rewrite heq in hlim'.
have eb := @extended_order_limit_unique R a _ _ hlim' halim.
by rewrite -eb.
Qed.
