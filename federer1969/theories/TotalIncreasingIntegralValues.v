(** The increasing-integral calculation in Federer (1969), 2.10.15, p. 178,
    uses 2.4.7, p. 84, twice: first on fibre-count functions, then on the
    projection parameter. This total extended-input adapter supplies the
    actual increasing limit of prescribed integral values. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit ExtendedIncreasingLimitSupremum
  PartialFunctionBasic PartialFunctionLimitExtremaUP PartialExtendedOrderLoci
  TotalExtendedLowerLimit MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP MeasureIncreasingConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [total_increasing_integral_values]: supporting
    total-function form of 2.4.7, p. 84, for the two
    integral limits in 2.10.15, p. 178. Pointwise and
    integral limits may both be infinite. *)
Lemma total_increasing_integral_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> X -> extended_real_line R) (g : X -> extended_real_line R)
    (a : nat -> \bar R) (b : \bar R) :
  (forall n x, 0<=f n x) ->
  (forall x, extended_increases_to (fun n => f n x) (g x)) ->
  (forall n, is_measure_integral mu (partial_function_total (f n)) (a n)) ->
  is_measure_integral mu (partial_function_total g) b -> extended_increases_to a b.
Proof.
move=> hpos hlim hi hgi.
have hmon n m x : (n<=m)%N -> f n x<=f m x := (hlim x).1 n m.
have he : total_extended_lower_limit f=g.
  apply/funext=> x; exact: extended_order_limit_unique
    (total_extended_lower_limit_increases hmon x).2 (hlim x).2.
have hg : is_partial_function_lower_limit (fun n => partial_function_total (f n)) (partial_function_total g).
  rewrite -he; exact: total_extended_lower_limit_specification.
have hp n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (partial_function_total (f n))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f n x); split=> //; exact: hpos.
have hinc n : measure_almost_everywhere mu
    (partial_extended_le_locus (partial_function_total (f n)) (partial_function_total (f n.+1))).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (f n x),(f n.+1 x); split=> //; split=> //; exact: hmon n n.+1 x (leqnSn n).
exact: (@measure_increasing_integral_values R X mu hm _ _ a b hg hp hinc hi hgi).
Qed.
