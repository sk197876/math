(** Federer (1969), 2.4.7, p. 84: Lebesgue's increasing convergence theorem.
    The proof uses nonnegative integrability and monotonicity for one
    inequality and Fatou for the other, exactly as in Federer's two-sentence
    proof. The conclusion includes the existence of the pointwise increasing
    limit on a conull set and its integral; infinity is permitted. No
    relevant correction occurs in the local erratum. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit
  PartialFunctionUP PartialFunctionLimitExtremaUP PartialFunctionLowerLimitSealed
  MeasureUP MeasureAlmostUP MeasurableFunctionUP PartialExtendedOrderLoci
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralComparison MeasureNonnegativeIntegral
  MeasureLowerLimitNonnegative MeasureFatou ExtendedLowerLimitUP ExtendedLowerLimit
  ExtendedIncreasingLowerLimit PartialIncreasingLowerLimit MeasureIncreasingLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_increasing_integral_values]: direct
    limit identity of Federer 2.4.7, p. 84, with
    the integral values and lower-limit function specified by
    their abstract laws. *)
Theorem measure_increasing_integral_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (a : nat -> \bar R) b :
  is_partial_function_lower_limit f g ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, measure_almost_everywhere mu (partial_extended_le_locus (f n) (f n.+1))) ->
  (forall n, is_measure_integral mu (f n) (a n)) -> is_measure_integral mu g b ->
  extended_increases_to a b.
Proof.
move=> hg hp hmon hi hgi.
have hstep n : a n <= a n.+1.
  exact (@measure_integral_monotone R X mu hm (f n) (f n.+1) (a n) (a n.+1)
    (hi n) (hi n.+1) (hmon n)).
have ha : forall n m, (n <= m)%N -> a n <= a m.
  exact (@homo_leq (\bar R) a (fun v w => is_true (v <= w))
    (fun v => lexx v) (fun w v z hvw hwz => le_trans hvw hwz) hstep).
have hb n : a n <= b.
  apply: (@measure_integral_monotone R X mu hm (f n) g (a n) b (hi n) hgi).
  exact ((@measure_increasing_lower_limit_laws R X mu hm f g hg hmon).2 n).
have hl := increasing_lower_limit_supremum ha (extended_lower_limit_laws a).
have hle : extended_lower_limit a <= b.
  apply: (extended_real_supremum_least hl)=> c [n ->]; exact: hb.
have hge := @measure_fatou_integral_values R X mu hm f g a b hg hp hi hgi.
have he : extended_lower_limit a = b by apply/eqP; rewrite eq_le hle hge.
rewrite -he; exact: extended_increasing_lower_limit ha (extended_lower_limit_laws a).
Qed.

(** Source for [measure_increasing_convergence]: complete Federer 2.4.7, p.
    84, with explicit pointwise convergence, integrability and increasing
    convergence of integrals *)
Theorem measure_increasing_convergence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_lower_limit f g ->
  (forall n, is_measure_measurable_function mu (f n)) ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, measure_almost_everywhere mu (partial_extended_le_locus (f n) (f n.+1))) ->
  measure_almost_everywhere mu (partial_extended_increasing_limit_locus f g) /\
  is_measure_integral mu g (measure_lower_integral mu g) /\
  extended_increases_to (fun n => measure_lower_integral mu (f n)) (measure_lower_integral mu g).
Proof.
move=> hg hf hp hmon.
have hgi := (@measure_lower_limit_nonnegative_integral R X mu hm f g hg hf hp).1.
split; first exact (@measure_increasing_lower_limit_laws R X mu hm f g hg hmon).1.
split=> //; apply: (@measure_increasing_integral_values R X mu hm f g
  (fun n => measure_lower_integral mu (f n)) _ hg hp hmon _ hgi)=> n.
exact (@nonnegative_measurable_function_integral R X mu hm (f n) (hf n) (hp n)).1.
Qed.

(** Source for [measure_sealed_increasing_convergence]: usable
    sealed-limit form of Federer 2.4.7, p. 84;
    no construction of the limit is exposed downstream. *)
Corollary measure_sealed_increasing_convergence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R)) :
  (forall n, is_measure_measurable_function mu (f n)) ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, measure_almost_everywhere mu (partial_extended_le_locus (f n) (f n.+1))) ->
  measure_almost_everywhere mu
    (partial_extended_increasing_limit_locus f (@PartialFunctionLowerLimit.value R X f)) /\
  is_measure_integral mu (@PartialFunctionLowerLimit.value R X f)
    (measure_lower_integral mu (@PartialFunctionLowerLimit.value R X f)) /\
  extended_increases_to (fun n => measure_lower_integral mu (f n))
    (measure_lower_integral mu (@PartialFunctionLowerLimit.value R X f)).
Proof.
exact (@measure_increasing_convergence R X mu hm f _ (@PartialFunctionLowerLimit.laws R X f)).
Qed.
