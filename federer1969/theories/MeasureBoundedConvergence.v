(** Federer (1969), 2.4.9, p. 85, Lebesgue's bounded convergence theorem.
    The proof follows the book: domination gives summability; Fatou applied
    to 2h-|fn-g| forces the nonnegative integral errors to zero; the
    absolute integral inequality gives convergence of the signed integrals.
    We use the equivalent eventual-bound consequence of Fatou instead of a
    separate limsup operator. No relevant correction occurs in the local
    Federer erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP
  PartialExtendedArithmetic PartialFunctionLowerLimitSealed MeasureUP MeasureAlmostUP
  MeasurableFunctionUP PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasureIntegralUP MeasureIntegralAddition MeasureIntegralDifference
  MeasureIntegralAlmostEquality MeasureAbsoluteSummability PartialDominatedConvergence
  DominatedErrorGraphs MeasureDominatedComplement MeasureFatou ExtendedLowerLimit
  FatouReflectedErrorLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_bounded_convergence_values]: the two
    convergence conclusions of Federer 2.4.9, p. 85,
    for arbitrary real representatives of the finite integrals.
    The conull finite-value region is derived separately from
    the printed hypotheses by measure_dominated_finite_limit_region. *)
Lemma measure_bounded_convergence_values (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) (a e : nat -> R) (b c : R) :
  measure_almost_everywhere mu (partial_dominated_real_limit_locus f g h) ->
  (forall n, is_measure_integral mu (f n) (a n)%:E) ->
  is_measure_integral mu g b%:E -> is_measure_integral mu h c%:E ->
  (forall n, is_measure_integral mu (partial_absolute_difference (f n) g) (e n)%:E) ->
  extended_order_limit (fun n => (e n)%:E) 0 /\
  extended_order_limit (fun n => (a n)%:E) b%:E.
Proof.
move=> hreg hi hgi hhi hei.
have hdouble : is_measure_integral mu (partial_extended_function_add h h) (c+c)%:E.
  apply: (@measure_integral_add R X mu hm h h c%:E c%:E (c+c)%:E hhi hhi).
  by rewrite /extended_add /=.
pose v n := partial_dominated_complement (f n) g h.
pose k := @PartialFunctionLowerLimit.value R X v.
have hk := @PartialFunctionLowerLimit.laws R X v.
have hki : is_measure_integral mu k (c+c)%:E.
  apply: (@measure_integral_almost_equal R X mu hm _ k (c+c)%:E hdouble).
  exact (@measure_dominated_complement_lower_limit R X mu hm f g h k hk hreg).
have hvi n : is_measure_integral mu (v n) (c+c-e n)%:E.
  exact (@measure_integral_finite_difference R X mu hm _ _ (c+c)%R (e n) hdouble (hei n)).
have hvp n : measure_almost_everywhere mu (partial_extended_nonnegative_locus (v n)).
  exact (@measure_dominated_complement_nonnegative R X mu hm f g h n hreg).
have hfatou := @measure_fatou_integral_values R X mu hm v k
  (fun n => (c+c-e n)%:E) (c+c)%:E hk hvp hvi hki.
have hbound n : (`|a n-b| <= e n)%R.
  exact (@measure_integral_difference_absolute_bound R X mu hm (f n) g (a n) b (e n)
    (hi n) hgi (hei n)).
have hep n : (0 <= e n)%R := le_trans (normr_ge0 _) (hbound n).
have helim := fatou_reflected_nonnegative_error_limit hep hfatou.
split=> //; exact: real_integral_error_comparison_limit hbound helim.
Qed.

(** Source for [measure_bounded_convergence]: complete Federer 2.4.9, p. 85,
    including the summability implicit in the two conclusions. Existential
    real values represent the integrals by their defining laws. The bounds
    and pointwise convergence may hold almost everywhere. *)
Theorem measure_bounded_convergence (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  is_measure_summable mu h ->
  (forall n, is_measure_measurable_function mu (f n)) ->
  is_measure_measurable_function mu g ->
  (forall n, measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (f n)) h)) ->
  measure_almost_everywhere mu (partial_extended_convergence_locus f g) ->
  exists (a e : nat -> R) (b : R),
    (forall n, is_measure_integral mu (f n) (a n)%:E) /\
    is_measure_integral mu g b%:E /\
    (forall n, is_measure_integral mu (partial_absolute_difference (f n) g) (e n)%:E) /\
    extended_order_limit (fun n => (e n)%:E) 0 /\
    extended_order_limit (fun n => (a n)%:E) b%:E.
Proof.
move=> hh hf hg hb hl.
have hreg := @measure_dominated_finite_limit_region R X mu hm f g h hh hb hl.
have hgb := @measure_dominated_limit_bound R X mu hm f g h hreg.
have hgs := (@measure_dominated_summable R X mu hm g h hg hh hgb).1.
have hfs n := (@measure_dominated_summable R X mu hm (f n) h (hf n) hh (hb n)).1.
have hes n := (@measure_summable_difference R X mu hm (f n) g (hfs n) hgs).2.
pose a n := projT1 (cid (hfs n)).
pose e n := projT1 (cid (hes n)).
have hai n : is_measure_integral mu (f n) (a n)%:E := projT2 (cid (hfs n)).
have hei n : is_measure_integral mu (partial_absolute_difference (f n) g) (e n)%:E := projT2 (cid (hes n)).
have [b hbi] := hgs; have [c hci] := hh.
have hlimits := @measure_bounded_convergence_values R X mu hm f g h a e b c hreg hai hbi hci hei.
exists a,e,b; split=> //; split=> //; by split.
Qed.
