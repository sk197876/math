(** Federer (1969), 2.4.16, p. 90: positive weighted signs give tests with
    exactly the sign of f. The public weight laws retain positivity even on
    null pieces, so this equality is pointwise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableFunctionUP PositiveIntegrableWeightUP PositiveIntegrableWeightMeasurable
  PositiveIntegrableWeightNorm TotalScalarArithmetic ScalarSignTest MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_sign_test]: the weight times sign(f)
    used in Federer 2.4.16, p. 90. The abstract weight may be
    supplied by any construction satisfying its stated laws. *)
Definition weighted_sign_test (R : realType) (X : Type)
    (f w : X -> real_norm_metric_space (scalar_absolute_value_norm R)) x :
    real_norm_metric_space (scalar_absolute_value_norm R) := w x * Num.sg (f x).

(** Source for [weighted_sign_test_absolute]: supporting absolute-value
    identity in Federer 2.4.16, p. 90, first integral display. *)
Lemma weighted_sign_test_absolute (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f w : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_positive_integrable_weight mu [set x | f x <> 0] w ->
  forall x, `|weighted_sign_test f w x| = w x.
Proof.
move=> hw x; have [hf|hf] := eqVneq (f x) 0.
- have hw0 : w x = 0.
    apply/eqP; rewrite eq_le (positive_weight_nonnegative hw x) andbT leNgt.
    apply/negP=> hp; exact: ((positive_weight_support hw x).1 hp) hf.
  by rewrite /weighted_sign_test hw0 mul0r normr0.
- by rewrite /weighted_sign_test normrM (ger0_norm (positive_weight_nonnegative hw x)) normr_sg hf mulr1.
Qed.

(** Source for [weighted_sign_test_sign]: the exact sign equality
    in Federer 2.4.16, p. 90, including null exceptional loci. *)
Lemma weighted_sign_test_sign (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (f w : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_positive_integrable_weight mu [set x | f x <> 0] w ->
  forall x, Num.sg (weighted_sign_test f w x) = Num.sg (f x).
Proof.
move=> hw x; have [hf|hf] := eqVneq (f x) 0.
- by rewrite /weighted_sign_test hf sgr0 mulr0 sgr0.
have hfn : f x <> 0 by move=> he; move: hf; rewrite he eqxx.
have hp : 0 < w x := (positive_weight_support hw x).2 hfn.
by rewrite /weighted_sign_test sgrM (gtr0_sg hp) mul1r sgr_id.
Qed.

(** Source for [weighted_sign_test_admissible]: supporting full
    finite-q unit-test admissibility and sign constraint, Federer
    2.4.16, p. 90. It holds for every q>=1 and places no
    finiteness assumption on the norm of f. *)
Theorem weighted_sign_test_admissible (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (q : R)
    (f w : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_positive_integrable_weight mu [set x | f x <> 0] w -> (1 <= q)%R ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_finite_lp_unit_test mu q (partial_function_total (weighted_sign_test f w)) /\
  is_sign_matching_test (partial_function_total f) (partial_function_total (weighted_sign_test f w)).
Proof.
move=> hw hq hf; split.
- apply: (@positive_integrable_weight_unit_test R X mu hm _ w _ q hw hq).
  + exact: (@measurable_total_scalar_product R X mu hm w
      (fun x => (Num.sg (f x) : real_norm_metric_space (scalar_absolute_value_norm R)))
      (@positive_integrable_weight_measurable R X mu hm _ w hw)
      (@measurable_total_scalar_sign R X mu hm f hf)).
  + exact: weighted_sign_test_absolute hw.
- move=> x z; split.
  + move=> [y [<- hy]]; exists (weighted_sign_test f w x); split=> //.
    by rewrite (weighted_sign_test_sign hw).
  + move=> [y [<- hy]]; exists (f x); split=> //.
    by rewrite (weighted_sign_test_sign hw) in hy.
Qed.
