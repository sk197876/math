(** Finite signed coefficient combinations for the section
    polynomial in Federer (1969), 3.2.45, pp. 279–280.
    This is an application of 2.4.4(4), pp. 82–83. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic ExtendedRealPartial
  PartialExtendedArithmetic MeasureUP MeasureIntegralUP MeasureIntegralAddition MeasureIntegralGraphEquivalence
  MeasureFiniteRealSumIntegral MeasureFiniteRealScaleIntegral MeasureStepConstants MeasureStepIntegralIdentification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_signed_real_sum_integral]: supporting
    finite interpolation of the section coefficients in
    Federer 3.2.45, pp. 279–280. Actual finite real
    integral values may have either sign. Each partial
    extended sum is defined because both values are
    finite, by 2.4.4(4), pp. 82–83. No positivity
    premise is imposed on the inverse interpolation
    coefficients. Empty sums and repeated indices remain. *)
Lemma finite_signed_real_sum_integral (R : realType) (X : choiceType) (I : eqType)
    (mu : set X -> \bar R) (hm : is_measure mu) (s : seq I)
    (u : I -> X -> real_line_metric R) (b : I -> R) :
  (forall i, i \in s -> is_measure_integral mu
    (partial_real_function_embed (partial_function_total (u i))) (b i)%:E) ->
  is_measure_integral mu (partial_real_function_embed
    (partial_function_total (fun x => ((\sum_(i <- s) u i x) : real_line_metric R))))
    (\sum_(i <- s) b i)%:E.
Proof.
elim: s=> [|i s hInduction] hIntegrals.
- have hFunction : (fun x : X => ((\sum_(i <- [::]) u i x) : real_line_metric R))=(fun _ => 0%R).
    by apply: funext=> x; rewrite big_nil.
  rewrite hFunction big_nil.
  have h := @measure_step_constant_integral R X mu hm 0%R; rewrite mul0e in h.
  exact (@measure_step_function_integral R X mu hm _ 0%:E (@measure_step_constant R X mu hm 0%R) h).
- have hTail j : j \in s -> is_measure_integral mu
      (partial_real_function_embed (partial_function_total (u j))) (b j)%:E.
    move=> hj; apply: hIntegrals; by rewrite in_cons hj orbT.
  have hDefined : extended_add (b i)%:E (\sum_(j <- s) b j)%:E=
      Some (b i+\sum_(j <- s) b j)%:E by rewrite /extended_add /= -EFinD.
  have h := @measure_integral_add R X mu hm _ _ _ _ _
    (hIntegrals i (mem_head i s)) (hInduction hTail) hDefined.
  have hFunction : (fun x : X => ((\sum_(j <- i::s) u j x) : real_line_metric R))=
      (fun x => (u i x+\sum_(j <- s) u j x)).
    by apply: funext=> x; rewrite big_cons.
  rewrite hFunction big_cons.
  exact: measure_integral_graph_equivalent (real_total_sum_embedding_graph _ _) h.
Qed.

(** Source for [finite_signed_real_combination_integral]: supporting
    inverse interpolation under the integral in Federer
    3.2.45, pp. 279–280. The original finite scalar
    multiplication law, 2.4.4(3), p. 82, combines
    with signed finite additivity. Every prescribed real
    coefficient, including zero and negative values, is
    retained. All input integrals are proved finite
    before using their scalar representatives. *)
Theorem finite_signed_real_combination_integral (R : realType) (X : choiceType) (I : eqType)
    (mu : set X -> \bar R) (hm : is_measure mu) (s : seq I)
    (u : I -> X -> real_line_metric R) (b c : I -> R) :
  (forall i, i \in s -> is_measure_integral mu
    (partial_real_function_embed (partial_function_total (u i))) (b i)%:E) ->
  is_measure_integral mu (partial_real_function_embed
    (partial_function_total (fun x => ((\sum_(i <- s) c i*u i x) : real_line_metric R))))
    (\sum_(i <- s) c i*b i)%:E.
Proof.
move=> hIntegrals.
apply: (@finite_signed_real_sum_integral R X I mu hm s
  (fun i x => (c i*u i x : real_line_metric R)) (fun i => c i*b i))=> i hi.
exact: (@measure_finite_real_total_scale_integral R X mu hm (u i) (b i) (c i) (hIntegrals i hi)).
Qed.
