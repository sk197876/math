(** Constant-function boundary cases for Federer (1969), 2.4.1, p. 80. The
    assigned value is c*mu(X), including infinite measures and c=0. source
    editions: MeasureStepFunctionUP.v. These are supporting consequences,
    not separate numbered claims in the book. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureBasic MeasurableTotalBasic MeasureStepFunctionUP NumericalSumSingleSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_step_constant_integral]: constant-function
    evaluation supporting the definition and zero-product convention
    in Federer 2.4.1, p. 80. *)
Lemma measure_step_constant_integral (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) :
  is_measure_step_integral mu (partial_function_total (fun _ : X => (c : real_line_metric R))) (c%:E*mu setT).
Proof.
pose u := partial_function_total (fun _ : X => (c : real_line_metric R)).
have hc : partial_function_preimage u [set c] = setT.
  apply/seteqP; split=> // x _; exists c; by split.
have hz y : (@setT R) y -> y != c -> y%:E*mu (partial_function_preimage u [set y]) = 0.
  move=> _ hy.
  have he : partial_function_preimage u [set y] = set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [z [<- he]]; apply: (negP hy); apply/eqP; exact: esym he.
  by rewrite he (measure_empty hm) mule0.
rewrite /is_measure_step_integral (@numerical_sum_single_support R R setT _ c Logic.I hz).
by rewrite hc.
Qed.

(** Source for [measure_step_constant]: constants satisfy the
    countable-range step definition in Federer 2.4.1, p. 80,
    even on a space of infinite measure. *)
Lemma measure_step_constant (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) :
  is_measure_step_function mu (partial_function_total (fun _ : X => (c : real_line_metric R))).
Proof.
constructor.
- exact: measurable_total_constant.
- apply: sub_countable _ (countable1 (c : real_line_metric R)).
  apply: subset_card_le=> y [x hy]; exact: esym hy.
- exists (c%:E*mu setT); exact: measure_step_constant_integral.
Qed.
