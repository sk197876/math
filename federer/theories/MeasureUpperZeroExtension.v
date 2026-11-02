(** Federer (1969), 2.4.10, p. 85: upper step functions may be restricted to
    measurable pieces when splitting upper integrals. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureStepFunctionUP
  MeasureStepNonnegative PartialExtendedOrderLoci MeasureZeroStepFunction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_upper_step_nonnegative_almost]:
    supporting nonnegativity of upper step functions for the
    nonnegative density in Federer 2.4.10, p. 85;
    compare the proof of 2.4.3(3), p. 82. *)
Lemma nonnegative_upper_step_nonnegative_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) :
  measure_almost_everywhere mu (partial_extended_nonnegative_locus f) -> is_measure_upper_function mu f u ->
  measure_almost_everywhere mu (partial_real_nonnegative_locus u).
Proof.
move=> hp hu; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hp hu.2)).
move=> x [[z [hz hpos]] [r [y [hr [hy hyr]]]]].
have he := partial_function_single_valued hz hy.
exists r; split=> //; have h : 0 <= r%:E by apply: le_trans _ hyr; by rewrite -he.
exact h.
Qed.

(** Source for [zero_extension_real_nonnegative_almost]: supporting
    nonnegativity of restricted upper step functions for
    Federer 2.4.10, p. 85. *)
Lemma zero_extension_real_nonnegative_almost (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (u : partial_function X (real_line_metric R)) :
  measure_almost_everywhere mu (partial_real_nonnegative_locus u) ->
  measure_almost_everywhere mu (partial_real_nonnegative_locus
    (partial_function_zero_extension (0%R : real_line_metric R) A u)).
Proof.
move=> hp; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hp).
move=> x [y [hy hpos]]; have [ha|ha] := pselect (A x).
- exists y; split=> //; apply/partial_function_zero_extension_graph; left; by split.
- exists 0%R; split=> //; apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [measure_upper_step_zero_extension]: supporting
    restriction of an upper function to a measurable set
    in Federer 2.4.10, p. 85. The majorised
    function itself need not be measurable. *)
Lemma measure_upper_step_zero_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (f : partial_function X (extended_real_line R)) (u : partial_function X (real_line_metric R)) :
  measure_measurable mu A -> is_measure_upper_function mu f u ->
  is_measure_upper_function mu (partial_function_zero_extension (0 : extended_real_line R) A f)
    (partial_function_zero_extension (0%R : real_line_metric R) A u).
Proof.
move=> hA hu; split; first exact (@measure_step_zero_extension R X mu hm A u hA hu.1).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hu.2).
move=> x [r [y [hr [hy hyr]]]]; have [ha|ha] := pselect (A x).
- exists r,y; split.
  + apply/partial_function_zero_extension_graph; left; by split.
  + split=> //; apply/partial_function_zero_extension_graph; left; by split.
- exists 0%R,0; split.
  + apply/partial_function_zero_extension_graph; right; by split.
  + split=> //; apply/partial_function_zero_extension_graph; right; by split.
Qed.
