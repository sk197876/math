(** Federer (1969), 3.2.6, p. 246: the
    measurable positive- and negative-derivative source sets.
    The actual derivative is retained; its already sealed
    total representative is used only to prove measurability. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP RealDerivativeRepresentative CurveArcLength
  LocallyAbsolutelyContinuousCurve PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableAlmostModification
  LebesgueScalarMeasure IntervalBumpFunctions TopologicalBorel BorelRegularMeasureUP MeasureFiniteClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [continuous_bv_actual_derivative_measurable]:
    supporting measurability of the actual f' for the
    sets A_1 and A_2 in Federer 3.2.6, p. 246.
    The proof representative agrees with every actual value
    and with the partial derivative on a conull domain. *)
Lemma continuous_bv_actual_derivative_measurable (R:realType) (f:R->R):
  curve_locally_finite_variation (f:R->real_line_metric R) ->
  continuous (f:real_line_metric R->real_line_metric R) ->
  @is_measure_measurable_function R [the choiceType of real_line_metric R]
    [the topologicalType of real_line_metric R] (@lebesgue_scalar_measure R) (real_curve_derivative f).
Proof.
move=>hBV hCont.
have hm:=lebesgue_scalar_is_measure R.
have hRep:=continuous_bv_derivative_representative_measurable hBV hCont.
apply:(@measurable_function_almost_equal R [the choiceType of real_line_metric R]
  [the topologicalType of real_line_metric R] (@lebesgue_scalar_measure R) hm
  (partial_function_total (real_derivative_representative f)) (real_curve_derivative f) hRep).
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) hm _ _ _ (bv_real_derivative_representative_ae hBV))=>x hx.
exists (real_derivative_representative f x); by split.
Qed.

(** Source for [positive_real_derivative_locus]: the actual
    derivative inequality f'(x)>0 in A_1 of Federer
    3.2.6, p. 246. Undefined derivatives are excluded. *)
Definition positive_real_derivative_locus (R:realType) (f:R->R):set (real_line_metric R):=
  partial_function_preimage (real_curve_derivative f) [set v|0<v].

(** Source for [negative_real_derivative_locus]: the actual
    derivative inequality f'(x)<0 in A_2 of Federer
    3.2.6, p. 246. Undefined derivatives are excluded. *)
Definition negative_real_derivative_locus (R:realType) (f:R->R):set (real_line_metric R):=
  partial_function_preimage (real_curve_derivative f) [set v|v<0].

(** Source for [scalar_curve_derivative_sign_loci_measurable]:
    measurability of the two derivative signs in Federer
    3.2.6, p. 246, from the actual partial graph. *)
Lemma scalar_curve_derivative_sign_loci_measurable (R:realType) (f:R->R):
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) ->
  measure_measurable (@lebesgue_scalar_measure R) (positive_real_derivative_locus f) /\
  measure_measurable (@lebesgue_scalar_measure R) (negative_real_derivative_locus f).
Proof.
move=>hAC.
have hMeas:=continuous_bv_actual_derivative_measurable
  (locally_absolutely_continuous_curve_finite_variation hAC)
  (locally_absolutely_continuous_curve_continuous hAC).
split.
- exact (measurable_function_open_preimage hMeas (@open_gt R 0)).
- exact (measurable_function_open_preimage hMeas (@open_lt R 0)).
Qed.

(** Source for [scalar_positive_derivative_set]: the set
    A_1={x:a<x<b,f'(x)>0} in Federer 3.2.6, p. 246. *)
Definition scalar_positive_derivative_set (R:realType) (f:R->R) (a b:R):=
  (`]a,b[:set (real_line_metric R)) `&` positive_real_derivative_locus f.

(** Source for [scalar_negative_derivative_set]: the set
    A_2={x:a<x<b,f'(x)<0} in Federer 3.2.6, p. 246. *)
Definition scalar_negative_derivative_set (R:realType) (f:R->R) (a b:R):=
  (`]a,b[:set (real_line_metric R)) `&` negative_real_derivative_locus f.

(** Source for [scalar_nonsigned_derivative_remainder]: the
    exact remaining set A_3=[a,b] minus (A_1 union A_2)
    in Federer 3.2.6, p. 246, including both endpoints. *)
Definition scalar_nonsigned_derivative_remainder (R:realType) (f:R->R) (a b:R):=
  (`[a,b]:set (real_line_metric R)) `\`
    (scalar_positive_derivative_set f a b `|` scalar_negative_derivative_set f a b).

(** Source for [scalar_derivative_interval_sets_measurable]:
    measurability of the three exact sets A_1,A_2,A_3
    in Federer 3.2.6, p. 246. All endpoints and
    degenerate or empty intervals retain their conventions. *)
Lemma scalar_derivative_interval_sets_measurable (R:realType) (f:R->R) a b:
  is_locally_absolutely_continuous_curve (f:R->real_line_metric R) ->
  measure_measurable (@lebesgue_scalar_measure R) (scalar_positive_derivative_set f a b) /\
  measure_measurable (@lebesgue_scalar_measure R) (scalar_negative_derivative_set f a b) /\
  measure_measurable (@lebesgue_scalar_measure R) (scalar_nonsigned_derivative_remainder f a b).
Proof.
move=>hAC; have hm:=lebesgue_scalar_is_measure R.
have hSigns:=scalar_curve_derivative_sign_loci_measurable hAC.
have hOpen:measure_measurable (@lebesgue_scalar_measure R) (`]a,b[:set (real_line_metric R)).
  have ho:open (`]a,b[:set (real_line_metric R)) by exact:interval_open.
  exact (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R) _ (open_borel_set ho)).
have hClosed:measure_measurable (@lebesgue_scalar_measure R) (`[a,b]:set (real_line_metric R)).
  exact (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hm (lebesgue_scalar_borel_regular R) _
    (closed_borel_set (@segment_closed_real R a b))).
have hP:=measure_measurable_intersection hm hOpen hSigns.1.
have hN:=measure_measurable_intersection hm hOpen hSigns.2.
split; first exact hP; split; first exact hN.
exact (measure_measurable_difference hm hClosed (measure_measurable_union hm hP hN)).
Qed.
