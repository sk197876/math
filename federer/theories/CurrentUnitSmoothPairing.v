(** Federer (1969), 4.1.7, pp. 358–359:
    the original unit density can be paired
    with an actual smooth covector field.
    Measurability is the earlier variable-pairing
    theorem 2.5.12, p. 105; compact bounds
    follow from continuity of the same field. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import PartialFunctionPreimages RealMetricBackground Hom RealNormUP NormMetric NormMetricContinuity NormClassZeroTopology
  NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing CurrentDomain
  CurrentCoefficientNorms CurrentCoefficientCompleteness CurrentSpaces CurrentMultivectorDual
  MultivectorDualSealed SmoothFunctionSpaceUP SmoothFunctionSpaceLaws OpenFamilyTopologyMathcomp
  ContinuousDualUP AbstractDualWeakEncoding WeakDualScalarEvaluation WeakEvaluationMeasurableCoordinates
  VectorDaniellHypotheses VectorDaniellRationalSpan VectorDaniellDualExtension MeasurableDualPairing
  PartialFunctionBasic MeasureUP MeasureAlmostBasic RadonMeasureUP RadonBorelRegularity
  MeasurableFunctionUP SummableRealFunctionUP CompactMaximum ContinuousRadonFieldLocalIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentUnitSmoothPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y := (A_m X R^o m).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation D := (exterior_power X m).
Local Notation DN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation UT := (current_domain R n U).
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation ev := (@current_smooth_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Variable xi:UT->D.
Hypothesis hUnit:forall x,DN (xi x)<=1.

(** Source for [current_unit_smooth_pairing_continuous_field]:
    the original smooth field is continuous
    on the actual subspace U, supporting
    the use of 2.5.12 in Federer
    4.1.7, pp. 358–359. *)
Lemma current_unit_smooth_pairing_continuous_field (psi:E):
  continuous (fun x:UT=>(ev psi (set_val x):real_norm_metric_space hNY)).
Proof.
exact:(@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U (ev psi)
  (norm_class_continuous (smooth_function_evaluation_smooth hE psi 0%N))).
Qed.

(** Source for [current_unit_smooth_pairing_measurable]:
    pairing the actual unit weak density
    with any original smooth field is
    measurable, supporting Federer 4.1.7,
    pp. 358–359. Neither compact support
    nor a global field bound is required. *)
Theorem current_unit_smooth_pairing_measurable
    (mu:set UT->\bar R) (hm:is_measure mu) (hr:is_radon_measure mu):
  is_measure_measurable_function mu
    (partial_function_total (fun x=>(xi x:open_family_topological_space
      (@current_multivector_weak_laws R n m).1)))->
  forall psi:E,is_measure_measurable_function mu
    (real_total_integrand (fun x=>pairing (xi x) (ev psi (set_val x)))).
Proof.
move=>hXi psi.
have [B hB]:=rational_dense_subspace_exists (@current_form_separable R h2 n m).
have hActualUnit x:dual_unit_ball hNY (fun y=>ed (xi x) y).
  apply/dual_unit_ball_bound;split.
  - exact:(set_valP (@abstract_dual_weak_point R Y NY hNY D ed DN hDual (xi x))).
  - exact:(@unit_dual_scalar_evaluation_bound R UT Y NY hNY D ed DN hDual xi hUnit x).
have hField:is_measure_measurable_function mu
    (partial_function_total (fun x:UT=>(ev psi (set_val x):real_norm_metric_space hNY))).
  exact ((@continuous_radon_field_locally_summable R UT Y NY hNY mu hm hr
    (fun x=>ev psi (set_val x)) (@current_unit_smooth_pairing_continuous_field psi)).1).
have hCoord y (_:B y):is_measure_measurable_function mu
    (partial_function_total (fun x=>(ed (xi x) y:real_line_metric R))).
  exact:(@weak_evaluation_measurable_coordinates R UT Y D (fun a y=>ed a y)
    (@current_multivector_weak_opens R n m) (@current_multivector_weak_laws R n m)
    mu hm xi hXi y).
have hResult:=@measurable_unit_dual_pairing R UT Y NY hNY B hB mu hm
  (fun x y=>ed (xi x) y) hActualUnit (fun x=>ev psi (set_val x)) hCoord hField.
have hValues:(fun x:UT=>ed (xi x) (ev psi (set_val x)))=
    (fun x=>pairing (xi x) (ev psi (set_val x))).
  apply:funext=>x;exact:MultivectorDual.laws.
by rewrite hValues in hResult.
Qed.

(** Source for [current_unit_smooth_pairing_compact_bound]:
    the same original scalar pairing is
    bounded on every compact subset of U,
    supporting local mass integrability of the
    actual exterior image density in Federer
    4.1.7, p. 359. The density may
    be only measurable. *)
Theorem current_unit_smooth_pairing_compact_bound (psi:E) (K:set UT):compact K->
  exists M:R,0<=M /\forall x,K x->`|pairing (xi x) (ev psi (set_val x))|<=M.
Proof.
move=>hK.
have hNorm:continuous (fun x:UT=>(NY (ev psi (set_val x)):real_line_metric R)).
  move=>x;exact:(continuous_comp (@current_unit_smooth_pairing_continuous_field psi x)
    (@real_norm_metric_norm_continuous R Y NY hNY (ev psi (set_val x)))).
case:(pselect (K !=set0))=>hNonempty.
- have [a [ha hMaximum]]:=@continuous_compact_maximum R UT K
    (fun x=>NY (ev psi (set_val x))) hNonempty hK hNorm.
  exists (NY (ev psi (set_val a)));split.
  + exact:real_seminorm_nonnegative hNY.1 _.
  + move=>x hx.
    have hBound:=@unit_dual_scalar_evaluation_bound R UT Y NY hNY D ed DN hDual
      xi hUnit x (ev psi (set_val x)).
    rewrite MultivectorDual.laws in hBound.
    exact:(le_trans hBound (hMaximum x hx)).
- exists 0;split;first exact:lexx.
  move=>x hx;exact:False_ind _ (hNonempty (ex_intro _ x hx)).
Qed.
End CurrentUnitSmoothPairing.
