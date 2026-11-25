(** Federer (1969), 4.1.19, p. 377: the
    actual exterior derivative of a class-one form
    is an original normed measurable form on U.
    Relative continuity and the finite coefficient space
    suffice; no global bound or finite volume is needed. *)
From mathcomp Require Import functions all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormClassZeroTopology InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain
  CurrentCoefficientNorms CurrentCoefficientCompleteness
  VectorDaniellRationalSpan SeparableVectorLone
  EuclideanOpenDomainMeasure PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureAlmostBasic RadonMeasureUP RadonBorelRegularity
  MeasurableFunctionUP MeasurableNormedFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_continuous_form_normed_measurable]:
    the measurable actual derivative in the
    class-one parenthesis of Federer 4.1.19,
    p. 377, through the original
    A(mu,Y) condition of 2.3.8, p. 78.
    The source is the literal relative U-domain. *)
Theorem current_continuous_form_normed_measurable
    (R : realType) (h2 : (1+1:R)!=0) n d
    (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (phi : R_n R n -> A_m (R_n R n) R^o d) :
  norm_class_zero (inner_norm (@euclidean_inner_productP R n))
    (@current_form_comass R h2 n d) U phi ->
  is_measurable_normed_function (@euclidean_open_domain_measure R n U)
    (partial_function_total (fun x : current_domain R n U =>
      (phi (set_val x):real_norm_metric_space
        (@current_form_comass_real_norm R h2 n d)))).
Proof.
move=> hPhi.
pose X := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose UT := current_domain R n U.
pose Y := A_m X R^o d.
pose N := @current_form_comass R h2 n d.
pose hN := @current_form_comass_real_norm R h2 n d.
pose mu := @euclidean_open_domain_measure R n U.
have hMeasure := @euclidean_open_domain_measure_laws R n U hU.
pose f := fun x : UT => phi (set_val x).
have hF : continuous (fun x : UT => (f x : real_norm_metric_space hN)).
  exact: (@norm_class_zero_restriction_continuous R X Y NX N hNX hN U phi hPhi).
have hMeas : is_measure_measurable_function mu
    (partial_function_total (fun x : UT => (f x : real_norm_metric_space hN))).
  constructor.
  - rewrite partial_function_total_domain.
    exact: (@measure_almost_everywhere_true R UT mu hMeasure.1).
  - move=> V hV; rewrite partial_function_total_preimage.
    apply: (@radon_open_measurable R UT mu hMeasure.2 (f @^-1` V)).
    exact: ((@continuousP UT (real_norm_metric_space hN) f).1 hF V hV).
have [D hD] := @rational_dense_subspace_exists R Y N hN
  (@current_form_separable R h2 n d).
exact: (@measurable_separable_vector_total R UT Y N hN D hD mu hMeasure.1 f hMeas).
Qed.
