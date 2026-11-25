(** Federer (1969), 4.1.17, p. 374: variation L1 convergence
    of the original measurable differential forms gives mass
    convergence of their actual contractions. Specialise the
    existing sealed measurable multiplier and its finite bilinear
    bound; no replacement contraction is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentDomain CurrentSpaces CurrentCoefficientNorms
  CurrentCoefficientCompleteness CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentMeasurableMultiplierUP CurrentMeasurableProductCoefficients
  CurrentMeasurableProducts CurrentMeasurableMultiplierLoneBound
  CurrentMassSealed MeasureIntegralUP SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_measurable_contraction_lone_bound]: every
    original pair of locally variation-summable k-forms has the
    stated mass-error bound whenever its norm difference is
    globally summable, supporting Federer 4.1.17, p. 374.
    Both contraction degrees may be zero. No coefficient
    smoothness, boundedness or compact support is assumed. *)
Theorem current_measurable_contraction_lone_bound
    (R:realType) (h2:(1+1:R)!=0) n k p
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T:@current_space R h2 n U hU (k+p))
    (hT:@is_integration_representable_current R h2 n (k+p) U hU T):
  let mu:=@NormalisedCurrent.measure R h2 n (k+p) U hU T hT in
  let NY:=@current_form_comass R h2 n k in
  let hNY:=@current_form_comass_real_norm R h2 n k in
  exists D:R,0<=D /\
  forall (f g:current_domain R n U->A_m (R_n R n) R^o k)
      (hf:is_locally_summable_current_field hNY mu f)
      (hg:is_locally_summable_current_field hNY mu g) a,
    is_measure_integral mu (real_total_integrand
      (fun x=>NY (f x-g x))) a%:E->
    (@CurrentMass.value R h2 n p U hU
      (@current_measurable_contraction R h2 n k p U hU T hT f hf-
        @current_measurable_contraction R h2 n k p U hU T hT g hg)
      <=(D*a)%:E)%E.
Proof.
exact:(@current_measurable_multiplier_lone_bound R h2 n (k+p) p U hU
  (A_m (R_n R n) R^o k) (@current_form_comass R h2 n k)
  (@current_form_comass_real_norm R h2 n k) (@current_form_separable R h2 n k)
  (@current_density_form_contraction R h2 n k p)
  (@current_density_form_contraction_bounded R h2 n k p) T hT).
Qed.
