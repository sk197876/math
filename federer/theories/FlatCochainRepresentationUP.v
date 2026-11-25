(** Federer (1969), 4.1.19, p. 377: the
    two bounded measurable form fields represent
    alpha by the two separate original L1
    actions. The weak derivative equation, norm
    equality and almost uniqueness are conclusions,
    not laws imposed on a candidate representation. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingPairing CurrentDomain CurrentCoefficientNorms
  PartialFunctionBasic MeasureUP MeasureIntegralUP SummableRealFunctionUP
  MeasurableNormedFunctionUP FlatCurrentUnionSpace FlatCochainSpace
  CompactSummableMultivectors CurrentLonePairImageUP
  EuclideanOpenDomainMeasure FlatCochainPairFunctional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Representation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation X := (R_n R n).
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation O d := (@compact_summable_multivector_space R h2 n d U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation Y d := (A_m X R^o d).
Local Notation N d := (@current_form_comass R h2 n d).
Local Notation hN d := (@current_form_comass_real_norm R h2 n d).

(** Source for [is_bounded_measurable_current_form]:
    bounded measurable U-valued differential form
    in Federer 4.1.19, p. 377,
    with its actual degree and comass. This
    concerns total representatives on the original U. *)
Definition is_bounded_measurable_current_form d (phi : UT -> Y d) :=
  is_measurable_normed_function mu
    (partial_function_total (fun x => (phi x : real_norm_metric_space (hN d)))) /\
  exists c : R, 0 <= c /\ forall x, N d (phi x) <= c.

(** Source for [is_lone_pair_form_density]: the
    two original integral identities in Federer
    4.1.19, p. 377, for every original
    compactly supported L1 multivector field. Every
    integral must exist with the stated finite
    value. No norm identity or derivative equality
    is built into the representation predicate. *)
Definition is_lone_pair_form_density (beta : Hom P R^o)
    (phi : UT -> Y m) (psi : UT -> Y m.+1) :=
  is_bounded_measurable_current_form phi /\
  is_bounded_measurable_current_form psi /\
  (forall xi : O m, is_measure_integral mu
    (real_total_integrand (fun x => pairing (value m xi x) (phi x)))
    (beta (xi,0))%:E) /\
  forall eta : O m.+1, is_measure_integral mu
    (real_total_integrand (fun x => pairing (value m.+1 eta x) (psi x)))
    (beta (0,eta))%:E.

(** Source for [is_flat_cochain_pair_density]: the
    original two form actions for alpha in
    Federer 4.1.19, p. 377, are the
    two actions of its induced beta. Norm,
    weak derivative and uniqueness remain separate conclusions. *)
Definition is_flat_cochain_pair_density (Q : Hom P W) (alpha : A)
    (phi : UT -> Y m) (psi : UT -> Y m.+1) :=
  is_lone_pair_form_density
    (@flat_cochain_pair_functional R h2 n m U hU Q alpha) phi psi.
End Representation.
