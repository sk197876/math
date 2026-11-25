(** Federer (1969), 4.1.19, p. 377: the
    actual original flat cochain has bounded measurable
    form representatives, the weak equation, the exact
    pair dual norm and almost uniqueness. All pair
    presentation premises are discharged by 4.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric
  NormDifferentialUP InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct CurrentDomain CurrentCoefficientNorms CurrentSpaces
  SmoothCompactSet CurrentFlatNorm FlatCurrentsUP FlatCurrentUnionSpace
  FlatCochainSpace CurrentLonePairImageUP CurrentLonePairCost
  CurrentLonePairFlatSealed FlatCochainPairFunctional
  FlatCochainRepresentationUP FlatCochainOriginalPairCosts
  FlatCochainPresentationNorm FlatCochainBoundedFormExistence
  FlatCochainFormWeakEquation FlatCochainFormEssentialNorm
  FlatCochainFormAlmostUniqueness FlatCochainRepresentativeNorm
  CurrentWeakExteriorPairUP EuclideanOpenDomainMeasure
  PartialFunctionBasic MeasureAlmostUP RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section OriginalRepresentation.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation hJ := (@current_lone_pair_cost_seminorm R h2 n m U hU).
Local Notation Q := (@CurrentLonePairFlat.map R h2 n m U hU).
Local Notation hQ := (@CurrentLonePairFlat.laws R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation E := (@flat_cochain_evaluation R h2 n m U hU).
Local Notation F := (@flat_cochain_norm R h2 n m U hU).
Local Notation beta := (@flat_cochain_pair_functional R h2 n m U hU Q).
Local Notation density := (@is_flat_cochain_pair_density R h2 n m U hU Q).
Local Notation hFirst := (@flat_cochain_original_pair_first_cost R h2 n m U hU).
Local Notation hSecond := (@flat_cochain_original_pair_second_cost R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).

(** Source for [flat_cochain_original_pair_norm]: the
    actual induced beta has dual norm F(alpha),
    Federer 4.1.19, p. 377. The seminorm
    on the original pair space need not be definite. *)
Theorem flat_cochain_original_pair_norm (alpha : A) :
  is_real_functional_norm J (hom_as_linear (beta alpha)) (F alpha).
Proof.
exact: (@flat_cochain_presentation_functional_norm R h2 n m U hU
  P J Q hFirst hSecond alpha).
Qed.

(** Source for [flat_cochain_original_signed_supremum]: the
    literal closed-unit-ball supremum of beta in
    Federer 4.1.19, p. 377, on the
    actual original compact-index flat union. *)
Theorem flat_cochain_original_signed_supremum (alpha : A) :
  F alpha=sup [set E alpha (Q v) | v in [set v | J v<=1]].
Proof.
exact: (@flat_cochain_presentation_signed_supremum R h2 n m U hU
  P J hJ Q hFirst hSecond alpha).
Qed.

(** Source for [flat_cochain_original_form_density_exists]:
    every flat cochain has the two bounded
    measurable representatives of Federer 4.1.19,
    p. 377, on its original U. Both
    pointwise comasses are at most its actual norm;
    no finite volume or finite current mass is assumed. *)
Theorem flat_cochain_original_form_density_exists (alpha : A) :
  exists phi : UT -> A_m X R^o m,
  exists psi : UT -> A_m X R^o m.+1,
    density alpha phi psi /\
    @is_weak_current_exterior_pair R h2 n m U hU phi psi /\
    (forall x, @current_form_comass R h2 n m (phi x)<=F alpha) /\
    forall x, @current_form_comass R h2 n m.+1 (psi x)<=F alpha.
Proof.
have [phi [psi [hDensity [hPhi hPsi]]]] :=
  @flat_cochain_bounded_form_density_exists R h2 n m U hU Q hFirst alpha.
exists phi,psi; split; first exact: hDensity.
split.
- exact: (@flat_cochain_form_density_weak_equation R h2 n m U hU
    Q hQ alpha phi psi hDensity).
- by split.
Qed.

(** Source for [flat_cochain_original_form_essential_norm]:
    any bounded measurable representing pair has
    the sharp essential norm of the cochain,
    supporting Federer 4.1.19, p. 377.
    Actual null modifications of the fields are allowed. *)
Theorem flat_cochain_original_form_essential_norm (alpha : A)
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  density alpha phi psi ->
  (F alpha)%:E=flat_cochain_representative_norm mu
    (@current_form_comass R h2 n m) (@current_form_comass R h2 n m.+1)
    (partial_function_total phi) (partial_function_total psi).
Proof.
exact: (@flat_cochain_form_density_essential_norm R h2 n m U hU
  Q hFirst hSecond alpha phi psi).
Qed.

(** Source for [flat_cochain_original_form_almost_unique]:
    both original representing forms are almost
    unique, Federer 4.1.19, p. 377.
    No equality of actual total representatives is asserted. *)
Theorem flat_cochain_original_form_almost_unique (alpha : A)
    (phi phi' : UT -> A_m X R^o m)
    (psi psi' : UT -> A_m X R^o m.+1) :
  density alpha phi psi -> density alpha phi' psi' ->
  measure_almost_everywhere mu [set x | phi x=phi' x] /\
  measure_almost_everywhere mu [set x | psi x=psi' x].
Proof.
exact: (@lone_pair_form_density_almost_unique R h2 n m U hU
  (beta alpha) phi phi' psi psi').
Qed.
End OriginalRepresentation.
