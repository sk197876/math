(** Federer (1969), 4.1.19, p. 377: the
    original cochain norm is the exact
    essential pair norm of any bounded
    measurable representation. The original two
    q-cost assertions identify the beta norm;
    the earlier pair result then applies. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms CurrentSpaces SmoothCompactSet
  CurrentFlatNorm FlatCurrentsUP FlatCurrentUnionSpace FlatCochainSpace
  CurrentLonePairImageUP CurrentLonePairCost FlatCochainPairFunctional
  FlatCochainRepresentationUP FlatCochainPresentationNorm
  EuclideanOpenDomainMeasure PartialFunctionBasic
  FlatCochainRepresentativeNorm LonePairFormEssentialNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CochainEssentialNorm.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Variable U : set (R_n R n).
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation X := (R_n R n).
Local Notation UT := (current_domain R n U).
Local Notation hNX :=
  (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation J := (@current_lone_pair_cost R h2 n m U hU).
Local Notation W := (@flat_current_union_space R h2 n m U hU).
Local Notation inc := (@flat_current_union_inclusion R h2 n m U hU).
Local Notation FK := (@current_flat_norm R h2 n m U hU).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU).
Local Notation A := (@flat_cochain_space R h2 n m U hU).
Local Notation N := (@flat_cochain_norm R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Variable Q : Hom P W.
Hypothesis hFirst : forall v : P,
  exists K : smooth_compact_set hNX U,
    flatK K (inc (Q v)) /\ fine (FK K (inc (Q v))) <= J v.
Hypothesis hSecond : forall (K : smooth_compact_set hNX U) (T : W),
  flatK K (inc T) -> forall delta : R, 0 < delta ->
  exists v : P, Q v=T /\ J v <= fine (FK K (inc T))+delta.

(** Source for [flat_cochain_form_density_essential_norm]:
    the flat norm of alpha equals the
    maximum of the two essential comasses
    of any bounded measurable representing pair,
    supporting the norm assertion of Federer
    4.1.19, p. 377. This supporting
    statement preserves arbitrary representatives and
    distinguishes the earlier literal global comass. *)
Theorem flat_cochain_form_density_essential_norm (alpha : A)
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  @is_flat_cochain_pair_density R h2 n m U hU Q alpha phi psi ->
  (N alpha)%:E=flat_cochain_representative_norm mu
    (@current_form_comass R h2 n m) (@current_form_comass R h2 n m.+1)
    (partial_function_total phi) (partial_function_total psi).
Proof.
move=> hDensity.
have hNorm := @flat_cochain_presentation_functional_norm R h2 n m U hU
  P J Q hFirst hSecond alpha.
exact: (@lone_pair_form_density_essential_norm R h2 n m U hU
  (@flat_cochain_pair_functional R h2 n m U hU Q alpha)
  phi psi (N alpha) hDensity hNorm).
Qed.
End CochainEssentialNorm.
