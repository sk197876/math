(** Federer (1969), 4.1.7, p. 358: existence
    of the original current mass. The earlier
    variation supremum with majorant one supplies
    its extended-real value. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain
  DistributionVariationUP DistributionVariationExistence CurrentMassUP CurrentMassVariation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentMassExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation UT := [the choiceType of set_type (U:set (real_norm_metric_space hNX))].
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R (real_norm_metric_space hNX) U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_mass_exists]: M(T) exists
    as an extended real for every original
    current, supporting Federer 4.1.7, p. 358.
    Zero is an admissible test, including
    on the empty open set. *)
Theorem current_mass_exists (T:@current_space R h2 n U hU m):
  exists c: \bar R,@is_current_mass R h2 n m U hU T c.
Proof.
have[c hc]:=@distribution_variation_value_exists R UT Y NY hNY DT dvalues
  (action T) (fun _=>1) (fun _=>ler01).
exists c;exact:(@current_mass_variation_law R h2 n m U hU T c).2 hc.
Qed.
End CurrentMassExistence.
