(** Federer (1969), 4.1.7, p. 358: the
    original global mass is the scalar-majorant
    supremum with majorant one. The compact
    test gauge of 4.1.5 is retained on
    its original K(U)+ domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentGlobalComassBound CurrentGlobalComassSealed CurrentMassUP ExtendedSupremumUP
  SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation DistributionVariationDomain DistributionVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentMassVariation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation NY := (@current_form_comass R h2 n m).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation ev := (@current_test_value R h2 n U hU m).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_mass_variation_values]: the
    literal global-comass constraint and the pointwise
    bound by one give the same original
    test supremum, supporting Federer 4.1.7,
    p. 358. The domain may be empty. *)
Theorem current_mass_variation_values (T:C):
  @current_mass_values R h2 n m U hU T=
    distribution_variation_values NY dvalues (action T) (fun _=>1).
Proof.
apply/seteqP;split=>a [phi [hBound hValue]];exists phi;split=>//.
- have hPoint:=(@current_global_comass_bound R h2 n m U (ev phi) 1).1 hBound.
  move=>x;exact:(hPoint (set_val x) (set_valP x)).
- apply:(@current_global_comass_bound R h2 n m U (ev phi) 1).2=>x hx.
  pose z:set_type (U:set XT):=exist _ x (mem_set hx).
  exact:(hBound z).
Qed.

(** Source for [current_mass_variation_law]: the
    original mass law is exactly the earlier
    real-test supremum law with majorant one,
    supporting Federer 4.1.7, p. 358. *)
Theorem current_mass_variation_law (T:C) c:
  @is_current_mass R h2 n m U hU T c<->
    is_distribution_variation_value NY dvalues (action T) (fun _=>1) c.
Proof.
by rewrite /is_current_mass current_mass_variation_values.
Qed.
End CurrentMassVariation.
