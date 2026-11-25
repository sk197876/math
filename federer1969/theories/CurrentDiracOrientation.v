(** Federer (1969), 4.1.11, p. 365: the original
    orienting field of the point current is defined at
    the point and equals the scalar unit. Use the maximal
    ball-limit field of 4.1.7, p. 357, and its proved
    agreement with the actual Radon density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentDiracDensity
  CurrentDirac CurrentIntegrationCriterion NormalisedCurrentSealed CurrentDiracRadonRepresentation
  CurrentOrientationSealed CurrentOrientationAlmost PartialFunctionUP MeasureAlmostUP
  PointMassMeasure PointMassPartialIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentDiracOrientation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x.
Variable c:X.
Hypothesis hc:U c.
Local Notation D := (@dirac_current R h2 n U hU c).
Local Notation cU := (@current_dirac_domain_point R n U c hc).
Local Notation unit := (@current_scalar_multivector_unit R n).
Variable hD:@is_integration_representable_current R h2 n 0%N U hU D.

(** Source for [current_dirac_auxiliary_at_point]: the
    original normalized auxiliary field of delta_c has
    the scalar-unit value at c, supporting the cone
    estimate in Federer 4.1.11, p. 365. *)
Theorem current_dirac_auxiliary_at_point:
  @NormalisedCurrent.auxiliary_density R h2 n 0%N U hU D hD cU=unit.
Proof.
have h:=@current_dirac_density_agreement R h2 n U hU c hc hD.
rewrite (@current_dirac_variation R h2 n U hU c hc hD) in h.
exact:(@point_mass_almost_iff R (current_domain R n U) cU _).1 h.
Qed.

(** Source for [current_dirac_orientation_at_point]: the
    original maximal orienting field of delta_c is
    defined at c with value one, supporting Federer
    4.1.11, p. 365. No total extension of the orienting
    field replaces its original partial domain. *)
Theorem current_dirac_orientation_at_point:
  partial_function_graph (@CurrentOrientation.value R h2 n 0%N U hU D hD) cU unit.
Proof.
have h:=@current_orientation_normalised_agreement R h2 n 0%N U hU D hD.
rewrite (@current_dirac_variation R h2 n U hU c hc hD) in h.
have hPoint:=(@point_mass_almost_iff R (current_domain R n U) cU _).1 h.
change (partial_function_graph (@CurrentOrientation.value R h2 n 0%N U hU D hD) cU
  (@NormalisedCurrent.auxiliary_density R h2 n 0%N U hU D hD cU)) in hPoint.
by rewrite current_dirac_auxiliary_at_point in hPoint.
Qed.
End CurrentDiracOrientation.
