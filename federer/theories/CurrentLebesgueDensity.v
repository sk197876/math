(** Federer (1969), 4.1.7, p. 356: the actual
    Lebesgue-density current and its class-one
    directional derivatives. The analytic proof is
    the integration-by-parts theorem already proved
    in 4.1.1, p. 346. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws NormClassOneUP
  NormClassOneDirectionalField InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorGrading AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentMultivectorDual MultivectorDualSealed CurrentDensityAction CurrentDensityUP CurrentDensitySealed
  CurrentDensityUniqueness CurrentDirectionalDerivative MeasureUP EuclideanLebesgueDimensions
  EuclideanDistributionMeasureContext ContinuousDualFieldLocalIntegrability DistributionIntegralByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentLebesgueDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (A_m X R^o m).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_form_comass R h2 n m).
Local Notation hNY := (@current_form_comass_real_norm R h2 n m).
Local Notation V := (exterior_power X m).
Local Notation VN := (@current_vector_mass R h2 n m).
Local Notation ed := (@MultivectorDual.evaluation R X m).
Local Notation hDual := (@current_multivector_continuous_dual R h2 n m).
Local Notation O := (@current_multivector_weak_opens R n m).
Local Notation hO := (@current_multivector_weak_laws R n m).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation E := (@current_smooth_space R h2 n (fun _=>True) hFull m).
Local Notation ev := (@current_smooth_value R h2 n (fun _=>True) hFull m).
Local Notation hE := (@current_smooth_space_laws R h2 n (fun _=>True) hFull m).
Local Notation D := (@current_smooth_derivatives R h2 n (fun _=>True) hFull m).
Local Notation hD := (@current_smooth_derivative_laws R h2 n (fun _=>True) hFull m).
Local Notation C := (@full_current_space R h2 n m).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).

(** Source for [current_lebesgue_density]: the original
    Lebesgue wedge xi for every locally
    mass-integrable measurable multivector field,
    Federer 4.1.7, p. 356. *)
Definition current_lebesgue_density (xi:X->V)
    (hField:@is_locally_integrable_current_density R h2 n m mu xi):C:=
  @CurrentDensity.value R h2 n m mu hm (@euclidean_distribution_measure_open R n) xi hField.

(** Source for [current_lebesgue_density_action]: the
    original action integral of Lebesgue wedge xi,
    Federer 4.1.7, p. 356. *)
Theorem current_lebesgue_density_action xi hField:
  is_current_density_action mu xi (@current_lebesgue_density xi hField).
Proof. exact:CurrentDensity.laws. Qed.

(** Source for [continuous_current_density_integrable]:
    a continuous multivector field satisfies every
    original local integrability requirement,
    supporting the class-one formulas in Federer
    4.1.7, p. 356. *)
Theorem continuous_current_density_integrable (xi:X->V):
  norm_class_zero NX VN (fun _=>True) xi ->
  @is_locally_integrable_current_density R h2 n m mu xi.
Proof.
exact:(@continuous_dual_field_locally_integrable R n Y NY hNY V ed VN hDual O hO xi).
Qed.

(** Source for [current_lebesgue_directional_action]:
    D_v of the current of a class-one field
    is the current of its actual directional
    derivative, Federer 4.1.7, p. 356.
    Reuse 4.1.1 without an additional
    whole-target separability hypothesis. *)
Theorem current_lebesgue_directional_action (xi:X->V) (DXi:X->Hom X V) v (T:C):
  is_current_density_action mu xi T ->
  is_norm_class_one_field NX VN (fun _=>True) xi DXi ->
  is_current_density_action mu (fun x=>DXi x v)
    (@current_directional_derivative R h2 n m (fun _=>True) hFull v T).
Proof.
move=>hAction hXi.
apply:(@current_density_distribution_action R h2 n m mu (fun x=>DXi x v) _).2.
exact:(@distribution_integral_derivative_action R X Y NX NY hNX hNY V ed VN hDual
  n (@coordinate_basis R n) (@coordinate_basisP R n) mu hm
  (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n)
  (@euclidean_distribution_measure_translation R n) xi E ev hE D hD v T DXi
  ((@current_density_distribution_action R h2 n m mu xi T).1 hAction) hXi).
Qed.

(** Source for [current_lebesgue_directional_derivative]:
    the original equality D_v(Lebesgue wedge xi)
    =Lebesgue wedge D_v xi, Federer 4.1.7,
    p. 356, with the original class-one
    hypothesis and the actual differential. *)
Theorem current_lebesgue_directional_derivative (xi:X->V) (DXi:X->Hom X V) v
    (hXi:is_norm_class_one_field NX VN (fun _=>True) xi DXi):
  @current_directional_derivative R h2 n m (fun _=>True) hFull v
    (current_lebesgue_density (continuous_current_density_integrable (norm_class_one_zero hXi)))=
  current_lebesgue_density (continuous_current_density_integrable
    (@norm_class_one_directional_continuous R X V NX VN hNX
      (@current_vector_mass_real_norm R h2 n m) (fun _=>True) xi DXi v hXi)).
Proof.
apply:(@current_density_action_unique R h2 n m mu (fun x=>DXi x v)).
- exact:current_lebesgue_directional_action (current_lebesgue_density_action _) hXi.
- exact:current_lebesgue_density_action.
Qed.
End CurrentLebesgueDensity.
