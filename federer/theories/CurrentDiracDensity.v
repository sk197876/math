(** Federer (1969), 4.1.7, pp. 356, 359:
    the original point mass as an
    actual zero-current. Reuse the point-mass
    integral of Chapter 2 and the
    sealed density-current existence theorem. The
    reference to 2.5.19, p. 113,
    concerns the Daniell point evaluation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingSum SimpleZeroDegree BoundedHom HomogeneousHom GradedComponents Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading ExteriorAlgebra ExteriorPowers FiniteExteriorPowers
  AlternatingForms AlternatingZero AlternatingPairing CurrentCoefficientNorms CurrentSpaces CurrentInteriorPairing
  SmoothCompactSet CurrentMultivectorDual CurrentDensityAction CurrentDensityUP CurrentDensitySealed DistributionIntegralFieldUP
  OpenFamilyTopologyMathcomp MeasurableTotalBasic PointMassMeasure PointMassRegularity PointMassIntegral
  MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [current_scalar_multivector_unit]: the
    original exterior unit in degree zero,
    supporting the measure/current identification in
    Federer 4.1.7, p. 356, by
    1.4.1, p. 17. *)
Definition current_scalar_multivector_unit (R:realType) n:exterior_power (R_n R n) 0:=
  exterior_zeroth_inclusion (R_n R n) 1.

(** Source for [current_scalar_multivector_unit_pairing]:
    its original pairing is the scalar
    coefficient of a zero-form, supporting
    Federer 4.1.7, pp. 356, 359. *)
Lemma current_scalar_multivector_unit_pairing (R:realType) n (phi:A_m (R_n R n) R^o 0):
  pairing (@current_scalar_multivector_unit R n) phi=zero_form_value phi.
Proof.
change (form_include phi (component_val (@current_scalar_multivector_unit R n))=zero_form_value phi).
rewrite /current_scalar_multivector_unit zeroth_inclusion_val /exterior_scalar scale1r.
exact:current_zero_covector_unit_value.
Qed.
Section CurrentDiracDensity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation unit := (@current_scalar_multivector_unit R n).
Variable c:X.
Local Notation mu := (@point_mass R X c).
Local Notation hm := (@point_mass_is_measure R X c).

(** Source for [point_mass_current_open_measurable]:
    the original point mass measures every
    open set, supporting its current in
    Federer 4.1.7, pp. 356, 359. *)
Lemma point_mass_current_open_measurable:
  @is_current_density_borel_measure R n mu.
Proof. move=>A _;exact:point_mass_every_set_measurable. Qed.

(** Source for [point_mass_current_density_integrable]:
    the original scalar-unit density is
    measurable and locally mass-integrable for
    the actual point mass, supporting Federer
    4.1.7, pp. 356, 359. *)
Lemma point_mass_current_density_integrable:
  @is_locally_integrable_current_density R h2 n 0%N mu (fun _=>unit).
Proof.
constructor.
- exact:(@measurable_total_constant R X
    [the topologicalType of open_family_topological_space (@current_multivector_weak_laws R n 0%N).1]
    mu hm unit).
- move=>K.
  pose g x:=if pselect (smooth_compact_carrier K x) then @current_vector_mass R h2 n 0%N unit else 0.
  exists (g c);exact:(@point_mass_real_integral R X c g).
Qed.

(** Source for [full_dirac_current]: the original
    unit point mass as an actual
    zero-current on R^n, supporting Federer
    4.1.7, p. 359. *)
Definition full_dirac_current:@full_current_space R h2 n 0%N:=
  @CurrentDensity.value R h2 n 0%N mu hm point_mass_current_open_measurable
    (fun _=>unit) point_mass_current_density_integrable.

(** Source for [full_dirac_current_evaluation]: the
    original delta_c action is evaluation of
    the scalar test at c, Federer
    4.1.7, p. 359, recalling 2.5.19. *)
Theorem full_dirac_current_evaluation psi:
  @current_value R h2 n (fun _=>True) hFull 0%N full_dirac_current psi=
    zero_form_value (@current_test_value R h2 n (fun _=>True) hFull 0%N psi c).
Proof.
have h:=@CurrentDensity.laws R h2 n 0%N mu hm point_mass_current_open_measurable
  (fun _=>unit) point_mass_current_density_integrable psi.
have hp:=@point_mass_real_integral R X c
  (fun x=>pairing unit (@current_test_value R h2 n (fun _=>True) hFull 0%N psi x)).
have he:=congr1 (@fine R) (measure_integral_unique h hp).
rewrite current_scalar_multivector_unit_pairing in he;exact:he.
Qed.
End CurrentDiracDensity.
