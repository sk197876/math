(** Federer (1969), 4.1.10, p. 364: the smooth primitive
    is the original affine homotopy integral [h#psi]_[0,1].
    Use the actual velocity and spatial differential from 4.1.9,
    p. 363, and the exact original test zero-extension values.
    On a star-shaped U all its original segment points stay in U. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates ExteriorGrading ExteriorPowers
  ExteriorMaps ExteriorHomogeneousProducts AlternatingForms AlternatingPairing CurrentSpaces
  CurrentMapDifferential CurrentOpenRestriction SmoothTestSpaces CurrentHomotopyUP
  CurrentHomotopyTimeVelocity CurrentHomotopyTransgressionVelocity CurrentAffineHomotopyDifferential
  CurrentConeHomotopySealed CurrentConeHomotopyClass CurrentConePoincare
  RealMetricBackground LebesgueScalarMeasure MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentConePrimitiveIntegral.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hOpen : forall x, U x -> norm_domain_interior NX U x.
Variable u : X.
Local Notation V := (fun _:X => True).
Local Notation A := (fun _:R => True).
Local Notation f := (fun _:X => u).
Local Notation g := (fun x:X => x).
Local Notation h := (@CurrentConeHomotopy.value R n u).
Local Notation hH := (@current_cone_ambient_homotopy R n u U hOpen).
Local Notation hU := (@current_homotopy_source_open R n n A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n n A U V f g h hH.1).
Local Notation hEV := (@current_smooth_space_laws R h2 n V hV j.+1).
Local Notation extension := (@current_open_test_extension R h2 n j.+1 U V hU hV (fun _ _ => Logic.I)).
Local Notation primitive := (@current_cone_test_primitive R h2 n j U hOpen u).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Local Notation DS t x := (@current_map_differential R n n U (@current_homotopy_slice_map R n n h t) x).
Local Notation Velocity t x := (@current_homotopy_time_velocity R n n A U h t x).
Local Notation I := (`[0,1]:set (real_line_metric R)).

(** Source for [current_cone_test_primitive_integral]: the actual
    primitive has the literal original homotopy integral, Federer
    4.1.10, p. 364. Its velocity is x-u; every coefficient is the
    given original test, not a freely chosen smooth extension. *)
Theorem current_cone_test_primitive_integral
    (psi : @current_test_space R h2 n U hU j.+1) (x:X) (hx:U x) eta :
  is_measure_subset_integral (@lebesgue_scalar_measure R) I
    (real_total_integrand (fun t =>
      pairing (exterior_product (exterior_first_inclusion X (x-u))
        (exterior_power_map (hom_as_linear (DS t x)) j eta))
        (@current_test_value R h2 n U hU j.+1 psi ((1-t)*:u+t*:x))))
    (pairing eta (@current_smooth_value R h2 n U hU j (primitive psi) x))%:E.
Proof.
pose phi := smooth_test_inclusion hEV (extension psi).
have hIntegral := @current_homotopy_transgression_velocity_integral R h2 n n j
  A U V f g h hH phi x hx eta.
have hAffine t y : A t -> U y ->
    @current_homotopy_slice_map R n n h t y=(1-t)*:f y+t*:g y.
  move=> _ _; exact: CurrentConeHomotopy.laws.
have hVelocity t : Velocity t x=x-u :=
  @current_affine_homotopy_time_velocity R n n A U V f g h hH hAffine t x Logic.I hx.
have hIntegrand :
    (fun t => pairing (exterior_product (exterior_first_inclusion X (Velocity t x))
      (exterior_power_map (hom_as_linear (DS t x)) j eta))
      (@current_smooth_value R h2 n V hV j.+1 phi (h (Point t x))))=
    (fun t => pairing (exterior_product (exterior_first_inclusion X (x-u))
      (exterior_power_map (hom_as_linear (DS t x)) j eta))
      (@current_test_value R h2 n U hU j.+1 psi ((1-t)*:u+t*:x))).
  apply: funext => t.
  change (pairing (exterior_product (exterior_first_inclusion X (Velocity t x))
    (exterior_power_map (hom_as_linear (DS t x)) j eta))
    (@current_test_value R h2 n V hV j.+1 (extension psi) (h (Point t x)))=
    pairing (exterior_product (exterior_first_inclusion X (x-u))
      (exterior_power_map (hom_as_linear (DS t x)) j eta))
      (@current_test_value R h2 n U hU j.+1 psi ((1-t)*:u+t*:x))).
  by rewrite current_open_test_extension_values hVelocity CurrentConeHomotopy.laws.
rewrite hIntegrand in hIntegral.
exact: hIntegral.
Qed.
End CurrentConePrimitiveIntegral.
