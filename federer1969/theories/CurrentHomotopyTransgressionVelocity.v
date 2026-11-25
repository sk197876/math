(** Federer (1969), 4.1.9, p. 363: identify the original
    homotopy-form integral with its printed h-dot_t and Dh_t
    expression. Reuse the actual pullback, exterior differential
    image and literal interval integral laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology normedtype ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading ExteriorPowers ExteriorMaps ExteriorHomogeneousProducts AlternatingForms AlternatingPairing
  AlternatingDual CurrentSpaces CurrentMapDifferential CurrentCartesianDomain CurrentCartesianVectorProduct
  SmoothFormPullbackUP SmoothFormPullbackSealed CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeVelocity CurrentHomotopyExteriorDifferential CurrentHomotopyTransgressionUP
  CurrentHomotopyTransgressionSealed ScalarSegmentCoordinateValues ConvexMetricSegment
  RealMetricBackground LebesgueScalarMeasure PartialFunctionUP PartialZeroExtension
  MeasureIntegralUP MeasureSubsetIntegral MeasureIntegralGraphEquivalence SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentHomotopyTransgressionVelocity.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation E := (@current_smooth_space R h2 n U hU j).
Local Notation F := (@current_smooth_space R h2 nu V hV (1+j)).
Local Notation ev := (@current_smooth_value R h2 n U hU j).
Local Notation fv := (@current_smooth_value R h2 nu V hV (1+j)).
Local Notation Pull := (@SmoothFormPullback.operator R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2).
Local Notation pv := (@current_smooth_value R h2 (1+n)%N AU hAU (1+j)).
Local Notation K := (@CurrentHomotopyTransgression.value R h2 n nu j A U V f g h hHomotopy).
Local Notation Integrand := (@current_homotopy_transgression_integrand R h2 n nu j A U V f g h hHomotopy).
Local Notation I := (`[0,1]:set (real_line_metric R)).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Local Notation DH t x := (@current_map_differential R (1+n)%N nu AU h (Point t x)).
Local Notation DS t x := (@current_map_differential R n nu U (@current_homotopy_slice_map R n nu h t) x).
Local Notation Velocity t x := (@current_homotopy_time_velocity R n nu A U h t x).

(** Source for [current_homotopy_transgression_integrand_velocity]:
    the original time integrand is the pairing of psi(h(t,x))
    with h-dot_t(x) wedge Lambda_j Dh_t(x) eta, supporting
    the homotopy formula for forms in Federer 4.1.9, p. 363. *)
Theorem current_homotopy_transgression_integrand_velocity (psi:F) x eta t:
  U x->I t->Integrand psi x eta t=
    pairing (exterior_product (exterior_first_inclusion Y (Velocity t x))
      (exterior_power_map (hom_as_linear (DS t x)) j eta)) (fv psi (h (Point t x))).
Proof.
move=>hx ht.
have hAt:A t:=@current_homotopy_closed_time_band R A hInterval t ht.
have hPoint:=@current_homotopy_join_member R n A U t x hAt hx.
have hPull:=@smooth_form_pullback_values R (1+n)%N nu (1+j) AU V F
  (@current_smooth_space R h2 (1+n)%N AU hAU (1+j)) fv pv h Pull
  (@SmoothFormPullback.laws R h2 (1+n)%N nu (1+j) AU V hAU hV h image hHomotopy.2)
  psi (Point t x) (DH t x) hPoint
  (@current_map_differential_actual R (1+n)%N nu AU h hHomotopy.2 (Point t x) hPoint).
have hClass:@is_current_homotopy_class R n nu A U V f g h 1%N:=conj geometry (hHomotopy.2 1%N).
have hPath:metric_segment_point (@euclidean_one_embed R 0) (@euclidean_one_embed R 1) t=euclidean_one_embed t.
  rewrite scalar_segment_parameter_value;congr (euclidean_one_embed _);ring.
rewrite /current_homotopy_transgression_integrand hPath.
rewrite hPull A_m_dual_pairing.
by rewrite (@current_homotopy_exterior_differential R n nu j A U V f g h hClass t x eta hAt hx).
Qed.

(** Source for [current_homotopy_transgression_velocity_integral]:
    the actual opaque homotopy form has exactly the printed
    velocity/spatial-derivative interval integral, supporting
    Federer 4.1.9, p. 363, for every original point,
    multivector and actual smooth target form. *)
Theorem current_homotopy_transgression_velocity_integral (psi:F) x (hx:U x) eta:
  is_measure_subset_integral (@lebesgue_scalar_measure R) I
    (real_total_integrand (fun t=>
      pairing (exterior_product (exterior_first_inclusion Y (Velocity t x))
        (exterior_power_map (hom_as_linear (DS t x)) j eta)) (fv psi (h (Point t x)))))
    (pairing eta (ev (K psi) x))%:E.
Proof.
have hIntegral:=@CurrentHomotopyTransgression.laws R h2 n nu j A U V f g h hHomotopy psi x hx eta.
apply:(@measure_integral_graph_equivalent R (real_line_metric R) (@lebesgue_scalar_measure R)
  _ _ _ _ hIntegral)=>t z.
rewrite !partial_function_zero_extension_graph.
split;move=>[[ht hv]|[hn hz]].
- left;split=>//;move:hv.
  by rewrite !real_total_integrand_graph (@current_homotopy_transgression_integrand_velocity psi x eta t hx ht).
- right;by split.
- left;split=>//;move:hv.
  by rewrite !real_total_integrand_graph (@current_homotopy_transgression_integrand_velocity psi x eta t hx ht).
- right;by split.
Qed.
End CurrentHomotopyTransgressionVelocity.
