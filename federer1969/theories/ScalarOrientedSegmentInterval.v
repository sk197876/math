(** Federer (1969), 4.1.8, p. 362: an
    ordered scalar segment is the original E^1
    restricted to its open interval. Use the
    original coordinate identification and affine signed
    integral; both currents are actual opaque currents. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  ScalarEuclideanApproximateLimits EuclideanLebesgueDimensions EuclideanLebesgueBoxes LebesgueScalarMeasure
  ExteriorGrading ExteriorPowers FiniteExteriorPowers AlternatingForms AlternatingPairing
  CurrentSpaces CurrentDensityUP CurrentEvaluation CurrentSegmentMapUP
  OrientedSegmentCurrentUP OrientedSegmentCurrentSealed ScalarSegmentCoordinateValues
  EuclideanCharacteristicCurrent EuclideanCharacteristicRestriction ScalarPositiveAffineSegmentIntegral
  ConvexMetricSegment RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPrecomposition PartialZeroExtension
  MeasureUP MeasurePushforward PushforwardMeasurabilityTransfer MeasureIntegralUP MeasureSubsetIntegral
  MeasureIntegralGraphEquivalence MeasureIntegralUniqueness InjectiveSubsetIntegralTransport SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarOrientedSegmentInterval.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation Leb := (@euclidean_lebesgue_measure R 1%N).
Local Notation ScalarLeb := (@lebesgue_scalar_measure R).
Local Notation project := (@euclidean_one_project R).
Local Notation embed := (@euclidean_one_embed R).
Local Notation value := (@current_test_value R h2 1%N (fun _=>True) hFull 1%N).
Local Notation top := (e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N)).
Variables u v:R.
Local Notation I := (`]u,v[:set (real_line_metric R)).
Local Notation B := (project @^-1` I).

(** Source for [scalar_segment_coordinate_measure]: the
    original coordinate projection R^1 to R preserves
    Lebesgue measure, supporting the scalar interval
    identity of Federer 4.1.8, p. 362, by
    2.6.5, pp. 119–120. *)
Lemma scalar_segment_coordinate_measure:measure_pushforward project Leb=ScalarLeb.
Proof.
apply:funext=>A;exact:esym (@euclidean_one_project_measure_preimage R A).
Qed.

(** Source for [scalar_segment_interval_measurable]: the
    original open scalar interval is measurable in
    R^1, supporting Federer 4.1.8, p. 362. *)
Lemma scalar_segment_interval_measurable:measure_measurable Leb B.
Proof.
apply:(@measure_pushforward_preimage_measurable R X (real_line_metric R) project Leb I
  (can_inj (@euclidean_one_projectK R))).
rewrite scalar_segment_coordinate_measure;exact:lebesgue_scalar_open_interval_measurable.
Qed.
Local Notation C := (@euclidean_characteristic_current R h2 1%N B scalar_segment_interval_measurable).
Local Notation S := (@OrientedSegmentCurrent.value R h2 1%N (fun _=>True) hFull
  (embed u) (embed v) (@scalar_segment_full_domain R u v)).

(** Source for [scalar_characteristic_interval_action]: the
    actual coordinate characteristic current has the
    original scalar open-interval integral for every
    original one-form test, supporting Federer 4.1.8,
    p. 362. *)
Theorem scalar_characteristic_interval_action phi:
  is_measure_subset_integral ScalarLeb I
    (real_total_integrand (fun s=>pairing top (value phi (embed s))))
    (@current_value R h2 1%N (fun _=>True) hFull 1%N C phi)%:E.
Proof.
pose g s:=pairing top (value phi (embed s)).
pose f x:=pairing top (value phi x).
have hI:=@euclidean_characteristic_current_action R h2 1%N B scalar_segment_interval_measurable phi.
have hIff:=@injective_image_subset_integral_iff R X (real_line_metric R) Leb ScalarLeb
  (euclidean_lebesgue_is_measure R 1%N) project I (real_total_integrand g)
  (@current_value R h2 1%N (fun _=>True) hFull 1%N C phi)%:E
  (can_inj (@euclidean_one_projectK R)) scalar_segment_coordinate_measure.
apply:hIff.2.
apply:(measure_integral_graph_equivalent _ hI)=>x z.
have hInner:partial_function_graph (real_total_integrand f) x z <->
    partial_function_graph (partial_function_precompose project (real_total_integrand g)) x z.
  change (partial_function_graph (real_total_integrand f) x z <->
    partial_function_graph (real_total_integrand g) (project x) z).
  by rewrite !real_total_integrand_graph /f /g euclidean_one_projectK.
by rewrite !partial_function_zero_extension_graph hInner.
Qed.

(** Source for [scalar_oriented_segment_interval_current]: the
    original ordered segment current equals the actual
    coordinate-oriented characteristic current of its open
    interval, supporting Federer 4.1.8, p. 362. *)
Theorem scalar_oriented_segment_interval_current:u<v->S=C.
Proof.
move=>huv;apply:(@current_values_extensional R h2 1%N 1%N (fun _=>True) hFull)=>phi.
have hInterval:=scalar_characteristic_interval_action phi.
have hAffine:=@scalar_positive_affine_segment_integral R
  (fun s=>pairing top (value phi (embed s))) u v
  (@current_value R h2 1%N (fun _=>True) hFull 1%N C phi) huv hInterval.
have hAction:=@OrientedSegmentCurrent.laws R h2 1%N (fun _=>True) hFull
  (embed u) (embed v) (@scalar_segment_full_domain R u v) phi.
have hFunction:(fun t=>pairing (exterior_first_inclusion X (embed v-embed u))
    (value phi (metric_segment_point (embed u) (embed v) t)))=
    (fun t=>(v-u)*pairing top (value phi (embed ((v-u)*t+u)))).
  apply:funext=>t;by rewrite scalar_segment_velocity scalar_segment_parameter_value /pairing linearZ.
rewrite hFunction in hAction.
exact:(EFin_inj (measure_integral_unique hAction hAffine)).
Qed.

(** Source for [scalar_oriented_segment_interval_action]: the
    original [u,v](alpha) equals the integral from
    u to v of <1,alpha(s)>, the final
    scalar display in Federer 4.1.8, p. 362. *)
Theorem scalar_oriented_segment_interval_action:u<v->forall phi,
  is_measure_subset_integral ScalarLeb I
    (real_total_integrand (fun s=>pairing top (value phi (embed s))))
    (@current_value R h2 1%N (fun _=>True) hFull 1%N S phi)%:E.
Proof.
move=>huv phi;rewrite (scalar_oriented_segment_interval_current huv).
exact:scalar_characteristic_interval_action.
Qed.

(** Source for [scalar_oriented_segment_interval_restriction]:
    the original [u,v]=E^1 contracted {s:u<s<v},
    exactly the final one-factor assertion of Federer
    4.1.8, p. 362. The right-hand side is
    the actual original measurable restriction operation. *)
Theorem scalar_oriented_segment_interval_restriction:u<v->
  S=@euclidean_fundamental_restricted_current R h2 1%N B scalar_segment_interval_measurable.
Proof.
move=>huv;rewrite (scalar_oriented_segment_interval_current huv).
exact:euclidean_characteristic_current_restriction.
Qed.
End ScalarOrientedSegmentInterval.
