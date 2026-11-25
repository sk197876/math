(** Federer (1969), 4.1.7, p. 359:
    the original half-line current and the
    whole-line left primitive candidate. The
    one-coordinate Euclidean line is identified
    with R by the existing scalar coordinate.
    Boundary and support assertions are proved
    separately from these definitions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology num_normedtype lra.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormDifferentialUP NormOpenDomainLaws
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanOneNormDifferential ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing AlternatingIsomorphism CurrentCoefficientNorms CurrentSpaces CurrentDensityUP CurrentDensityAction
  CurrentCharacteristicDensity CurrentOpenRestriction CurrentTestValueLaws
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP RealSubsetIntegralGraph CharacteristicFunctionUP CharacteristicFunctionSealed
  SmoothFunctionSpaceUP SmoothTestEvaluation TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineCurrents.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x).
Local Notation mu := (@euclidean_lebesgue_measure R 1).
Local Notation hm := (euclidean_lebesgue_is_measure R 1).

(** Source for [current_halfline_domain]: the
    original U=(0,infinity) in the in-book
    example, Federer 4.1.7, p. 359. *)
Definition current_halfline_domain:set X:=[set x|0<x ord0].

(** Source for [current_halfline_domain_open]: the
    original half-line is open in its
    actual Euclidean norm topology, supporting
    Federer 4.1.7, p. 359. *)
Lemma current_halfline_domain_open:forall x,current_halfline_domain x->
  norm_domain_interior NX current_halfline_domain x.
Proof.
move=>x hx;exists (x ord0);split;first exact:hx.
move=>h hh.
have hAbs:`|h ord0|<x ord0 by rewrite -euclidean_one_norm_coordinate;exact:hh.
have /andP [hNegative hPositive]: -x ord0<h ord0<x ord0 by rewrite -ltr_norml.
change (is_true (0<(x+h) ord0));rewrite ffunE;lra.
Qed.

(** Source for [current_halfline_upper_set]: the
    original whole-line left interval ending
    at b, supporting the displayed S in
    Federer 4.1.7, p. 359. *)
Definition current_halfline_upper_set b:set X:=[set x|x ord0<=b].

(** Source for [current_halfline_upper_set_measurable]:
    the original left interval is Lebesgue
    measurable, supporting the actual density
    construction in Federer 4.1.7, p. 359. *)
Lemma current_halfline_upper_set_measurable b:measure_measurable mu (current_halfline_upper_set b).
Proof.
have hCoordinate:continuous (fun x:XT=>(x ord0:real_line_metric R)).
  move=>x.
  exact (@continuous_comp [the topologicalType of XT]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R 1)]
    [the topologicalType of real_line_metric R]
    (fun z:XT=>(z:inner_metric_space (@euclidean_inner_productP R 1)))
    (@euclidean_one_project R) x (@euclidean_distribution_norm_to_inner R 1 x)
    (@euclidean_one_project_continuous R x)).
have hClosed:@closed XT (current_halfline_upper_set b).
  have hRay:@closed (real_line_metric R) [set t|t<=b] by exact:closed_le.
  apply:preimage_closed hRay=>x _;exact:hCoordinate.
exact:(@euclidean_distribution_measure_borel R 1 _ (closed_borel_set hClosed)).
Qed.

(** Source for [halfline_left_primitive_candidate]:
    the actual S integrating the original
    oriented unit on (-infinity,b], Federer
    4.1.7, p. 359. This definition
    assumes no primitive or uniqueness property. *)
Definition halfline_left_primitive_candidate b:@full_current_space R h2 1 1%N:=
  @current_characteristic_density R h2 1 1%N mu hm
    (@euclidean_distribution_measure_borel R 1) (@euclidean_distribution_measure_compact_finite R 1)
    (current_halfline_upper_set b) (current_halfline_upper_set_measurable b)
    (e_lambda (@coordinate_basis R 1) (ord_tuple 1)).

(** Source for [halfline_left_primitive_candidate_action]:
    the candidate's exact original integral
    against every compact test, supporting
    Federer 4.1.7, p. 359. *)
Lemma halfline_left_primitive_candidate_action b:
  is_current_density_action mu
    (fun x=>(@CharacteristicFunction.value R X (current_halfline_upper_set b) x)*:
      e_lambda (@coordinate_basis R 1) (ord_tuple 1)) (halfline_left_primitive_candidate b).
Proof. exact:current_characteristic_density_action. Qed.

(** Source for [halfline_current]: the original
    current T on U=(0,infinity), Federer
    4.1.7, p. 359. It is the
    actual open restriction of the preceding
    integral current. *)
Definition halfline_current b:
    @current_space R h2 1 current_halfline_domain current_halfline_domain_open 1%N:=
  @current_open_restriction R h2 1 1%N current_halfline_domain (fun _=>True)
    current_halfline_domain_open hFull (fun _ _=>Logic.I) (halfline_left_primitive_candidate b).

(** Source for [halfline_current_action]: the
    original T integrates the oriented scalar
    coefficient precisely over (0,b], Federer
    4.1.7, p. 359. No arbitrary
    continuation outside U enters its value. *)
Theorem halfline_current_action b psi:
  is_measure_subset_integral mu [set x:X|0<x ord0<=b]
    (real_total_integrand (fun x=>pairing (e_lambda (@coordinate_basis R 1) (ord_tuple 1))
      (@current_test_value R h2 1 current_halfline_domain current_halfline_domain_open 1%N psi x)))
    (@current_value R h2 1 current_halfline_domain current_halfline_domain_open 1%N
      (halfline_current b) psi)%:E.
Proof.
rewrite /halfline_current current_open_restriction_evaluation.
pose P:=@current_open_test_extension R h2 1 1%N current_halfline_domain (fun _=>True)
  current_halfline_domain_open hFull (fun _ _=>Logic.I).
pose s:=@CharacteristicFunction.value R X (current_halfline_upper_set b).
have hs:=@CharacteristicFunction.laws R X (current_halfline_upper_set b).
pose z:=e_lambda (@coordinate_basis R 1) (ord_tuple 1).
pose f x:=pairing z
  (@current_test_value R h2 1 current_halfline_domain current_halfline_domain_open 1%N psi x).
pose g x:=s x*f x.
have hAction:=halfline_left_primitive_candidate_action b (P psi).
have hPoint:(fun x=>pairing (s x*:z) (@current_test_value R h2 1 (fun _=>True) hFull 1%N (P psi) x))=g.
  apply:funext=>x;rewrite current_open_test_extension_values /g /f /pairing linearZ;by [].
rewrite hPoint in hAction.
apply:(@real_subset_integral_total R X mu [set x:X|0<x ord0<=b] f g _ _ _).2 hAction.
- move=>x /andP [hx0 hxb];by rewrite /g /s (characteristic_on_set hs hxb) mul1r.
- move=>x hx.
  case:(pselect (current_halfline_domain x))=>hPositive.
  + have hOutside:~current_halfline_upper_set b x.
      move=>hxb;apply:hx;by apply/andP;split.
    by rewrite /g /s (characteristic_off_set hs hOutside) mul0r.
  + have hZero:@current_test_value R h2 1 current_halfline_domain current_halfline_domain_open 1%N psi x=0:=
      (@smooth_test_value_outside R X (A_m X R^o 1) NX
      (@current_form_comass R h2 1 1%N) hNX (@current_form_comass_real_norm R h2 1 1%N)
      current_halfline_domain (@current_smooth_space R h2 1 current_halfline_domain current_halfline_domain_open 1%N)
      (@current_smooth_value R h2 1 current_halfline_domain current_halfline_domain_open 1%N)
      (@current_smooth_space_laws R h2 1 current_halfline_domain current_halfline_domain_open 1%N) psi x hPositive).
    by rewrite /g /f hZero /pairing linear0 hom_zeroE mulr0.
Qed.
End HalflineCurrents.
