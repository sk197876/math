(** Federer (1969), 2.5.4, p. 96, last paragraph: "We observe that all Borel
    sets of R^2 are phi_2 measurable, but not all are phi_1 measurable; for
    instance R^2 cap {x : x_2 >= 0} is not phi_1 measurable. Also L_1 subset
    L_2, lambda_1 = lambda_2|L_1 hence the conclusion of 2.5.2 holds with
    both L_1, lambda_1, phi_1 and L_1, lambda_1, phi_2; of course phi_2 is
    not L_1 regular." Together with 2.5.3, p. 94: "There is usually more
    than one measure phi for which the conclusion of the preceding theorem
    holds (see 2.5.4, 2.5.14)." The theorems of
    PlaneRegularMeasureExamples.v carry an auxiliary measure L1 and the
    hypothesis L1[a, b] = b - a. Here L1 is eliminated: every K(R) regular
    measure representing the Riemann integral is the Lebesgue measure of
    2.5.17, p. 111, by the uniqueness of 2.5.3, so the statements below
    concern phi_1 and phi_2 alone. The half-plane is shown to be a Borel
    set, so the contrast of Borel measurability is one statement, and phi_1
    and phi_2 are shown to be distinct measures for which the conclusion of
    2.5.2 holds with L_1, lambda_1. The local erratum has no entry for pp.
    95–96. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground TopologicalBorel ContinuousBorelPreimages
  FunctionLatticeUP FunctionLatticeRegularityUP FunctionLatticeRegularUniqueness RealIntegralFunctionalUP
  MeasureUP CompactSupportFunctionUP CompactSupportFunctionLattice StieltjesDaniellIntegral
  LebesgueLineMeasure PlaneRegularMeasureExamples PlaneBorelMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PlaneComparison.
Variable R : realType.
Local Notation plane := (R * R)%type.
Local Notation KR := (@compactly_supported_continuous_functions R R).
Local Notation L_1 := (@first_coordinate_lattice R).
Local Notation L_2 := (@plane_continuous_lattice R).
Local Notation lambda := (@plane_section_integral R).

(** Source for [upper_half_plane]: the set R^2 cap {x : x_2 >= 0} of
    Federer 2.5.4, p. 96, last paragraph. *)
Definition upper_half_plane : set plane := [set x | 0 <= x.2].

(** Source for [upper_half_plane_borel]: R^2 cap {x : x_2 >= 0} is a
    Borel set of R^2, implicit in "not all [Borel sets] are phi_1
    measurable; for instance R^2 cap {x : x_2 >= 0}", Federer 2.5.4,
    p. 96. It is the inverse image of the closed set
    {t : 0 <= t} under the continuous second coordinate. *)
Lemma upper_half_plane_borel : borel_set upper_half_plane.
Proof.
have hsnd : continuous (snd : plane -> R) by move=> p; exact: cvg_snd.
have hc : closed [set t : R | 0 <= t] := closed_ge (y := 0).
have h := continuous_borel_preimage hsnd (closed_borel_set hc).
exact h.
Qed.

(** Source for [lebesgue_line_segment]: every K(R) regular measure L1
    representing the Riemann integral of 2.5.17, p. 111, satisfies
    L1{t : a <= t <= b} = b - a whenever a <= b; supporting
    Federer 2.5.4, pp. 95–96. The measure is the one of
    [lebesgue_line_measure_exists] by the uniqueness of 2.5.3, p. 94. *)
Lemma lebesgue_line_segment (L1 : set R -> \bar R) :
  is_measure L1 -> is_function_lattice_regular KR L1 ->
  is_real_integral_functional L1 KR (induced_daniell (fun x : R => x)) ->
  forall a b : R, a <= b -> L1 `[a, b] = (b - a)%:E.
Proof.
move=> hm hr hA a b hab.
have [L0 [hm0 [hr0 [hA0 [_ hseg]]]]] := @lebesgue_line_measure_exists R.
rewrite -(hseg a b hab).
exact: (@function_lattice_regular_representation_unique R R KR _
  (@compactly_supported_continuous_functions_lattice R R) L1 L0 hm hm0 hA hA0 hr hr0 `[a, b]).
Qed.

(** Source for [first_coordinate_half_plane_not_measurable]: "R^2 cap
    {x : x_2 >= 0} is not phi_1 measurable", Federer 2.5.4, p. 96,
    for every L_1 regular measure phi_1 representing lambda_1. The
    one-dimensional Lebesgue measure of 2.5.17, p. 111, is supplied
    internally; no hypothesis on it remains. *)
Theorem first_coordinate_half_plane_not_measurable (phi : set plane -> \bar R) :
  is_measure phi -> is_real_integral_functional phi L_1 lambda ->
  is_function_lattice_regular L_1 phi ->
  ~ measure_measurable phi upper_half_plane.
Proof.
move=> hm hA hr.
have [L1 [hm1 [hr1 [hA1 [_ hseg]]]]] := @lebesgue_line_measure_exists R.
exact: (upper_half_plane_not_measurable hm hA hr hm1 hr1 hA1 hseg).
Qed.

(** Source for [plane_continuous_not_first_regular]: "of course phi_2
    is not L_1 regular", Federer 2.5.4, p. 96, for every L_2
    regular measure phi_2 representing lambda_2, without an auxiliary
    measure L1 in the statement. *)
Theorem plane_continuous_not_first_regular (phi : set plane -> \bar R) :
  is_measure phi -> is_real_integral_functional phi L_2 lambda ->
  is_function_lattice_regular L_2 phi ->
  ~ is_function_lattice_regular L_1 phi.
Proof.
move=> hm hA hr.
have [L1 [hm1 [hr1 [hA1 [_ hseg]]]]] := @lebesgue_line_measure_exists R.
exact: (plane_continuous_measure_not_first_regular hm hA hr hm1 hr1 hA1 hseg).
Qed.

(** Source for [plane_borel_measurability_contrast]: "all Borel sets
    of R^2 are phi_2 measurable, but not all are phi_1 measurable; for
    instance R^2 cap {x : x_2 >= 0} is not phi_1 measurable", Federer
    2.5.4, p. 96, as one statement about any L_1 regular phi_1
    representing lambda_1 and any L_2 regular phi_2 representing
    lambda_2. *)
Theorem plane_borel_measurability_contrast (phi1 phi2 : set plane -> \bar R) :
  is_measure phi1 -> is_real_integral_functional phi1 L_1 lambda ->
  is_function_lattice_regular L_1 phi1 ->
  is_measure phi2 -> is_real_integral_functional phi2 L_2 lambda ->
  is_function_lattice_regular L_2 phi2 ->
  [/\ forall S : set plane, borel_set S -> measure_measurable phi2 S,
    borel_set upper_half_plane & ~ measure_measurable phi1 upper_half_plane].
Proof.
move=> hm1 hA1 hr1 hm2 hA2 hr2; split.
- exact: (plane_continuous_borel_measurable hm2 hA2 hr2).
- exact: upper_half_plane_borel.
- exact: (first_coordinate_half_plane_not_measurable hm1 hA1 hr1).
Qed.

(** Source for [plane_representing_measures_differ]: "the
    conclusion of 2.5.2 holds with both L_1, lambda_1, phi_1 and
    L_1, lambda_1, phi_2", Federer 2.5.4, p. 96, while phi_1 and
    phi_2 are different measures: this is the example announced in
    2.5.3, p. 94, "There is usually more than one measure phi for
    which the conclusion of the preceding theorem holds". The
    half-plane is phi_2 measurable but not phi_1 measurable. *)
Theorem plane_representing_measures_differ (phi1 phi2 : set plane -> \bar R) :
  is_measure phi1 -> is_real_integral_functional phi1 L_1 lambda ->
  is_function_lattice_regular L_1 phi1 ->
  is_measure phi2 -> is_real_integral_functional phi2 L_2 lambda ->
  is_function_lattice_regular L_2 phi2 ->
  [/\ is_real_integral_functional phi1 L_1 lambda,
    is_real_integral_functional phi2 L_1 lambda &
    phi1 <> phi2].
Proof.
move=> hm1 hA1 hr1 hm2 hA2 hr2; split=> //.
- exact: (plane_continuous_measure_represents_first hA2).
- move=> he.
  have [h2 hb h1] := plane_borel_measurability_contrast hm1 hA1 hr1 hm2 hA2 hr2.
  by apply: h1; rewrite he; exact: h2 _ hb.
Qed.

(** Source for [first_coordinate_lattice_nonunique_representation]:
    Federer 2.5.3, p. 94, "There is usually more than one measure
    phi for which the conclusion of the preceding theorem holds (see
    2.5.4 ...)", realised by the two measures of 2.5.4, p. 96: two
    distinct measures over R^2 represent lambda_1 on L_1. *)
Theorem first_coordinate_lattice_nonunique_representation :
  exists phi1 phi2 : set plane -> \bar R,
    [/\ is_measure phi1, is_measure phi2,
      is_real_integral_functional phi1 L_1 lambda,
      is_real_integral_functional phi2 L_1 lambda & phi1 <> phi2].
Proof.
have [phi1 [hm1 [hA1 hr1]]] := @first_coordinate_regular_measure_exists R.
have [phi2 [hm2 [hA2 hr2]]] := @plane_continuous_regular_measure_exists R.
have [_ hA2' hne] := plane_representing_measures_differ hm1 hA1 hr1 hm2 hA2 hr2.
by exists phi1, phi2; split.
Qed.

End PlaneComparison.
