(** Federer (1969), 2.5.11, p. 102: the example showing that the answer to
    the question of 2.5.10 is in general negative. For j in {1,2}, Y_j is a
    set of cardinal aleph_j, alpha_j is the counting measure over Y_j, and
    beta_j is the measure vanishing on the sets of cardinal less than
    aleph_j and equal to one on the sets of cardinal aleph_j. Over X=Y_1 x
    Y_2 the product measures alpha_1 x beta_2 and beta_1 x alpha_2 of 2.6.1
    define the lattice L=L_1(alpha_1 x beta_2) meet L_1(beta_1 x alpha_2),
    corrected by the erratum p. 2, book p. 102 line 8, and the functionals
    lambda and mu. The carriers Y_j are types; "card Y_j = aleph_j" is
    expressed by the successor specification of CardinalSuccessorUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CardinalSuccessorUP CardinalMeasureUP CardinalMeasureLaws
  MeasureUP MeasureBasic MeasureSplit CountingMeasure NonnegativeSumSupport
  ProductMeasureUP ProductMeasure ProductRectangleValue ProductRectangleMeasurability
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureCharacteristicIntegral
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralGraphEquivalence MeasureDensityNullSets
  SummableRealFunctionUP SummableRealFunctionLattice SummableRealArithmetic
  FunctionLatticeUP MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellIntegralUP
  MonotoneDaniellIntegralSum RealIntegralFunctionalUP RealIntegralFunctional
  FunctionLatticeRegularityUP RegularDaniellRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

Section Example.
Variable R : realType.
Variables J1 J2 : choiceType.
Hypothesis h1 : is_cardinal_successor (@setT nat) (@setT J1).
Hypothesis h2 : is_cardinal_successor (@setT J1) (@setT J2).

(** Source for [example_beta1]: the measure beta_1 over Y_1 in
    Federer 2.5.11, p. 102, with aleph_1 represented by Y_1 itself,
    so that the sets of smaller cardinal are the countable sets. *)
Definition example_beta1 : set J1 -> \bar R := cardinal_measure R (@setT nat).

(** Source for [example_beta2]: the measure beta_2 over Y_2 in
    Federer 2.5.11, p. 102; the sets of cardinal less than aleph_2
    are those injecting into Y_1. *)
Definition example_beta2 : set J2 -> \bar R := cardinal_measure R (@setT J1).

(** Source for [example_beta1_measure]: beta_1 measures Y_1,
    Federer 2.5.11, p. 102; countable unions of countable sets
    are countable. *)
Lemma example_beta1_measure : is_measure example_beta1.
Proof. exact (@cardinal_measure_is_measure R J1 nat setT (@countable_sigma_small J1)). Qed.

(** Source for [example_beta2_measure]: beta_2 measures Y_2,
    Federer 2.5.11, p. 102; countable unions of sets of cardinal
    at most aleph-one have cardinal at most aleph-one. *)
Lemma example_beta2_measure : is_measure example_beta2.
Proof. exact (@cardinal_measure_is_measure R J2 J1 setT (@aleph_one_sigma_small J1 J2 setT h1)). Qed.

(** Source for [example_nu1]: the product measure alpha_1 x beta_2
    of Federer 2.5.11, p. 102, formed as in 2.6.1, p. 114. *)
Definition example_nu1 : set (J1 * J2) -> \bar R :=
  product_measure (counting_measure_is_measure R J1) example_beta2_measure.

(** Source for [example_nu2]: the product measure beta_1 x alpha_2
    of Federer 2.5.11, p. 102, formed as in 2.6.1, p. 114. *)
Definition example_nu2 : set (J1 * J2) -> \bar R :=
  product_measure example_beta1_measure (counting_measure_is_measure R J2).

(** Source for [example_nu1_measure]: alpha_1 x beta_2 measures X,
    Federer 2.6.1, p. 115, used in 2.5.11, p. 102. *)
Lemma example_nu1_measure : is_measure example_nu1.
Proof. exact: (product_measure_measure_law (product_measure_specification _ _)). Qed.

(** Source for [example_nu2_measure]: beta_1 x alpha_2 measures X,
    Federer 2.6.1, p. 115, used in 2.5.11, p. 102. *)
Lemma example_nu2_measure : is_measure example_nu2.
Proof. exact: (product_measure_measure_law (product_measure_specification _ _)). Qed.

(** Source for [example_lattice]: the function lattice
    L=L_1(alpha_1 x beta_2) meet L_1(beta_1 x alpha_2) of Federer
    2.5.11, p. 102, with the total-domain reading of the erratum,
    p. 2, book p. 102 line 8. *)
Definition example_lattice : set (J1 * J2 -> R) :=
  [set f | summable_real_functions example_nu1 f /\ summable_real_functions example_nu2 f].

(** Source for [example_lattice_is_lattice]: L is a lattice of
    functions, Federer 2.5.11, p. 102, by 2.5.1, p. 91: an
    intersection of two summable lattices. *)
Lemma example_lattice_is_lattice : is_function_lattice example_lattice.
Proof.
have hA := summable_real_functions_lattice example_nu1_measure.
have hB := summable_real_functions_lattice example_nu2_measure.
constructor.
- move=> f g [hf1 hf2] [hg1 hg2].
  by split; [exact: (function_lattice_add hA hf1 hg1)|exact: (function_lattice_add hB hf2 hg2)].
- move=> c f hc [hf1 hf2].
  by split; [exact: (function_lattice_scale hA hc hf1)|exact: (function_lattice_scale hB hc hf2)].
- move=> f g [hf1 hf2] [hg1 hg2].
  by split; [exact: (function_lattice_minimum hA hf1 hg1)|exact: (function_lattice_minimum hB hf2 hg2)].
- move=> c f hc [hf1 hf2].
  by split; [exact: (function_lattice_truncation hA hc hf1)|exact: (function_lattice_truncation hB hc hf2)].
- move=> f g [hf1 hf2] [hg1 hg2] hfg.
  by split; [exact: (function_lattice_ordered_difference hA hf1 hg1 hfg)
            |exact: (function_lattice_ordered_difference hB hf2 hg2 hfg)].
Qed.

(** Source for [example_lattice_summable1]: members of L are
    alpha_1 x beta_2 summable, Federer 2.5.11, p. 102. *)
Lemma example_lattice_summable1 : example_lattice `<=` summable_real_functions example_nu1.
Proof. by move=> f [h _]. Qed.

(** Source for [example_lattice_summable2]: members of L are
    beta_1 x alpha_2 summable, Federer 2.5.11, p. 102. *)
Lemma example_lattice_summable2 : example_lattice `<=` summable_real_functions example_nu2.
Proof. by move=> f [_ h]. Qed.

(** Source for [example_integral1]: the integral functional
    f mapped to integral f d(alpha_1 x beta_2) on L in Federer 2.5.11,
    p. 102, which is also the functional mu. *)
Definition example_integral1 : (J1 * J2 -> R) -> R :=
  lattice_measure_integral example_lattice_summable1.

(** Source for [example_integral2]: the integral functional
    f mapped to integral f d(beta_1 x alpha_2) on L in Federer 2.5.11,
    p. 102. *)
Definition example_integral2 : (J1 * J2 -> R) -> R :=
  lattice_measure_integral example_lattice_summable2.

(** Source for [example_integral1_spec]: the integral law of the
    first summand of lambda in Federer 2.5.11, p. 102. *)
Lemma example_integral1_spec :
  is_real_integral_functional example_nu1 example_lattice example_integral1.
Proof. exact: lattice_measure_integral_specification. Qed.

(** Source for [example_integral2_spec]: the integral law of the
    second summand of lambda in Federer 2.5.11, p. 102. *)
Lemma example_integral2_spec :
  is_real_integral_functional example_nu2 example_lattice example_integral2.
Proof. exact: lattice_measure_integral_specification. Qed.

(** Source for [example_lambda]: the linear functional lambda on L
    displayed in Federer 2.5.11, p. 102. *)
Definition example_lambda (f : J1 * J2 -> R) : R := example_integral1 f+example_integral2 f.

(** Source for [example_mu]: the linear functional mu on L displayed
    in Federer 2.5.11, p. 102. *)
Definition example_mu : (J1 * J2 -> R) -> R := example_integral1.

(** Source for [example_lambda_monotone_daniell]: lambda is a monotone
    Daniell integral on L, as required for the L regular measure in
    Federer 2.5.11, p. 102, by 2.5.1, p. 92. *)
Lemma example_lambda_monotone_daniell :
  is_monotone_daniell_integral example_lattice example_lambda.
Proof.
apply: monotone_daniell_integral_sum.
- exact (real_integral_functional_is_monotone_daniell example_nu1_measure
    example_lattice_is_lattice example_integral1_spec).
- exact (real_integral_functional_is_monotone_daniell example_nu2_measure
    example_lattice_is_lattice example_integral2_spec).
Qed.

(** Source for [example_mu_monotone_daniell]: mu is a monotone Daniell
    integral on L, Federer 2.5.11, p. 102, by 2.5.1, p. 92. *)
Lemma example_mu_monotone_daniell :
  is_monotone_daniell_integral example_lattice example_mu.
Proof.
exact (real_integral_functional_is_monotone_daniell example_nu1_measure
  example_lattice_is_lattice example_integral1_spec).
Qed.

(** Source for [example_mu_daniell]: mu is a Daniell integral on L
    in the sense of 2.5.5, as presupposed by the comparison with 2.5.9
    in Federer 2.5.11, p. 102. *)
Lemma example_mu_daniell : is_daniell_integral example_lattice example_mu.
Proof. exact (monotone_daniell_integral_is_daniell example_mu_monotone_daniell). Qed.

(** Source for [example_lattice_absolute]: the absolute value of a
    member of L belongs to L, supporting the inequality
    mu(|f|) <= lambda(|f|) in Federer 2.5.11, p. 102. *)
Lemma example_lattice_absolute (f : J1 * J2 -> R) :
  example_lattice f -> example_lattice (fun x => `|f x|%R).
Proof.
move=> [hf1 hf2]; split.
- exact (summable_real_absolute example_nu1_measure hf1).
- exact (summable_real_absolute example_nu2_measure hf2).
Qed.

(** Source for [example_mu_dominated]: the inequality
    mu(|f|) <= lambda(|f|) for f in L, called clear in Federer 2.5.11,
    p. 102; the second integral of |f| is nonnegative. *)
Lemma example_mu_dominated (f : J1 * J2 -> R) :
  example_lattice f -> (example_mu (fun x => `|f x|%R) <= example_lambda (fun x => `|f x|%R))%R.
Proof.
move=> hf; rewrite /example_lambda /example_mu lerDl.
apply: (@monotone_daniell_integral_nonnegative R _ example_lattice _ example_lattice_is_lattice
  (real_integral_functional_is_monotone_daniell example_nu2_measure
    example_lattice_is_lattice example_integral2_spec) _ (example_lattice_absolute hf)).
by move=> x; exact: normr_ge0.
Qed.

(** Source for [example_summable_zero]: the zero function is summable
    for every measure, supporting nonemptiness of L in Federer 2.5.11,
    p. 102, by 2.4.4(1), p. 82. *)
Lemma example_summable_zero (X : choiceType) (nu : set X -> \bar R) :
  is_measure nu -> summable_real_functions nu (fun _ : X => 0%R).
Proof.
move=> hn; exists 0%R.
apply: measure_integral_graph_equivalent (measure_extended_zero_integral hn)=> x y.
by rewrite real_total_integrand_graph.
Qed.

(** Source for [example_lattice_zero]: L contains the zero function,
    so that the L regular measure of Federer 2.5.3 exists for the
    functional lambda of 2.5.11, p. 102. *)
Lemma example_lattice_zero : example_lattice (fun _ => 0%R).
Proof.
split; [exact (example_summable_zero example_nu1_measure)
       |exact (example_summable_zero example_nu2_measure)].
Qed.

(** Source for [example_regular_measure_exists]: existence of the L
    regular measure phi associated with lambda in Federer 2.5.11,
    p. 102, by 2.5.3, p. 94. Uniqueness among L regular representing
    measures is part of the cited theorem. *)
Theorem example_regular_measure_exists : exists phi : set (J1 * J2) -> \bar R,
  is_measure phi /\ is_real_integral_functional phi example_lattice example_lambda /\
  is_function_lattice_regular example_lattice phi.
Proof.
have [phi [hm [hi [hr _]]]] := monotone_daniell_regular_representation
  example_lattice_is_lattice example_lambda_monotone_daniell
  (ex_intro _ _ example_lattice_zero).
by exists phi.
Qed.

(** Source for [example_beta1_whole]: beta_1(Y_1)=1 in Federer 2.5.11,
    p. 102, since Y_1 is uncountable. *)
Lemma example_beta1_whole : example_beta1 setT = 1.
Proof. exact (cardinal_measure_whole R h1.2.1). Qed.

(** Source for [example_beta2_whole]: beta_2(Y_2)=1 in Federer 2.5.11,
    p. 102, since Y_2 has cardinal aleph_2. *)
Lemma example_beta2_whole : example_beta2 setT = 1.
Proof. exact (cardinal_measure_whole R h2.2.1). Qed.

(** Source for [example_beta1_singleton]: a point of Y_1 is beta_1
    null, Federer 2.5.11, p. 102. *)
Lemma example_beta1_singleton (u : J1) : example_beta1 [set u] = 0.
Proof. exact (cardinal_measure_small R (countable1 u)). Qed.

(** Source for [example_beta2_singleton]: a point of Y_2 is beta_2
    null, Federer 2.5.11, p. 102. *)
Lemma example_beta2_singleton (v : J2) : example_beta2 [set v] = 0.
Proof. exact (cardinal_measure_small R (card_le_trans (countable1 v) h1.1)). Qed.

(** Source for [example_counting_singleton]: a point has counting
    measure one, Federer 2.1.2, p. 54, used in 2.5.11, p. 102. *)
Lemma example_counting_singleton (K : choiceType) (u : K) :
  counting_measure (R := R) [set u] = 1.
Proof. by rewrite counting_measure_sum nonnegative_sum_singleton // lee_fin ler01. Qed.

(** Source for [example_counting1_whole]: Y_1 is infinite, so its
    counting measure is infinite, Federer 2.1.2, p. 54, used for
    the value zero of mu on the horizontal lines in 2.5.11, p. 102. *)
Lemma example_counting1_whole : counting_measure (R := R) (@setT J1) = +oo.
Proof. by apply: counting_measure_infinite; apply/infiniteP; exact: h1.1. Qed.

(** Source for [example_rectangle_characteristic]: the characteristic
    function of a measurable rectangle, used for {u} x Y_2 and
    Y_1 x {v} in Federer 2.5.11, p. 102. *)
Definition example_rectangle_characteristic (A : set J1) (B : set J2) : J1 * J2 -> R :=
  @CharacteristicFunction.value R (J1 * J2) (A `*` B).

(** Source for [example_rectangle_integral1]: the alpha_1 x beta_2
    integral of a rectangle characteristic function is the product of
    the factor measures, Federer 2.6.2(2), p. 115, and 2.4.5, p. 83,
    used in 2.5.11, p. 102. *)
Lemma example_rectangle_integral1 (A : set J1) (B : set J2) :
  measure_measurable example_beta2 B ->
  is_measure_integral example_nu1 (real_total_integrand (example_rectangle_characteristic A B))
    (counting_measure (R := R) A * example_beta2 B).
Proof.
move=> hB.
have hA := @counting_measure_measurable R J1 A.
rewrite -(product_measure_rectangle_value (counting_measure_is_measure R J1) example_beta2_measure hA hB).
exact (measure_characteristic_integral example_nu1_measure (CharacteristicFunction.laws _ _)
  (product_measure_rectangle_measurable _ _ hA hB)).
Qed.

(** Source for [example_rectangle_integral2]: the beta_1 x alpha_2
    integral of a rectangle characteristic function, Federer 2.6.2(2),
    p. 115, and 2.4.5, p. 83, used in 2.5.11, p. 102. *)
Lemma example_rectangle_integral2 (A : set J1) (B : set J2) :
  measure_measurable example_beta1 A ->
  is_measure_integral example_nu2 (real_total_integrand (example_rectangle_characteristic A B))
    (example_beta1 A * counting_measure (R := R) B).
Proof.
move=> hA.
have hB := @counting_measure_measurable R J2 B.
rewrite -(product_measure_rectangle_value example_beta1_measure (counting_measure_is_measure R J2) hA hB).
exact (measure_characteristic_integral example_nu2_measure (CharacteristicFunction.laws _ _)
  (product_measure_rectangle_measurable _ _ hA hB)).
Qed.

(** Source for [example_vertical_rectangle_in_lattice]: for a beta_2
    measurable H, the characteristic function of {u} x H belongs to L,
    with lambda value beta_2(H); the case H=Y_2 is the characteristic
    function of {u} x Y_2 in Federer 2.5.11, p. 102. *)
Lemma example_vertical_rectangle_in_lattice (u : J1) (H : set J2) :
  measure_measurable example_beta2 H ->
  example_lattice (example_rectangle_characteristic [set u] H) /\
  (example_mu (example_rectangle_characteristic [set u] H))%:E = example_beta2 H /\
  (example_lambda (example_rectangle_characteristic [set u] H))%:E = example_beta2 H.
Proof.
move=> hH.
have hb : example_beta2 H = 0 \/ example_beta2 H = 1 by exact: cardinal_measure_values.
have h1' := example_rectangle_integral1 [set u] hH.
rewrite example_counting_singleton mul1e in h1'.
have h2' := example_rectangle_integral2 H (cardinal_measure_small_measurable R
  (@countable_sigma_small J1) (countable1 u)).
rewrite example_beta1_singleton mul0e in h2'.
have hL : example_lattice (example_rectangle_characteristic [set u] H).
  split; last by exists 0%R.
  by case: hb=> hb; [exists 0%R|exists 1%R]; rewrite hb in h1'; exact: h1'.
split=> //.
have hm : (example_mu (example_rectangle_characteristic [set u] H))%:E = example_beta2 H.
  exact (measure_integral_unique (example_integral1_spec hL) h1').
split=> //.
have hl : (example_integral2 (example_rectangle_characteristic [set u] H))%:E = 0.
  exact (measure_integral_unique (example_integral2_spec hL) h2').
by rewrite /example_lambda EFinD hm hl adde0.
Qed.

(** Source for [example_horizontal_rectangle_in_lattice]: for a beta_1
    measurable G, the characteristic function of G x {v} belongs to L,
    with mu value zero and lambda value beta_1(G); the case G=Y_1 is
    the characteristic function of Y_1 x {v} in Federer 2.5.11, p. 102. *)
Lemma example_horizontal_rectangle_in_lattice (G : set J1) (v : J2) :
  measure_measurable example_beta1 G ->
  example_lattice (example_rectangle_characteristic G [set v]) /\
  example_mu (example_rectangle_characteristic G [set v]) = 0%R /\
  (example_lambda (example_rectangle_characteristic G [set v]))%:E = example_beta1 G.
Proof.
move=> hG.
have hb : example_beta1 G = 0 \/ example_beta1 G = 1 by exact: cardinal_measure_values.
have h1' := example_rectangle_integral1 G (cardinal_measure_small_measurable R
  (@aleph_one_sigma_small J1 J2 setT h1) (card_le_trans (countable1 v) h1.1)).
rewrite example_beta2_singleton mule0 in h1'.
have h2' := example_rectangle_integral2 [set v] hG.
rewrite example_counting_singleton mule1 in h2'.
have hL : example_lattice (example_rectangle_characteristic G [set v]).
  split; first by exists 0%R.
  by case: hb=> hb; [exists 0%R|exists 1%R]; rewrite hb in h2'; exact: h2'.
split=> //.
have hm : (example_mu (example_rectangle_characteristic G [set v]))%:E = 0.
  exact (measure_integral_unique (example_integral1_spec hL) h1').
split; first exact (EFin_inj hm).
have hl : (example_integral2 (example_rectangle_characteristic G [set v]))%:E = example_beta1 G.
  exact (measure_integral_unique (example_integral2_spec hL) h2').
by rewrite /example_lambda EFinD hm hl add0e.
Qed.

(** Source for [example_vertical_line_values]: the characteristic
    function f of {u} x Y_2 belongs to L with mu(f)=1, Federer 2.5.11,
    p. 102, second display of the proof. *)
Lemma example_vertical_line_values (u : J1) :
  example_lattice (example_rectangle_characteristic [set u] setT) /\
  example_mu (example_rectangle_characteristic [set u] setT) = 1%R.
Proof.
have [hL [hm _]] := example_vertical_rectangle_in_lattice u
  (measure_measurable_whole example_beta2_measure).
by split=> //; apply: EFin_inj; rewrite hm example_beta2_whole.
Qed.

(** Source for [example_horizontal_line_values]: the characteristic
    function g of Y_1 x {v} belongs to L with mu(g)=0, Federer 2.5.11,
    p. 102, third display of the proof. *)
Lemma example_horizontal_line_values (v : J2) :
  example_lattice (example_rectangle_characteristic setT [set v]) /\
  example_mu (example_rectangle_characteristic setT [set v]) = 0%R.
Proof.
have [hL [hm _]] := example_horizontal_rectangle_in_lattice v
  (measure_measurable_whole example_beta1_measure).
by split.
Qed.

End Example.
