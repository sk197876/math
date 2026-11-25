(** Federer (1969), 2.5.11, p. 102: "we see from 2.5.3 that L_1(phi)=L",
    with L_1(phi) the total space of the erratum p. 2, book p. 102 line 12.
    The inclusion of L in L_1(phi) is 2.5.2, p. 92
    ([example_lattice_summable]). For the reverse inclusion, each product
    measure nu=alpha_1 x beta_2 or nu=beta_1 x alpha_2 satisfies the level
    estimate t nu{f>t} <= lambda(f) on L+ and is continuous along increasing
    sequences of arbitrary sets by 2.1.5(1), pp. 56–57, being regular by
    2.6.2(1), pp. 115–117; hence nu <= phi by the envelope formula of 2.5.2,
    p. 92. The strict levels of L+ are nu measurable, so by the F_2 hulls of
    2.5.3, p. 94, every phi measurable set of finite phi measure is nu
    measurable, and every phi summable function is nu summable. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CardinalSuccessorUP CardinalMeasureUP CardinalMeasureLaws
  CardinalProductExample CardinalProductCounterexample
  MeasureUP MeasureBasic CountingMeasure ProductMeasureUP ProductMeasure ProductMeasureRegularity
  RegularMeasureContinuity ExtendedRealOrderLimit ExtendedRealLimitBounds
  FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellCoverUP RegularDaniellEnvelope
  DaniellEnvelopeBounds RealIntegralFunctionalUP RealIntegralFunctional
  FunctionLatticeLevelMeasurability SummableRealFunctionUP SummableRealArithmetic
  TotalScalarLpUP TotalLoneSummability FiniteMeasurableDomination LatticeRegularDomination.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section LoneIdentity.
Variable R : realType.
Variables J1 J2 : choiceType.
Hypothesis h1 : is_cardinal_successor (@setT nat) (@setT J1).
Variable phi : set (J1 * J2) -> \bar R.
Hypothesis hm : is_measure phi.
Hypothesis hA : is_real_integral_functional phi (@example_lattice R J1 J2 h1) (@example_lambda R J1 J2 h1).
Hypothesis hr : is_function_lattice_regular (@example_lattice R J1 J2 h1) phi.

Local Notation nu1 := (@example_nu1 R J1 J2 h1).
Local Notation nu2 := (@example_nu2 R J1 J2).
Local Notation hn1 := (@example_nu1_measure R J1 J2 h1).
Local Notation hn2 := (@example_nu2_measure R J1 J2).
Local Notation L := (@example_lattice R J1 J2 h1).
Local Notation hL := (@example_lattice_is_lattice R J1 J2 h1).
Local Notation lambda := (@example_lambda R J1 J2 h1).

(** Source for [lone_identity_envelope]: the suiting-sequence
    envelope law of 2.5.2, p. 92, for the L regular measure phi of
    Federer 2.5.11, p. 102, by the uniqueness in 2.5.3, p. 94. *)
Lemma lone_identity_envelope : is_daniell_cover_envelope L lambda phi.
Proof. exact (regular_representing_measure_envelope hL hm hA hr). Qed.

(** Source for [nu1_level_bound]: the level estimate
    t nu{f>t} <= lambda(f) of Federer 2.5.3, p. 94, for
    nu=alpha_1 x beta_2 and the first summand of lambda in 2.5.11,
    p. 102. *)
Lemma nu1_level_bound (f : J1 * J2 -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  t%:E * nu1 [set x | (t < f x)%R] <= (lambda f)%:E.
Proof.
move=> hf ht.
apply: le_trans (represented_lattice_strict_level_bound hn1
  (@example_integral1_spec R J1 J2 h1) hf ht) _.
rewrite lee_fin /example_lambda lerDl.
exact: (@monotone_daniell_integral_nonnegative R _ L _ hL
  (real_integral_functional_is_monotone_daniell hn2 hL
    (@example_integral2_spec R J1 J2 h1)) f hf.1 hf.2).
Qed.

(** Source for [nu2_level_bound]: the level estimate of Federer
    2.5.3, p. 94, for nu=beta_1 x alpha_2 and the second summand of
    lambda in 2.5.11, p. 102. *)
Lemma nu2_level_bound (f : J1 * J2 -> R) (t : R) :
  positive_function_lattice L f -> (0 < t)%R ->
  t%:E * nu2 [set x | (t < f x)%R] <= (lambda f)%:E.
Proof.
move=> hf ht.
apply: le_trans (represented_lattice_strict_level_bound hn2
  (@example_integral2_spec R J1 J2 h1) hf ht) _.
rewrite lee_fin /example_lambda lerDr.
exact: (@monotone_daniell_integral_nonnegative R _ L _ hL
  (real_integral_functional_is_monotone_daniell hn1 hL
    (@example_integral1_spec R J1 J2 h1)) f hf.1 hf.2).
Qed.

(** Source for [nu1_increasing_union]: continuity of the regular
    measure alpha_1 x beta_2 along increasing sequences of arbitrary
    sets, Federer 2.1.5(1), pp. 56–57, and 2.6.2(1), pp. 115–117,
    used for the identity L_1(phi)=L in 2.5.11, p. 102. *)
Lemma nu1_increasing_union (V : nat -> set (J1 * J2)) (c : \bar R) :
  (forall n m, (n <= m)%N -> V n `<=` V m) -> (forall n, nu1 (V n) <= c) ->
  nu1 (\bigcup_n V n) <= c.
Proof.
move=> hV hc.
have hlim := @regular_measure_continuity_below R _ nu1 hn1
  (product_measure_is_regular (counting_measure_is_measure R J1) (@example_beta2_measure R J1 J2 h1)) V hV.
exact: (extended_order_limit_upper_bound hlim.2 hc).
Qed.

(** Source for [nu2_increasing_union]: continuity of the regular
    measure beta_1 x alpha_2 along increasing sequences, Federer
    2.1.5(1), pp. 56–57, and 2.6.2(1), pp. 115–117, used in 2.5.11,
    p. 102. *)
Lemma nu2_increasing_union (V : nat -> set (J1 * J2)) (c : \bar R) :
  (forall n m, (n <= m)%N -> V n `<=` V m) -> (forall n, nu2 (V n) <= c) ->
  nu2 (\bigcup_n V n) <= c.
Proof.
move=> hV hc.
have hlim := @regular_measure_continuity_below R _ nu2 hn2
  (product_measure_is_regular (@example_beta1_measure R J1) (counting_measure_is_measure R J2)) V hV.
exact: (extended_order_limit_upper_bound hlim.2 hc).
Qed.

(** Source for [nu1_le_phi]: alpha_1 x beta_2 is dominated by the
    L regular measure phi, by the envelope formula of Federer 2.5.2,
    p. 92; supporting lemma for L_1(phi)=L in 2.5.11, p. 102. *)
Lemma nu1_le_phi (S : set (J1 * J2)) : nu1 S <= phi S.
Proof.
apply: (daniell_envelope_dominates hL (@example_lambda_monotone_daniell R J1 J2 h1)
  lone_identity_envelope hn1).
- exact: nu1_level_bound.
- by move=> V c; exact: nu1_increasing_union.
Qed.

(** Source for [nu2_le_phi]: beta_1 x alpha_2 is dominated by phi,
    Federer 2.5.2, p. 92, supporting L_1(phi)=L in 2.5.11, p. 102. *)
Lemma nu2_le_phi (S : set (J1 * J2)) : nu2 S <= phi S.
Proof.
apply: (daniell_envelope_dominates hL (@example_lambda_monotone_daniell R J1 J2 h1)
  lone_identity_envelope hn2).
- exact: nu2_level_bound.
- by move=> V c; exact: nu2_increasing_union.
Qed.

(** Source for [strict_levels_nu1_measurable]: the strict levels
    {x: f(x)>t} of members f of L+ are alpha_1 x beta_2 measurable,
    since f is alpha_1 x beta_2 summable, Federer 2.3.2(1), p. 73;
    supporting lemma for 2.5.11, p. 102. *)
Lemma strict_levels_nu1_measurable (S : set (J1 * J2)) :
  function_lattice_strict_levels L S -> measure_measurable nu1 S.
Proof.
move=> [f [t [[hf _] [ht ->]]]]; have [a ha] := hf.1.
exact: (real_total_positive_level_measurable hn1 t ha.1).
Qed.

(** Source for [strict_levels_nu2_measurable]: the strict levels of
    members of L+ are beta_1 x alpha_2 measurable, Federer 2.3.2(1),
    p. 73; supporting lemma for 2.5.11, p. 102. *)
Lemma strict_levels_nu2_measurable (S : set (J1 * J2)) :
  function_lattice_strict_levels L S -> measure_measurable nu2 S.
Proof.
move=> [f [t [[hf _] [ht ->]]]]; have [a ha] := hf.2.
exact: (real_total_positive_level_measurable hn2 t ha.1).
Qed.

(** Source for [nu1_finite_measurable]: every phi measurable set of
    finite phi measure is alpha_1 x beta_2 measurable, by its F_2
    hull, Federer 2.5.3, p. 94; supporting lemma for 2.5.11, p. 102. *)
Lemma nu1_finite_measurable (S : set (J1 * J2)) :
  measure_measurable phi S -> phi S < +oo -> measure_measurable nu1 S.
Proof.
exact: (lattice_regular_dominated_finite_measurable hm hn1 hr nu1_le_phi
  strict_levels_nu1_measurable).
Qed.

(** Source for [nu2_finite_measurable]: every phi measurable set of
    finite phi measure is beta_1 x alpha_2 measurable, Federer 2.5.3,
    p. 94; supporting lemma for 2.5.11, p. 102. *)
Lemma nu2_finite_measurable (S : set (J1 * J2)) :
  measure_measurable phi S -> phi S < +oo -> measure_measurable nu2 S.
Proof.
exact: (lattice_regular_dominated_finite_measurable hm hn2 hr nu2_le_phi
  strict_levels_nu2_measurable).
Qed.

(** Source for [lone_summable_nu1]: a function of L_1(phi) is
    alpha_1 x beta_2 summable, by 2.4.4(7)–(8), p. 82, and the two
    preceding comparisons; first half of the inclusion
    L_1(phi) in L in Federer 2.5.11, p. 102. *)
Lemma lone_summable_nu1 (f : J1 * J2 -> R) :
  total_scalar_lp phi 1 f -> summable_real_functions nu1 f.
Proof.
move=> hf; have hs := @total_lone_summable_real R _ phi hm f hf.
have [a ha] := @summable_real_absolute R _ phi hm f hs.
exact: (@finite_dominated_real_absolute_integral R _ phi nu1 hm hn1 f a nu1_le_phi
  nu1_finite_measurable hs ha).1.
Qed.

(** Source for [lone_summable_nu2]: a function of L_1(phi) is
    beta_1 x alpha_2 summable; second half of the inclusion
    L_1(phi) in L in Federer 2.5.11, p. 102. *)
Lemma lone_summable_nu2 (f : J1 * J2 -> R) :
  total_scalar_lp phi 1 f -> summable_real_functions nu2 f.
Proof.
move=> hf; have hs := @total_lone_summable_real R _ phi hm f hf.
have [a ha] := @summable_real_absolute R _ phi hm f hs.
exact: (@finite_dominated_real_absolute_integral R _ phi nu2 hm hn2 f a nu2_le_phi
  nu2_finite_measurable hs ha).1.
Qed.

(** Source for [lone_in_example_lattice]: the inclusion
    L_1(phi) in L contained in "we see from 2.5.3 that L_1(phi)=L",
    Federer 2.5.11, p. 102, with the erratum p. 2, book p. 102 line 12. *)
Theorem lone_in_example_lattice (f : J1 * J2 -> R) : total_scalar_lp phi 1 f -> L f.
Proof. by move=> hf; split; [exact: lone_summable_nu1|exact: lone_summable_nu2]. Qed.

(** Source for [example_lone_identity]: the identity L_1(phi)=L in
    Federer 2.5.11, p. 102, "we see from 2.5.3 that L_1(phi)=L",
    with the total space L_1(phi) of the erratum p. 2, book p. 102
    line 12. The inclusion of L is 2.5.2, p. 92. *)
Theorem example_lone_identity : total_scalar_lp phi 1 = L.
Proof.
apply/seteqP; split=> f hf; first exact: lone_in_example_lattice.
apply: (@summable_real_total_lone R _ phi hm f).
exact: (@example_lattice_summable R J1 J2 h1 phi hA f hf).
Qed.

End LoneIdentity.
