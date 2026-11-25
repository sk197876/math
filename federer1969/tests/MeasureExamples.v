(** Regression examples for Federer (1969), Chapter 2. this edition has no
    measure-theory chapter. Each example below identifies the precise
    statement and boundary convention tested. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureTheory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_empty_sum_regression]: Federer 2.1.1,
    p. 52, empty sum before (1); arbitrary signed summands, even
    with both infinite signs, contribute nothing on the empty set. *)
Lemma measure_empty_sum_regression (R : realType) (I : choiceType) (f : I -> \bar R) :
  numerical_sum set0 f = Some 0.
Proof. exact: numerical_sum_empty. Qed.

(** Source for [measure_positive_infinite_sum_regression]: Federer
    2.1.1(1),(4)-(5), p. 52; a single positive infinite summand
    gives a defined infinite sum. *)
Lemma measure_positive_infinite_sum_regression (R : realType) :
  numerical_sum [set true] (fun _ : bool => (+oo : \bar R)) = Some +oo.
Proof.
rewrite numerical_sum_nonnegative; last by move=> x _; exact: leey.
by rewrite nonnegative_sum_singleton // leey.
Qed.

(** Source for [measure_negative_infinite_sum_regression]: Federer
    2.1.1(6), p. 52, coefficient minus one; the sign reversal of
    a positive infinite total is defined negative infinity. *)
Lemma measure_negative_infinite_sum_regression (R : realType) :
  numerical_sum [set true] (fun _ : bool => (-oo : \bar R)) = Some -oo.
Proof.
change (numerical_sum [set true] (fun _ : bool => - (+oo : \bar R)) = Some -oo).
by rewrite numerical_sum_negate measure_positive_infinite_sum_regression.
Qed.

(** Source for [measure_opposing_infinite_terms]: Federer
    2.1.1(4)-(5), p. 52; regression summand with opposite infinite
    values, whose positive and negative variations are both infinite. *)
Definition measure_opposing_infinite_terms (R : realType) (b : bool) : \bar R :=
  if b then +oo else -oo.

(** Source for [measure_opposing_positive_variation_regression]:
    Federer 2.1.1(1),(3), p. 52; the positive variation of the
    preceding regression is supported at true and has infinite sum. *)
Lemma measure_opposing_positive_variation_regression (R : realType) :
  nonnegative_sum setT (fun b => extended_positive_part (@measure_opposing_infinite_terms R b)) = +oo.
Proof.
transitivity (extended_positive_part (@measure_opposing_infinite_terms R true)).
- apply: (@nonnegative_sum_single_support R _ setT _ true)=> //.
  + exact: extended_positive_part_nonnegative.
  + move=> [] _; first by rewrite eqxx.
    by move=> _; rewrite /measure_opposing_infinite_terms /extended_positive_part maxNye.
- by rewrite /measure_opposing_infinite_terms /extended_positive_part maxye.
Qed.

(** Source for [measure_opposing_negative_variation_regression]:
    Federer 2.1.1(1),(3), p. 52; the negative variation is supported
    at false and also has infinite sum. *)
Lemma measure_opposing_negative_variation_regression (R : realType) :
  nonnegative_sum setT (fun b => extended_negative_part (@measure_opposing_infinite_terms R b)) = +oo.
Proof.
transitivity (extended_negative_part (@measure_opposing_infinite_terms R false)).
- apply: (@nonnegative_sum_single_support R _ setT _ false)=> //.
  + exact: extended_negative_part_nonnegative.
  + move=> [] _; last by rewrite eqxx.
    by move=> _; rewrite /measure_opposing_infinite_terms /extended_negative_part /extended_positive_part maxNye.
- by rewrite /measure_opposing_infinite_terms /extended_negative_part /extended_positive_part maxye.
Qed.

(** Source for [measure_opposing_infinities_undefined_regression]:
    Federer 2.1.1(4)-(5), p. 52; the two-point sum is undefined,
    despite each individual summand being an extended real. *)
Lemma measure_opposing_infinities_undefined_regression (R : realType) :
  numerical_sum setT (@measure_opposing_infinite_terms R) = None.
Proof.
rewrite /numerical_sum measure_opposing_positive_variation_regression
  measure_opposing_negative_variation_regression.
exact: extended_add_opposite_infinities.
Qed.

(** Source for [measure_infinite_counting_sum_regression]: Federer
    2.1.1(3), p. 52, and counting-measure example in 2.1.2,
    p. 54; summing one over the natural numbers gives infinity. *)
Lemma measure_infinite_counting_sum_regression (R : realType) :
  nonnegative_sum setT (fun _ : nat => (1 : R)%:E) = +oo.
Proof.
apply: nonnegative_sum_infinite_constant; first exact: ltr01.
exact: infinite_nat.
Qed.

(** Source for [measure_zero_weight_infinite_fibre_regression]:
    Federer 2.1.1(11), p. 53; zero weights on infinite fibres
    give zero, using precisely the exceptional product convention.
    This tests the iterated-sum theorem on genuinely infinite fibres. *)
Lemma measure_zero_weight_infinite_fibre_regression (R : realType) :
  numerical_sum (setT `*` setT)
    (fun p : bool * nat => (0 : R)%:E * (1 : R)%:E) = Some 0.
Proof.
have hf : forall p : bool * nat, (setT `*` setT) p -> 0 <= (1 : R)%:E.
  by move=> p _; rewrite lee_fin ler01.
rewrite (@numerical_sum_weighted_product R _ _
  setT setT (fun _ : bool * nat => (1 : R)%:E) (fun _ => 0%R) hf).
have he : (fun _ : bool => (0 : R)%:E * nonnegative_sum setT (fun _ : nat => (1 : R)%:E)) =
    (fun _ : bool => (0 : \bar R)).
  by apply: funext=> b; rewrite measure_infinite_counting_sum_regression mul0e.
rewrite he numerical_sum_nonnegative; last by move=> b _.
have hz : nonnegative_sum setT (fun _ : bool => (0 : \bar R)) = 0.
  by apply: nonnegative_sum_zero.
by rewrite hz.
Qed.

(** Source for [measure_two_point_counting_regression]: Federer
    2.1.2, p. 54, counting measure example: the boolean space has
    exactly two points. *)
Lemma measure_two_point_counting_regression (R : realType) :
  counting_measure (R := R) (@setT bool) = (2 : R)%:E.
Proof.
rewrite counting_measure_sum nonnegative_sum_bool; last by move=> b; rewrite lee_fin ler01.
by rewrite -EFinD.
Qed.

(** Source for [measure_nonempty_singleton_not_measurable_regression]:
    Federer 2.1.2, p. 54, zero-or-one measure example; on two points, a
    singleton is a concrete nonmeasurable subset. *)
Lemma measure_nonempty_singleton_not_measurable_regression (R : realType) :
  ~ measure_measurable (@nonempty_measure R _) [set true].
Proof.
move=> /nonempty_measure_measurable_iff [he|he].
- have ht : [set true] true by []; by rewrite he in ht.
- have hf : [set true] false by rewrite he.
  discriminate hf.
Qed.

(** Source for [measure_restrict_nonmeasurable_regression]: Federer
    2.1.2, p. 54, restriction by Y imposes no measurability hypothesis
    on Y. The preceding nonmeasurable singleton still yields a measure. *)
Lemma measure_restrict_nonmeasurable_regression (R : realType) :
  is_measure (measure_restrict (@nonempty_measure R _) [set true]).
Proof. exact: (@measure_restrict_is_measure R _ _ (@nonempty_measure_is_measure R _) [set true]). Qed.

(** Source for [measure_empty_restriction_regression]: Federer
    2.1.2, p. 54, restriction definition at Y empty gives zero on
    every subset, including a subset of infinite original measure. *)
Lemma measure_empty_restriction_regression (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (A : set I) :
  measure_restrict mu set0 A = 0.
Proof. by rewrite /measure_restrict set0I (measure_empty hm). Qed.

(** Source for [measure_counting_tail_infinite_regression]: Federer
    2.1.3(5), p. 55, regression for its finiteness hypothesis. *)
Lemma measure_counting_tail_infinite_regression (R : realType) n :
  counting_measure (R := R) [set k | (n <= k)%N] = +oo.
Proof.
apply: counting_measure_infinite.
have he : [set k | (n <= k)%N] = setT `\` [set k | (k < n)%N].
  apply/seteqP; split.
  - move=> k hk; split=> //; move=> hkn; by move: hk; rewrite /= leqNgt hkn.
  - move=> k [_ hk]; rewrite /= leqNgt; apply/negP; exact hk.
rewrite he; apply: infinite_setD infinite_nat _; exact: finite_II.
Qed.

(** Source for [measure_counting_tail_intersection_regression]: Federer
    2.1.3(5), p. 55 The intersection of all tails is empty and has counting
    measure zero. *)
Lemma measure_counting_tail_intersection_regression (R : realType) :
  counting_measure (R := R) (\bigcap_n [set k | (n <= k)%N]) = 0.
Proof.
have he : (\bigcap_n [set k | (n <= k)%N]) = (@set0 nat).
  apply/seteqP; split=> [k hk|k []].
  have h := hk k.+1 Logic.I; by rewrite /= ltnn in h.
rewrite he; exact: (@measure_empty R _ _ (@counting_measure_is_measure R _)).
Qed.

(** Source for [measure_counting_tail_no_zero_limit_regression]: Federer
    2.1.3(5), p. 55 The decreasing measurable tails fail continuity from
    above when the finite-first-measure hypothesis is removed. *)
Lemma measure_counting_tail_no_zero_limit_regression (R : realType) :
  ~ extended_order_limit
    (fun n => counting_measure (R := R) [set k | (n <= k)%N]) 0.
Proof.
move=> [_ hu].
have h01 : (0 : \bar R) < 1 by rewrite lte_fin ltr01.
have [N hN] := hu 1 h01; have h := hN N (leqnn N).
by rewrite measure_counting_tail_infinite_regression ltNge leey in h.
Qed.

(** Source for [measure_nonmeasurable_singleton_hull_regression]:
    Federer 2.1.4, p. 56, finite criterion; combine with the zero-or-one
    measure of 2.1.2, p. 54. A nonmeasurable singleton in the two-point
    space has the whole space as a hull, both of measure one. *)
Lemma measure_nonmeasurable_singleton_hull_regression (R : realType) :
  is_measure_hull (@nonempty_measure R _) [set true] setT.
Proof.
apply: (@measure_hull_of_finite_equal_measure R _ _
  (@nonempty_measure_is_measure R _) [set true] setT).
- by move=> x _.
- exact: (@measure_measurable_whole R _ _ (@nonempty_measure_is_measure R _)).
- have hA : [set true] != (@set0 bool) by apply/eqP=> he; have ht : [set true] true by []; rewrite he in ht.
  have hX : (@setT bool) != set0 by apply/eqP=> he; have ht : (@setT bool) true by []; rewrite he in ht.
  by rewrite /nonempty_measure (negbTE hA) (negbTE hX).
- rewrite /nonempty_measure; case: ifP=> _; exact: ltry.
Qed.

(** Source for [measure_infinite_equal_superset_not_hull_regression]:
    Federer 2.1.4, p. 56, regression for the finite-measure condition. Here
    deleting zero from the naturals gives the same obstruction, detected by
    the singleton test at zero. *)
Lemma measure_infinite_equal_superset_not_hull_regression (R : realType) :
  counting_measure (R := R) (setT `\` [set 0%N]) = +oo /\
  counting_measure (R := R) (@setT nat) = +oo /\
  ~ is_measure_hull (@counting_measure R _) (setT `\` [set 0%N]) setT.
Proof.
split.
- apply: counting_measure_infinite; exact: infinite_setD infinite_nat (finite_set1 _).
- split; first by apply: counting_measure_infinite; exact: infinite_nat.
  move=> h.
  have ht := @measure_hull_test R _ _ _ _ h [set 0%N]
    (@counting_measure_measurable R _ [set 0%N]).
  have he : [set 0%N] `&` (setT `\` [set 0%N]) = set0.
    apply/seteqP; split=> [x [hx [_ hn]]|x []]; exact: hn hx.
  rewrite he setIT (@measure_empty R _ _ (@counting_measure_is_measure R _))
    counting_measure_sum nonnegative_sum_singleton in ht; last by rewrite lee_fin ler01.
  have h01 : (0 : \bar R) < 1 by rewrite lte_fin ltr01.
  by rewrite -ht ltxx in h01.
Qed.

(** Source for [measure_regularisation_counting_regression]: Federer
    2.1.5, p. 57, regularisation preserves originally measurable sets;
    counting measure has all subsets measurable by 2.1.2, p. 54,
    so regularising it leaves the entire set function unchanged. *)
Lemma measure_regularisation_counting_regression (R : realType) (I : choiceType) :
  measure_regularisation (@counting_measure R I) = @counting_measure R I.
Proof.
apply: funext=> A; exact: (@regularised_measure_measurable_value R I _
  (@counting_measure_is_measure R I) A (@counting_measure_measurable R I A)).
Qed.

(** Source for [measure_regularisation_empty_regression]: Federer
    2.1.5, p. 57, regularisation is a measure and hence retains
    the empty-set value zero from 2.1.2, p. 53. *)
Lemma measure_regularisation_empty_regression (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) : measure_regularisation mu set0 = 0.
Proof. exact: (@measure_empty R I _ (regularised_measure_is_measure hm)). Qed.

(** Source for [measure_regularisation_irregular_singleton_regression]:
    Federer 2.1.5, p. 57, combine the first irregular example with the final
    regularisation formula. A singleton's value rises from one to two
    because its only measurable superset is the whole space. *)
Lemma measure_regularisation_irregular_singleton_regression (R : realType) :
  finite_infinite_measure (R := R) [set 0%N] = (1 : R)%:E /\
  measure_regularisation (@finite_infinite_measure R _) [set 0%N] = (2 : R)%:E.
Proof.
have h0 : [set 0%N] != (@set0 nat).
  apply/eqP=> he; have hx : [set 0%N] 0%N by []; by rewrite he in hx.
split; first exact: (@finite_infinite_measure_finite R _ _ h0 (finite_set1 _)).
apply/eqP; rewrite eq_le; apply/andP; split.
- rewrite -(@finite_infinite_measure_infinite R _ setT infinite_nat).
  apply: (@measure_regularisation_lower R _ _ _ (measure_regularisation_laws _) [set 0%N] setT).
  + by move=> x _.
  + exact: (@measure_measurable_whole R _ _ (@finite_infinite_measure_is_measure R _)).
- apply: (measure_regularisation_greatest (measure_regularisation_laws _))=> B hB hmB.
  have [he|he] := proj1 (@finite_infinite_measure_measurable_iff R _ B infinite_nat) hmB.
  + have h := hB 0%N (erefl _); by rewrite he in h.
  + by rewrite he (@finite_infinite_measure_infinite R _ setT infinite_nat).
Qed.

(** Source for [measure_restriction_erratum_values_regression]:
    Federer 2.1.5, p. 57, third example, corrected by erratum
    p. 1, book p. 57 line 26: card(A) on subsets of S. The
    empty, singleton and two-point support values are zero, one and two. *)
Lemma measure_restriction_erratum_values_regression (R : realType) :
  two_point_restriction_measure (R := R) set0 = 0 /\
  two_point_restriction_measure (R := R) [set Some false] = (1 : R)%:E /\
  two_point_restriction_measure (R := R) two_point_support = (2 : R)%:E.
Proof.
split; first exact: (@measure_empty R _ _ (@two_point_restriction_measure_is_measure R)).
split; first exact: two_point_restriction_singleton_inside.
rewrite two_point_restriction_measure_inside; last by move=> x hx.
exact: two_point_support_counting.
Qed.

Local Open Scope card_scope.

(** Source for [ulam_empty_regression]: Federer 2.1.6,
    p. 58, regression for the initial-segment assertion: zero is
    Ulam, including empty ambient carriers. *)
Lemma ulam_empty_regression (R : realType) (I : choiceType) :
  is_ulam_set R (@set0 I).
Proof. apply: ulam_set_countable; exact: countable0. Qed.

(** Source for [ulam_naturals_regression]: Federer 2.1.6,
    p. 58, direct regression of the printed aleph-zero assertion. *)
Lemma ulam_naturals_regression (R : realType) :
  is_ulam_set R (@setT nat).
Proof. apply: ulam_set_countable; exact: countableP. Qed.

(** Source for [cardinal_zero_successor_regression]: Federer
    2.1.6(2), pp. 58-59, regression for the finite case omitted
    from the printed proof's infinite-alpha argument. A singleton
    is the cardinal successor of the empty set. *)
Lemma cardinal_zero_successor_regression :
  is_cardinal_successor (@set0 bool) [set true].
Proof.
split; first exact: card_ge0.
split.
- move/card_le0P=> he; have ht : [set true] true by []; by rewrite he in ht.
- move=> K C _ hn.
  have hC : C != set0.
    apply/eqP=> he; apply: hn; rewrite he; exact: card_ge0.
  have [c hc] := proj1 (set0P C) hC.
  apply: (@cardinal_bound_of_injection _ K [set true] C (fun _ => c)).
  + by move=> x _.
  + by move=> x y /set_mem hx /set_mem hy _; rewrite hx hy.
Qed.

(** Source for [ulam_zero_successor_regression]: Federer
    2.1.6(2), pp. 58-59, apply the general successor theorem
    to zero and one. This checks that no infinitude hypothesis
    has accidentally entered the public theorem. *)
Lemma ulam_zero_successor_regression (R : realType) :
  is_ulam_set R [set true].
Proof.
exact: (@ulam_set_successor R _ _ set0 [set true]
  (@ulam_empty_regression R _) cardinal_zero_successor_regression).
Qed.

From mathcomp Require Import topology.

(** Source for [borel_empty_space_regression]: Federer 2.2.1,
    p. 59, empty-space boundary: the largest and smallest Borel
    families coincide and contain only the empty set. *)
Lemma borel_empty_space_regression (I : choiceType) (F : set (set I)) :
  is_borel_family set0 F -> F = [set A | A = set0].
Proof.
move=> hF; apply/seteqP; split.
- move=> A hA; apply/seteqP; split=> [x hx|x []].
  exact: (@borel_family_within I set0 F hF A hA x hx).
- move=> A ->; exact: borel_family_empty hF.
Qed.

(** Source for [borel_generation_erratum_regression]: local
    counterexample for the uncorrected criterion in Federer 2.2.1,
    p. 60. With no generators, the complement-generator condition
    is vacuous but the resulting closure family is not Borel on
    a nonempty space. Erratum p. 1, book p. 60 line 4, fixes
    precisely this issue by requiring the empty set as a generator. *)
Lemma borel_generation_erratum_regression (d : bool) :
  @is_generated_closed_family d _ (@setT bool) set0 [set A | A = set0] /\
  (forall A : set bool, (@set0 (set bool)) A ->
    [set B | B = set0] (setT `\` A)) /\
  ~ is_borel_family (@setT bool) [set A | A = set0].
Proof.
split; first exact: empty_generators_closed_specification.
split; first by move=> A [].
apply: empty_only_not_borel; by exists true.
Qed.

(** Source for [borel_empty_partition_regression]: Federer
    2.2.1, p. 60, empty partition convention: no members
    form a countable disjoint Borel partition of the empty set. *)
Lemma borel_empty_partition_regression (T : topologicalType) :
  @is_borel_partition T set0 set0.
Proof. exact: borel_partition_empty. Qed.

(** Source for [measure_zero_support_regression]: Federer
    2.2.1, p. 60, empty-support boundary: the zero set function
    has empty support, verified through the sealed support laws. *)
Lemma measure_zero_support_regression (R : realType) (T : topologicalType) :
  measure_support (fun _ : set T => (0 : \bar R)) = set0.
Proof. exact: measure_support_zero. Qed.

From mathcomp Require Import topology pseudometric_structure.

(** Source for [borel_closed_empty_approximation_regression]: Federer
    2.2.2(1), pp. 60-61, empty target with arbitrary total
    measure: only the measure of the approximated set must be finite. *)
Lemma borel_closed_empty_approximation_regression (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) :
  (forall U, open U -> measure_measurable mu U) ->
  is_closed_approximable mu set0.
Proof.
move=> ho; apply: (@metric_borel_closed_approximation R T mu hm set0 ho).
- exact: open_borel_set open0.
- by rewrite (measure_empty hm) ltry.
Qed.

(** Source for [borel_open_empty_approximation_regression]: Federer
    2.2.2(2), p. 61, empty open covering sequence and empty
    target. The ambient measure may be infinite. *)
Lemma borel_open_empty_approximation_regression (R : realType) (T : pseudoMetricType R)
    (mu : set T -> \bar R) (hm : is_measure mu) (epsilon : R) :
  (forall U, open U -> measure_measurable mu U) -> (0 < epsilon)%R ->
  exists W, open W /\ mu W < epsilon%:E.
Proof.
move=> ho he.
have hV (n : nat) : open (@set0 T) /\ mu (@set0 T) < +oo.
  split; first exact: open0; by rewrite (measure_empty hm) ltry.
have hcover : (@set0 T) `<=` \bigcup_(n : nat) (@set0 T) by move=> x [].
have [W [hW [_ herror]]] := @metric_borel_open_approximation R T mu hm set0
  (fun _ => set0) epsilon ho (open_borel_set open0) hV hcover he.
exists W; split=> //; by rewrite setD0 in herror.
Qed.

(** Source for [closed_approximation_zero_tolerance_regression]: Federer
    2.2.2, pp. 60-61, strict epsilon positivity cannot be
    dropped: no difference set can have measure strictly below zero. *)
Lemma closed_approximation_zero_tolerance_regression (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (A C : set T) :
  ~ (mu (A `\` C) < 0).
Proof. by move=> h; have hn := @measure_nonnegative R _ mu hm (A `\` C); rewrite leNgt h in hn. Qed.

From mathcomp Require Import topology pseudometric_structure.

(** Source for [borel_regularisation_empty_regression]: Federer
    2.2.3, p. 62, regression for the empty Borel set: its value
    remains zero even if the whole original measure is infinite. *)
Example borel_regularisation_empty_regression (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) : borel_regularisation mu set0 = 0.
Proof.
rewrite (borel_regularised_measure_borel_value hm (open_borel_set (@open0 T))).
exact: measure_empty hm.
Qed.

(** Source for [borel_regularisation_infinite_whole_regression]:
    Federer 2.2.3, p. 62, regression retaining infinity on the
    whole Borel space; regularisation requires no global finiteness. *)
Example borel_regularisation_infinite_whole_regression (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) : mu setT = +oo ->
  borel_regularisation mu setT = +oo.
Proof. by rewrite (borel_regularised_measure_borel_value hm (open_borel_set (@openT T))). Qed.

(** Source for [borel_regular_empty_sandwich_regression]: Federer
    2.2.3, p. 61, regression applying the sandwich theorem at the
    zero-measure empty set, with no assumption on the whole measure. *)
Example borel_regular_empty_sandwich_regression (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) : exists D B,
  borel_set D /\ borel_set B /\ D `<=` set0 /\ set0 `<=` B /\ mu (B `\` D) = 0.
Proof.
apply: (@borel_regular_finite_sandwich R T mu hm hr set0 (measure_measurable_empty hm)).
by rewrite (measure_empty hm) ltry.
Qed.

From mathcomp Require Import topology pseudometric_structure.

(** Source for [radon_empty_compact_approximation_regression]:
    Federer 2.2.5, p. 63, regression at the empty measurable set,
    with no finiteness assumption on the measure of the entire space. *)
Example radon_empty_compact_approximation_regression (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu)
    (hr : is_radon_measure mu) epsilon : (0 < epsilon)%R ->
  exists K, compact K /\ K `<=` set0 /\ mu (set0 `\` K) < epsilon%:E.
Proof.
move=> he; apply: (@radon_compact_approximation R T mu hm hr set0 epsilon
  (measure_measurable_empty hm) _ he).
by rewrite (measure_empty hm) ltry.
Qed.

(** Source for [radon_zero_tolerance_regression]: Federer
    2.2.5, p. 63, regression recording the need for positive
    epsilon when the error is required to be strictly smaller. *)
Example radon_zero_tolerance_regression (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) (A K : set T) :
  ~ (mu (A `\` K) < 0).
Proof. by rewrite ltNge (measure_nonnegative hm). Qed.

From mathcomp Require Import topology pseudometric_structure.

(** Source for [sequence_default_first_cylinder]: regression for
    Federer 2.2.6, p. 63: the constant positive-one sequence
    lies in the first cylinder. Its zero-based coordinate code is zero. *)
Example sequence_default_first_cylinder (R : realType) :
  positive_sequence_cylinder 0%N (positive_sequence_default R).
Proof. by rewrite /positive_sequence_cylinder /= /positive_sequence_default positive_sequence_coordinatesK. Qed.

(** Source for [sequence_zero_prefix_whole]: regression for
    Federer 2.2.6, p. 63: prescribing no initial coordinates
    gives the whole sequence space, including in the product basis. *)
Example sequence_zero_prefix_whole (R : realType) (x : positive_sequence_space R) :
  positive_sequence_prefix x 0 = setT.
Proof. apply/seteqP; split=> // y _ i; by rewrite ltn0. Qed.

(** Source for [sequence_delete_insert_first_coordinate]: regression
    for Federer 2.2.6, p. 63, the cylinder homeomorphism at the
    smallest positive coordinate, encoded by zero. *)
Example sequence_delete_insert_first_coordinate (R : realType) (x : positive_sequence_space R) :
  positive_sequence_tail (positive_sequence_prepend 0%N x) = x.
Proof. exact: positive_sequence_tail_prepend. Qed.

(** Source for [sequence_constant_array_flatten]: regression for
    Federer 2.2.6, p. 63, countable-product reindexing: a
    constant array of positive-one sequences remains the positive-one
    sequence under every index map, including nonbijective maps. *)
Example sequence_constant_array_flatten (R : realType) (decode : nat -> nat * nat) :
  positive_sequence_flatten decode (fun _ => positive_sequence_default R) = positive_sequence_default R.
Proof.
apply: positive_sequence_extensionality=> i.
by rewrite /positive_sequence_flatten /positive_sequence_default !positive_sequence_coordinatesK.
Qed.

From mathcomp Require Import topology pseudometric_structure.

Local Open Scope ring_scope.

(** Source for [lipschitz_constant_zero_regression]: regression for Federer
    2.2.7, p. 64. *)
Example lipschitz_constant_zero_regression (R : realType) (T U : metricType R)
    (X : set T) (a : U) (h : is_metric_lipschitz X (fun _ => a)) :
  metric_lipschitz_constant h = 0.
Proof.
apply: least_metric_lipschitz_unique (metric_lipschitz_constant_specification h) _.
exact: metric_lipschitz_constant_map.
Qed.

(** Source for [lipschitz_empty_zero_regression]: regression
    for Federer 2.2.7, p. 64: the least nonnegative bound on
    the empty domain is zero, independently of the function. *)
Example lipschitz_empty_zero_regression (R : realType) (T U : metricType R)
    (f : T -> U) (h : is_metric_lipschitz set0 f) :
  metric_lipschitz_constant h = 0.
Proof.
apply: least_metric_lipschitz_unique (metric_lipschitz_constant_specification h) _.
exact: metric_lipschitz_empty.
Qed.

(** Source for [lipschitz_constant_has_positive_witness_regression]:
    regression for the positive-witness wording of Federer 2.2.7,
    pp. 63–64: a constant map is Lipschitzian, including on an
    empty domain, even though its optimal bound is zero. *)
Example lipschitz_constant_has_positive_witness_regression (R : realType)
    (T U : metricType R) (X : set T) (a : U) :
  is_metric_lipschitz X (fun _ => a).
Proof. exact: metric_lipschitz_of_bound (least_metric_lipschitz_bound (metric_lipschitz_constant_map X a)). Qed.

(** Source for [lipschitz_negative_bound_empty_regression]: local boundary
    clarification for Federer 2.2.7, p. 64: on an empty domain the pointwise
    limsup condition is vacuous, whereas the nonnegative optimal constant
    cannot be bounded by -1. This explains the explicit nonnegative M
    hypothesis It is not an entry in Federer's erratum. *)
Example lipschitz_negative_bound_empty_regression (R : realType)
    (T U : metricType R) (f : T -> U) (h : is_metric_lipschitz set0 f) :
  ~ (metric_lipschitz_constant h <= -1).
Proof.
move=> hh; have hn := le_trans (metric_lipschitz_constant_nonnegative h) hh.
by move: hn; rewrite oppr_ge0 ler10.
Qed.

(** Regression examples for Federer (1969), 2.2.8,
    pp. 64–65. Editions and conventions: ClosedCoverTreeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceSeparability
  SequenceCompleteness CompleteMetricUP ClosedCoverTreeUP SequenceTreePrefixes
  ClosedCoverMapUP ClosedCoverMapLipschitz SequenceParametrisation LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [sequence_space_parametrisation_regression]:
    regression for Federer 2.2.8, pp. 64–65, using the
    complete separable space of 2.2.6 itself as target. This checks
    compatibility of the abstract completeness and sequence interfaces. *)
Example sequence_space_parametrisation_regression (R : realType) :
  exists g : positive_sequence_space R -> positive_sequence_space R,
    (forall x, exists n, g n = x) /\ is_locally_metric_lipschitz setT g /\ continuous g.
Proof.
apply: complete_separable_sequence_parametrisation.
- move=> F PF hF; exact: (@positive_sequence_cauchy_limit_exists R F PF hF).
- exact: positive_sequence_separable.
- by exists (positive_sequence_default R).
Qed.

(** Source for [closed_tree_empty_prefix_regression]: regression
    for Federer 2.2.8, p. 64: the empty prefix denotes the
    entire target, and imposes no small-diameter condition. *)
Example closed_tree_empty_prefix_regression (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (n : positive_sequence_space R) x : E (sequence_tree_prefix n 0) x.
Proof. by rewrite /= (closed_cover_tree_root hE). Qed.

(** Source for [closed_tree_coincident_inputs_regression]:
    regression for the local distance bound in Federer 2.2.8,
    pp. 64–65: coincident input sequences satisfy the bound
    with no first-difference index to choose. *)
Example closed_tree_coincident_inputs_regression (R : realType) (T : metricType R)
    (E : seq nat -> set T) (hE : is_closed_cover_tree E)
    (g : positive_sequence_space R -> T) (hg : is_closed_cover_map E g) n :
  mdist (g n) (g n) <= mdist n n.
Proof.
apply: (@closed_cover_map_small_distance R T E hE g hg n n).
rewrite mdistxx; exact: closed_cover_tree_scale_positive.
Qed.

(** Regression examples for Federer (1969), 2.2.9, p. 65. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import SequenceSpace SequenceCoordinates HomeomorphismOnto TopologicalBorel
  RealMetricBackground RealOpenIntervals RealIntervalClosureEndpoints
  OpenEmbeddingBorelImage OpenEmbeddingTreeUP SequenceBorelEmbedding
  RealMetricCompleteness RealSequenceBorelEmbedding.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [adjacent_interval_closures_regression]: regression for
    Federer 2.2.9, p. 65. The tree interface must allow this endpoint
    behavior. *)
Example adjacent_interval_closures_regression (R : realType) :
  real_open_interval (0 : R) 1 `&` real_open_interval 1 2 = set0 /\
  (closure (real_open_interval (0 : R) 1) `&`
   closure (real_open_interval (1 : R) 2)) 1.
Proof.
split; first by apply: real_open_intervals_ordered_disjoint; exact: lexx.
split.
- apply: real_open_interval_right_endpoint_closure; exact: ltr01.
- apply: real_open_interval_left_endpoint_closure; by rewrite ltr1n.
Qed.

(** Source for [empty_open_embedding_level_regression]: regression
    for Federer 2.2.9, p. 65: the zero-level union is the
    whole space because its unique finite word is the root.
    The displayed Gamma uses positive levels. *)
Example empty_open_embedding_level_regression (R : realType) (T : metricType R)
    (U : seq nat -> set T) (hU : is_open_embedding_tree U) :
  open_embedding_level U 0 = setT.
Proof.
apply/seteqP; split; first by move=> x _.
move=> x _; exists (@nil nat)=> //; by rewrite (open_embedding_tree_root hU).
Qed.

(** Source for [real_borel_embedding_nonempty_regression]:
    regression for Federer 2.2.9, p. 65: the produced Borel
    set with countable complement is nonempty, witnessed by the
    image of the sequence consisting entirely of ones. *)
Example real_borel_embedding_nonempty_regression (R : realType) :
  exists G : set (real_line_metric R),
    borel_set G /\ countable (~` G) /\ G !=set0.
Proof.
have [G [g [hB [hC hg]]]] := @real_sequence_borel_embedding_countable_complement R.
exists G; split=> //; split=> //.
exists (g (@positive_sequence_default R)).
rewrite -(homeomorphism_onto_image hg); by exists (@positive_sequence_default R).
Qed.

(** Regression examples for Federer (1969), 2.2.10, pp. 65–66: empty and
    whole-space projection witnesses, empty unions, and the real-valued
    distance convention. These are checked boundary cases of the annotated
    public declarations, not additional claims attributed to Federer. Source
    context: SuslinSetUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets cardinality reals topology.
From Federer Require Import SuslinSetUP ClosedSetProjection OpenSetClosedProjection
  BorelClosedProjection SuslinFamilyClosure MetricSetDistanceUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [whole_metric_space_closed_projection_example]: regression
    for Federer 2.2.10, p. 66, and the separate whole-space case. No finite
    distance to the empty complement is required. *)
Example whole_metric_space_closed_projection_example (R : realType) (T : metricType R) :
  has_univalent_closed_projection R (@setT T).
Proof. apply: open_set_univalent_closed_projection; exact: openT. Qed.

(** Source for [empty_borel_closed_projection_example]: regression
    for the Borel representation in Federer 2.2.10, p. 66,
    retaining an empty target in any ambient metric space. *)
Example empty_borel_closed_projection_example (R : realType) (T : metricType R) :
  has_univalent_closed_projection R (@set0 T).
Proof. apply: metric_borel_univalent_closed_projection; exact: open_borel_set open0. Qed.

(** Source for [empty_family_suslin_union_example]: regression
    strengthening of the union clause in Federer 2.2.10,
    p. 66: even the empty family has a Suslin union. *)
Example empty_family_suslin_union_example (R : realType) (T : topologicalType) :
  is_suslin_set R (\bigcup_(A in @set0 (set T)) A).
Proof. rewrite bigcup_set0; exact: empty_set_suslin. Qed.

(** Source for [empty_set_has_no_real_distance_example]: Supporting Federer
    2.2.10, p. 66.At a point of the ambient space, the empty set cannot have
    a finite real greatest lower bound of distances. *)
Example empty_set_has_no_real_distance_example (R : realType) (T : metricType R)
    (x : T) (d : T -> R) : ~ is_metric_set_distance set0 d.
Proof.
move=> hd; have hl : forall a : T, set0 a -> d x+1 <= mdist x a by move=> a [].
have hh := @metric_set_distance_greatest R T set0 d hd x (d x+1) hl.
have ht : d x < d x+1 by rewrite ltrDl ltr01.
by have := lt_le_trans ht hh; rewrite ltxx.
Qed.

From Federer Require Import CompleteMetricUP InjectiveClosedImageBorel
  BorelSuslinComplement.

(** Source for [constant_on_singleton_injective_image_example]: regression
    for Federer 2.2.10(2), p. 67: injectivity is required only on the closed
    domain. A globally constant map is injective on a singleton, even in a
    larger source space. *)
Example constant_on_singleton_injective_image_example (R : realType) (T : metricType R)
    (Y : topologicalType) (x : T) (y : Y) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) -> hausdorff_space Y ->
  borel_set ((fun _ : T => y) @` [set x]).
Proof.
move=> hT hsep hY; apply: (@injective_closed_image_borel R T Y (fun _ => y) [set x] hT hsep hY).
- move=> z; exact: cvg_cst.
- apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
- by move=> u v hu hv _; rewrite hu hv.
Qed.

(** Source for [borel_suslin_complement_empty_example]: regression
    for the complement characterization in Federer 2.2.10,
    p. 68: the empty set and whole space are both Suslin,
    including when the ambient metric space is empty. *)
Example borel_suslin_complement_empty_example (R : realType) (T : metricType R) :
  is_complete_metric_space T ->
  (exists H : set T, countable H /\ dense H) ->
  is_suslin_set R (@set0 T) /\ is_suslin_set R (~` (@set0 T)).
Proof.
move=> hT hsep; apply: (proj1 (@borel_iff_suslin_and_complement_suslin R T set0 hT hsep)).
exact: open_borel_set (@open0 T).
Qed.

(** Boundary regressions for Federer (1969), 2.2.11, p. 68: empty and whole
    slices and the non-Suslin complement of the diagonal example. The whole
    slice checks the empty-base normalization without exposing the private
    coding formula. Source context: CountableOpenBaseUP.v. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import SequenceSpace UniversalClosedSetUP
  SuslinSetUP SequenceNonBorelSuslin TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [universal_closed_whole_slice_example]: regression
    for Federer 2.2.11, p. 68: the whole closed space must
    occur as a slice, even though a coding base without an empty
    member could not represent it by the printed formula. *)
Example universal_closed_whole_slice_example (R : realType) (T : topologicalType)
    (C : set (T * positive_sequence_space R)) :
  is_universal_closed_set C -> exists n, forall x, C (x,n).
Proof.
move=> hC; have [n hn] := @universal_closed_set_slices R T C hC setT (@closedT T).
exists n=> x; have hx : (@setT T) x := Logic.I; by rewrite hn in hx.
Qed.

(** Source for [universal_closed_empty_slice_example]: regression
    for Federer 2.2.11, p. 68: the empty closed set has
    a parameter slice in every universal closed relation. *)
Example universal_closed_empty_slice_example (R : realType) (T : topologicalType)
    (C : set (T * positive_sequence_space R)) :
  is_universal_closed_set C -> exists n, forall x, ~ C (x,n).
Proof.
move=> hC; have [n hn] := @universal_closed_set_slices R T C hC set0 (@closed0 T).
exists n=> x hx; have hh : (@set0 T) x by rewrite hn.
exact hh.
Qed.

(** Source for [sequence_suslin_complement_failure_example]: regression
    for Federer 2.2.11, p. 68: Suslin sets are not closed
    under complements, in contrast with the Borel-family laws. *)
Example sequence_suslin_complement_failure_example (R : realType) :
  ~ (forall A : set (positive_sequence_space R),
       is_suslin_set R A -> is_suslin_set R (~` A)).
Proof.
move=> h; have [A [hA [hn _]]] := sequence_suslin_non_borel_exists R.
exact: hn (h A hA).
Qed.

(** Boundary regressions for Federer (1969), 2.2.4, p. 62: countable ambient
    spaces, null measures and singleton selection families. These exercise
    the necessary uncountability/positivity premises and the abstract
    selection laws. Source context: SeparableMetricBaseConstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import CountableNeighborhoodLocus PositiveClosedCardinality DisjointSelectionsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_space_condensation_kernel_empty_example]:
    Supporting Federer 2.2.4, p. 62.In a countable space every point already
    has the whole space as a countable open neighborhood, so the kernel is
    empty. *)
Example countable_space_condensation_kernel_empty_example (T : topologicalType) :
  countable (@setT T) -> (~` @countable_neighborhood_locus T) = set0.
Proof.
move=> hc; apply/seteqP; split=> [x hx|x []].
apply: hx; exists setT; split; first exact: openT.
by split.
Qed.

(** Source for [zero_measure_positive_closed_family_empty_example]:
    regression for the family Gamma in Federer 2.2.4, p. 62:
    a measure identically zero has no positive closed subsets,
    so the positivity premise cannot be dropped from the theorem. *)
Example zero_measure_positive_closed_family_empty_example (R : realType)
    (T : topologicalType) (mu : set T -> \bar R) (A : set T) :
  (forall C, mu C = 0) -> positive_closed_family mu A = set0.
Proof.
move=> hz; apply/seteqP; split=> [C [_ [_ hp]]|C []].
by rewrite hz ltxx in hp.
Qed.

(** Source for [singleton_disjoint_selections_impossible_example]:
    regression for the two selections in Federer 2.2.4, p. 62: a singleton
    cannot supply disjoint left and right selections, explaining the need
    for the cardinal fresh-point argument. *)
Example singleton_disjoint_selections_impossible_example (T : choiceType)
    (x : T) (f g : unit -> T) :
  ~ is_disjoint_family_selection (fun _ : unit => [set x]) f g.
Proof.
move=> h; have hf := disjoint_selection_left_member h tt.
have hg := disjoint_selection_right_member h tt.
have he : f tt = g tt by rewrite hf hg.
exact (@disjoint_selection_separated unit T (fun _ : unit => [set x]) f g h tt tt he).
Qed.

(** Regression examples for Federer (1969), 2.2.12, pp. 68–69. Source
    context and proof conventions: SequenceBoxes.v and
    SuslinMeasurability.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import SequenceSpace SequenceCoordinates SequenceBoxes
  SuslinSetUP TopologicalBorel SequenceNonBorelSuslin MeasureUP MeasureBasic
  SuslinMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [sequence_zero_box_singleton_example]: regression
    for the compact box K in Federer 2.2.12, p. 69.
    Natural bound zero means positive bound one; the box then
    consists exactly of the constant-one sequence. *)
Example sequence_zero_box_singleton_example (R : realType) :
  @sequence_coordinate_box R (fun _ => 0%N) = [set positive_sequence_default R].
Proof.
apply/seteqP; split.
- move=> n hn; apply: positive_sequence_extensionality=> i.
  have hi := hn i; move: hi; rewrite leqn0=> /eqP ->.
  by rewrite /positive_sequence_default positive_sequence_coordinatesK.
- move=> n ->; exact: sequence_coordinate_box_nonempty.
Qed.

(** Source for [suslin_empty_test_approximation_example]: regression
    for Federer 2.2.12, p. 68, with an empty test
    set. The full theorem applies without requiring the test set
    to be measurable or inhabited. *)
Example suslin_empty_test_approximation_example (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (S : set X) (delta : R) :
  (forall C : set X, closed C -> measure_measurable mu C) ->
  is_suslin_set R S -> (0 < delta)%R ->
  exists C, closed C /\ C `<=` S /\ mu ((set0 `&` S) `\` C) <= delta%:E.
Proof.
move=> hc hS hd; apply: (@suslin_closed_inner_approximation R X mu hm S set0 delta hc hS _ hd).
by rewrite (measure_empty hm) ltry.
Qed.

(** Source for [non_borel_universally_measurable_example]: regression
    combining Federer 2.2.11, p. 68, and 2.2.12,
    pp. 68–69. A non-Borel Suslin subset of N is measurable
    for every measure making closed sets measurable; measurability
    is therefore stronger coverage than merely proving Borel sets
    measurable. No finite-total-measure premise is introduced. *)
Example non_borel_universally_measurable_example (R : realType) :
  exists A : set (positive_sequence_space R), ~ borel_set A /\
    forall (mu : set (positive_sequence_space R) -> \bar R),
      is_measure mu ->
      (forall C, closed C -> measure_measurable mu C) -> measure_measurable mu A.
Proof.
have [A [hA [_ hn]]] := sequence_suslin_non_borel_exists R.
exists A; split=> // mu hm hc; exact: (@suslin_set_measurable R [the topologicalType of positive_sequence_space R] mu hm A hc hA).
Qed.

(** Regression examples for Federer (1969), 2.2.13, pp. 69–70. Source
    context: BorelImageMeasurability.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import CompleteMetricUP TopologicalBorel MeasureUP
  BorelImageMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_image_empty_domain_example]: regression
    for Federer 2.2.13, pp. 69–70. The Borel domain
    set may be empty, and the conclusion needs no positive
    measure, nonempty-domain, or injectivity premise. *)
Example borel_image_empty_domain_example (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (mu : set Y -> \bar R)
    (hm : is_measure mu) :
  is_complete_metric_space X ->
  (exists D : set X, countable D /\ dense D) ->
  hausdorff_space Y -> continuous f ->
  (forall C, closed C -> measure_measurable mu C) ->
  measure_measurable mu (f @` set0).
Proof.
move=> hX hs hY hf hc.
apply: (@continuous_borel_image_measurable R X Y f mu hm set0 hX hs hY hf hc).
exact: open_borel_set open0.
Qed.

(** Source for [continuous_entire_image_measurable_example]: regression
    for Federer 2.2.13, pp. 69–70: the entire image
    is measurable without any finiteness premise on its measure. *)
Example continuous_entire_image_measurable_example (R : realType) (X : metricType R)
    (Y : topologicalType) (f : X -> Y) (mu : set Y -> \bar R)
    (hm : is_measure mu) :
  is_complete_metric_space X ->
  (exists D : set X, countable D /\ dense D) ->
  hausdorff_space Y -> continuous f ->
  (forall C, closed C -> measure_measurable mu C) ->
  measure_measurable mu (f @` setT).
Proof.
move=> hX hs hY hf hc.
apply: (@continuous_borel_image_measurable R X Y f mu hm setT hX hs hY hf hc).
exact: open_borel_set openT.
Qed.

(** Regression examples for the final continued-fraction comparison in
    Federer (1969), 2.2.9, p. 65. These check indexing, literal finite
    truncation, rational exclusion and the distinction between finite
    endpoints and the infinite image. Source context and supporting
    references: ContinuedFractions.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SequenceSpace SequenceCoordinates RationalRealUP
  ContinuedFractionBranches FiniteContinuedFractions ContinuedFractions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continued_fraction_empty_truncation_example]:
    regression for the zero-term indexing convention supporting
    the displayed positive-term fraction in Federer 2.2.9, p. 65. *)
Example continued_fraction_empty_truncation_example (R : realType)
    (n : positive_sequence_space R) : continued_fraction_convergent n 0 = 0.
Proof. by []. Qed.

(** Source for [continued_fraction_two_ones_example]: regression
    for the literal two-term fraction 1/(1+1/1)=1/2
    in Federer 2.2.9, p. 65. This checks ordinary
    consecutive digits, not only four-digit grouped convergents. *)
Example continued_fraction_two_ones_example (R : realType) :
  continued_fraction_convergent (@positive_sequence_default R) 2 = (2 : R)^-1.
Proof.
by rewrite /continued_fraction_convergent /positive_sequence_default
  positive_sequence_coordinatesK /= /continued_fraction_branch addr0 invr1.
Qed.

(** Source for [continued_fraction_rational_half_excluded_example]:
    regression for the exact irrational image of the homeomorphism
    in Federer 2.2.9, p. 65. The rational finite
    convergent one half has no infinite positive-digit expansion. *)
Example continued_fraction_rational_half_excluded_example (R : realType) :
  ~ exists n : positive_sequence_space R, continued_fraction_map n = (1 : R)/2.
Proof.
move=> [n hn]; have hirr := continued_fraction_map_irrational n.
apply: hirr.2.2; rewrite hn.
exact: (@natural_quotient_rational R 1 2 (erefl true)).
Qed.

(** Source for [continued_fraction_infinite_ones_inside_example]:
    regression for the strict unit-interval image in Federer
    2.2.9, p. 65. Although the first all-one
    truncation is one, the infinite all-one value lies strictly
    below one and is irrational. *)
Example continued_fraction_infinite_ones_inside_example (R : realType) :
  irrational_unit_interval (continued_fraction_map (@positive_sequence_default R)).
Proof. exact: continued_fraction_map_irrational. Qed.

(** Regression examples for Federer (1969), 2.2.14, p. 70. Source context
    and hypotheses: BorelFunctionUP.v and BorelSuslinImages.v. *)
From mathcomp Require Import all_boot classical_sets cardinality reals topology.
From Federer Require Import BorelFunctionUP BorelFunctionBasic CharacteristicBorel
  CharacteristicFunctionSealed RealMetricBackground TopologicalBorel
  SuslinSetUP ClosedSetProjection CompleteMetricUP BorelSuslinImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [identity_borel_regression]: regression for Federer 2.2.14,
    p. 70. *)
Example identity_borel_regression (X : topologicalType) : is_borel_function (@id X).
Proof. exact: identity_borel_function. Qed.

(** Source for [empty_characteristic_borel_regression]: regression
    for the characteristic-function equivalence in Federer 2.2.14,
    p. 70. The empty set has a Borel characteristic
    function through the sealed abstract interface. *)
Example empty_characteristic_borel_regression (R : realType) (X : topologicalType) :
  @is_borel_function X [the topologicalType of real_line_metric R]
    (@CharacteristicFunction.value R X set0).
Proof.
apply: (proj1 (@borel_iff_characteristic_borel R X set0)); exact: open_borel_set open0.
Qed.

(** Source for [borel_empty_suslin_image_regression]: regression
    for the final assertion of Federer 2.2.14, p. 70.
    Empty Suslin domains are covered without an inhabitance premise. *)
Example borel_empty_suslin_image_regression (R : realType) (X Y : metricType R)
    (f : X -> Y) :
  is_complete_metric_space X -> is_complete_metric_space Y ->
  (exists D : set X, countable D /\ dense D) ->
  (exists D : set Y, countable D /\ dense D) ->
  is_borel_function f -> is_suslin_set R (f @` set0).
Proof.
move=> hx hy hsx hsy hf.
apply: (@borel_function_suslin_image R X Y f set0 hx hy hsx hsy hf).
exact: empty_set_suslin.
Qed.

(** Regression examples for Federer (1969), 2.2.15,
    pp. 70–71: signed integer-cell boundaries, real targets,
    and empty domains/targets. Theorems and source comparisons
    are documented in the imported modules. *)
From mathcomp Require Import all_boot all_order all_algebra ssrint boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground MetricSubsetBackground RealIntegerCells
  RealQuantisationUP BorelFunctionBasic BaireFunctions BaireRealAlgebra RealBorelBaire
  FiniteCurveApproximationUP BaireEmptyTargetBoundary BaireTargetCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [example_real_identity_baire]: regression
    for the real Borel-to-Baire converse in Federer 2.2.15,
    pp. 70–71, on the unbounded identity map. *)
Example example_real_identity_baire (R : realType) :
  is_baire_function (@id (real_line_metric R)).
Proof. apply: real_borel_function_baire; exact: identity_borel_function. Qed.

(** Source for [example_negative_integer_cell_boundary]: regression
    for the half-open cells of Federer 2.2.15, p. 71:
    at i=1, the value -1 belongs to the cell labelled -1,
    including its lower endpoint. *)
Example example_negative_integer_cell_boundary (R : realType) :
  real_integer_cell (fun _ : unit => (-1 : R)) 0 (-1)%R tt.
Proof.
rewrite /real_integer_cell /=; split; first by rewrite divr1 lexx.
by rewrite divr1 addrN /= ltrN10.
Qed.

(** Source for [example_negative_quantisation_boundary]: regression
    for the h_i approximant of Federer 2.2.15, p. 71.
    Any implementation satisfying the abstract laws must preserve
    the negative integer -1 exactly at the unit grid. *)
Example example_negative_quantisation_boundary (R : realType) (q : unit -> R) :
  is_real_quantisation (fun _ => (-1 : R)) q 0 -> q tt = -1.
Proof.
move=> hq; have [j [hj hv]] := hq tt.
have he := real_integer_cell_unique hj (@example_negative_integer_cell_boundary R).
by rewrite hv he /= divr1.
Qed.

(** Source for [example_real_target_curve_condition]: regression
    for the final target condition in Federer 2.2.15, p. 71.
    The identity curve works on R for every finite set,
    including the empty set, and every positive tolerance. *)
Example example_real_target_curve_condition (R : realType) :
  has_finite_curve_approximation [the metricType R of real_line_metric R].
Proof.
move=> Z hZ e he; exists id; split.
- by move=> x V hV.
- move=> z hz; exists z; by rewrite mdistxx.
Qed.

(** Source for [example_empty_source_baire]: regression for
    the arbitrary metric-source convention in Federer 2.2.15,
    pp. 70–71. Every map from the empty real
    subspace is continuous and hence Baire. *)
Example example_empty_source_baire (R : realType) (Y : metricType R)
    (f : metric_subset (@set0 [the metricType R of real_line_metric R]) -> Y) :
  is_baire_function f.
Proof. apply: continuous_baire_function=> x; exfalso; exact: set_valP x. Qed.

(** Source for [example_empty_target_needs_alternative]: regression
    for the local empty-target correction to Federer 2.2.15,
    p. 71. Even for the empty finite set, the
    literal curve condition cannot hold in an empty target. *)
Example example_empty_target_needs_alternative (R : realType) :
  ~ has_finite_curve_approximation
    [the metricType R of metric_subset (@set0 [the metricType R of real_line_metric R])].
Proof. apply: empty_target_curve_approximation_impossible=> y; exact: set_valP y. Qed.

(** Regression examples for Federer (1969), 2.2.16, pp. 71–72: empty support
    and maximal sets, whole-space interior cores, and the countable
    dense-set case. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum MeasureUP MeasureSupport MetricSubsetBackground
  MetricInteriorCores SeparatedMetricSetUP MaximalSeparatedSealed UlamCountable
  FiniteMeasureSupportSeparable UlamMeasureSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [example_whole_space_interior_core]: regression
    for C_n(V) in Federer 2.2.16, p. 71,
    when V is the whole space. The complement-distance
    inequality is vacuous and the core is the whole space. *)
Example example_whole_space_interior_core (R : realType) (X : metricType R) (r : R) :
  metric_interior_core (@setT X) r = setT.
Proof.
apply/seteqP; split.
- by move=> x hx.
- move=> x _ y hy; exact: False_ind _ (hy Logic.I).
Qed.

(** Source for [example_empty_maximal_separated_set]: regression
    for the maximal sets A_n in Federer 2.2.16,
    p. 71. A maximal separated subset of the empty
    set is empty; its construction does not require a point. *)
Example example_empty_maximal_separated_set (R : realType) (X : metricType R) (r : R) :
  @MaximalSeparated.value R X set0 r = set0.
Proof.
apply/seteqP; split; last by move=> x [].
exact: (@separated_subset_inside R X set0 r _ (@MaximalSeparated.laws R X set0 r)).
Qed.

(** Source for [example_countable_dense_support_complement_null]:
    regression for the Ulam hypothesis in Federer 2.2.16,
    pp. 71–72. A countable dense set suffices,
    by the countable Ulam case proved in 2.1.6, p. 58. *)
Example example_countable_dense_support_complement_null (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set X) :
  mu setT < +oo -> (forall V, open V -> measure_measurable mu V) ->
  countable D -> dense D -> mu (~` measure_support mu) = 0.
Proof.
move=> hf ho hc hd; apply: (@finite_measure_ulam_dense_support_complement_null R X mu hm D hf ho hd).
exact: ulam_set_countable hc.
Qed.

(** Source for [example_zero_measure_support_separable]: regression
    for the empty-support case of the first assertion in
    Federer 2.2.16, p. 71. The zero measure
    satisfies all hypotheses even on a nonseparable ambient space. *)
Example example_zero_measure_support_separable (R : realType) (X : metricType R) :
  exists D : set (metric_subset (measure_support (fun _ : set X => (0 : \bar R)))),
    countable D /\ dense D.
Proof.
have hm : is_measure (fun _ : set X => (0 : \bar R)).
  constructor; first by move=> A; rewrite lexx.
  move=> A G hG hcover.
  have hz B : G B -> (0 : \bar R) = 0 by [].
  by rewrite (nonnegative_sum_zero hz) lexx.
have ho V : open V -> measure_measurable (fun _ : set X => (0 : \bar R)) V.
  by move=> hV A; rewrite adde0.
apply: (@finite_measure_support_separable R X _ hm _ ho); exact: ltry.
Qed.

(** Regression examples for Federer (1969), 2.2.17, p. 72: identity images,
    compact sources and exact empty-set outer neighborhoods. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasurePushforward RadonMeasureUP ProperMapUP
  ProperImageComplement RadonProperPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [example_identity_proper]: regression for
    the properness definition in Federer 2.2.17, p. 72.
    The identity map preserves compact sets under inverse image. *)
Example example_identity_proper (X : topologicalType) : is_proper_map (@id X).
Proof. by move=> K hK. Qed.

(** Source for [example_identity_radon_pushforward]: regression
    for the Radon image conclusion in Federer 2.2.17,
    p. 72. Identity pushforward is Radon without
    adding a finite-total-measure assumption. *)
Example example_identity_radon_pushforward (R : realType) (X : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (hr : is_radon_measure mu) :
  is_radon_measure (measure_pushforward (@id X) mu).
Proof.
apply: (@proper_continuous_radon_pushforward R X X mu hm hr id
  (radon_hausdorff hr) (radon_locally_compact hr) _ (@example_identity_proper X)).
by move=> x V hV.
Qed.

(** Source for [example_compact_source_countable_cover]: regression
    for the countable compact-cover hypothesis in Federer
    2.2.17, p. 72. A compact space, including
    an empty compact space, has the singleton cover by itself. *)
Example example_compact_source_countable_cover (X : topologicalType) :
  compact (@setT X) -> has_countable_compact_cover X.
Proof.
move=> hX; exists [set (@setT X)]; split; first exact: countable1.
split; first by move=> K ->.
apply/seteqP; split; first by move=> x hx.
move=> x hx; exists setT=> //.
Qed.

(** Source for [example_empty_set_outer_neighborhood_exact]: regression
    for the displayed open-neighborhood requirement in Federer
    2.2.17, p. 72. For the empty set, the
    open complement of the image gives exact zero measure,
    including when the source measure has infinite total mass. *)
Example example_empty_set_outer_neighborhood_exact (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : X -> Y) :
  hausdorff_space Y -> locally_compact (@setT Y) -> continuous f -> is_proper_map f ->
  exists W, open W /\ (@set0 Y) `<=` W /\ measure_pushforward f mu W = 0.
Proof.
move=> hY hl hf hp; exists (~` (f @` setT)); split.
- exact: proper_continuous_image_complement_open hY hl hf hp.
- split; first by move=> x [].
  exact: (@pushforward_subset_outside_image_null R X Y mu hm f _ (fun y hy => hy)).
Qed.

(** Regression examples for Federer (1969), 2.3.1, p. 72. The imported
    declarations give Source context and precise conventions. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasureUP MeasureBasic
  MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [almost_on_empty_set_regression]: empty-relative-set
    regression for the final paragraph of Federer 2.3.1, p. 72. *)
Example almost_on_empty_set_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (P : set X) :
  is_measure mu -> measure_almost_everywhere_on mu set0 P.
Proof. by move=> hm; rewrite /measure_almost_everywhere_on set0D (measure_empty hm). Qed.

(** Source for [total_function_almost_reflexive_regression]:
    total-domain regression for almost equality in Federer 2.3.1,
    p. 72; no finite-measure or nonzero-measure premise is required. *)
Example total_function_almost_reflexive_regression (R : realType)
    (X : choiceType) (Y : Type) (mu : set X -> \bar R) (f : X -> Y) :
  is_measure mu -> measure_almost_equal mu (partial_function_total f) (partial_function_total f).
Proof.
move=> hm; rewrite measure_almost_equal_self partial_function_total_domain.
exact: measure_almost_everywhere_true hm.
Qed.

(** Source for [zero_measure_empty_target_almost_regression]:
    zero-measure and empty-target regression for Federer 2.3.1,
    p. 72. A function with empty domain is admissible here;
    no default value in the target has been chosen. *)
Example zero_measure_empty_target_almost_regression (R : realType) :
  measure_almost_equal (fun _ : set unit => (0 : \bar R))
    (@partial_function_empty unit Empty_set) (@partial_function_empty unit Empty_set).
Proof. by rewrite measure_almost_equal_empty_self. Qed.

(** Source for [empty_domain_not_almost_reflexive_regression]:
    nonnull-domain regression for the equality locus in Federer
    2.3.1, p. 72. Undefined values are not treated as equal values. *)
Example empty_domain_not_almost_reflexive_regression (R : realType)
    (X : choiceType) (Y : Type) (mu : set X -> \bar R) :
  mu setT <> 0 ->
  ~ measure_almost_equal mu (@partial_function_empty X Y) (@partial_function_empty X Y).
Proof. by rewrite measure_almost_equal_empty_self. Qed.

(** Regression examples for Federer (1969), 2.3.2, pp. 73–74: partial
    domains, empty targets and empty extrema. Source context and
    qualifications: MeasurableFunctionUP.v, PartialFunctionExtensionUP.v and
    PartialFunctionSupremumUP.v. *)
From mathcomp Require Import all_boot all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  PartialFunctionExtensionUP PartialFunctionPostcomposition MeasureUP MeasurableFunctionUP
  MeasurableFunctionBasic ExtendedRealOrderTopology PartialFunctionSupremumUP
  PartialFunctionInfimumUP PartialFunctionExtrema PartialFunctionSupremumSealed
  PartialFunctionInfimumSealed MeasurableCountableSupremum MeasurableCountableInfimum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_empty_intersection_preimage_regression]:
    regression for the Borel-family argument in Federer 2.3.2,
    p. 73. An empty intersection has preimage the partial
    domain, which need not be the whole measured space. *)
Example partial_empty_intersection_preimage_regression (X Y : Type) (f : partial_function X Y) :
  partial_function_preimage f (\bigcap_(j in (@set0 nat)) (@set0 Y)) = partial_function_domain f.
Proof. by rewrite bigcap_set0 partial_function_preimage_whole. Qed.

(** Source for [empty_target_extension_counterexample]: local
    boundary counterexample to the unqualified extension remark in
    Federer 2.3.2, p. 73, second paragraph. The empty
    function on the one-point null source is measurable into the
    empty space but has no total extension into that target.
    This is not a correction listed in Federer's erratum. *)
Example empty_target_extension_counterexample (R : realType) :
  is_measure_measurable_function (fun _ : set unit => (0 : \bar R))
    (@partial_function_empty unit (discrete_topology Empty_set)) /\
  ~ exists h : unit -> discrete_topology Empty_set,
    is_partial_function_total_extension (@partial_function_empty unit (discrete_topology Empty_set)) h.
Proof.
split.
- constructor; first by [].
  by move=> U ho A; rewrite adde0.
- by move=> [h _]; case: (h tt).
Qed.

(** Source for [empty_product_needs_conull_domain_regression]: regression
    for the standing domain hypothesis in Federer 2.3.2(5), p. 73, explicit.
    An empty family of projection tests alone imposes no domain condition. *)
Example empty_product_needs_conull_domain_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) : mu setT <> 0 ->
  ~ is_measure_measurable_function mu
    (@partial_function_empty X (prod_topology (fun _ : Empty_set => discrete_topology unit))) /\
  forall i : Empty_set, is_measure_measurable_function mu
    (partial_function_postcompose
      (@partial_function_empty X (prod_topology (fun _ : Empty_set => discrete_topology unit)))
      (fun y => y i)).
Proof.
move=> hn; split; last by move=> [].
move=> hf; apply: hn.
exact: (proj1 (@measurable_empty_function_iff R X _ mu hm) hf).
Qed.

(** Source for [empty_family_supremum_regression]: regression for
    the empty-family convention of Federer 2.3.2, p. 74,
    inherited from 2.1.1, p. 51. *)
Example empty_family_supremum_regression (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : J -> partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu (@PartialFunctionSupremum.value R X J set0 f) /\
  forall x, partial_function_graph (@PartialFunctionSupremum.value R X J set0 f) x -oo.
Proof.
split.
- apply: (@measurable_sealed_countable_supremum R X J mu hm set0 f); first exact: countable0.
  by move=> j [].
- exact: (@partial_supremum_empty_graph R X J f _ (@PartialFunctionSupremum.laws R X J set0 f)).
Qed.

(** Source for [empty_family_infimum_regression]: regression for
    the empty-family infimum in Federer 2.3.2, p. 74,
    using the plus-infinity convention in 2.1.1, p. 51. *)
Example empty_family_infimum_regression (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : J -> partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu (@PartialFunctionInfimum.value R X J set0 f) /\
  forall x, partial_function_graph (@PartialFunctionInfimum.value R X J set0 f) x +oo.
Proof.
split.
- apply: (@measurable_sealed_countable_infimum R X J mu hm set0 f); first exact: countable0.
  by move=> j [].
- exact: (@partial_infimum_empty_graph R X J f _ (@PartialFunctionInfimum.laws R X J set0 f)).
Qed.

From Federer Require Import PartialExtendedArithmetic ExtendedRealPartial
  PartialFunctionLimitExtremaUP PartialFunctionUpperLimitSealed PartialFunctionLowerLimitSealed
  MetricSetSeparationInfimum ExtendedRealBounds.

(** Source for [opposite_infinity_function_sum_undefined]: regression
    for the domain proviso in Federer 2.3.2, p. 74,
    with the undefined scalar pair from 2.1.1, p. 51. *)
Example opposite_infinity_function_sum_undefined (R : realType) (X : Type) :
  partial_function_domain (partial_extended_function_add
    (partial_function_total (fun _ : X => (+oo : extended_real_line R)))
    (partial_function_total (fun _ : X => (-oo : extended_real_line R)))) = set0.
Proof.
apply/seteqP; split=> x; last by [].
move=> [z hz]; have [a [b [ha [hb he]]]] := (proj1 (partial_extended_function_add_graph _ _ _ _)) hz.
change ((+oo : extended_real_line R) = a) in ha.
change ((-oo : extended_real_line R) = b) in hb.
by rewrite -ha -hb extended_add_opposite_infinities in he.
Qed.

(** Source for [zero_infinity_function_product_undefined]: regression
    for ordinary partial multiplication in Federer 2.3.2,
    p. 74. The zero-product convention is not used implicitly. *)
Example zero_infinity_function_product_undefined (R : realType) (X : Type) :
  partial_function_domain (partial_extended_function_multiply
    (partial_function_total (fun _ : X => (0 : extended_real_line R)))
    (partial_function_total (fun _ : X => (+oo : extended_real_line R)))) = set0.
Proof.
apply/seteqP; split=> x; last by [].
move=> [z hz]; have [a [b [ha [hb he]]]] := (proj1 (partial_extended_function_multiply_graph _ _ _ _)) hz.
change ((0 : extended_real_line R) = a) in ha.
change ((+oo : extended_real_line R) = b) in hb.
by rewrite -ha -hb extended_multiply_zero_infinity in he.
Qed.

(** Source for [initially_undefined_sequence]: Supporting Federer 2.3.2, p.
    74. *)
Definition initially_undefined_sequence (R : realType) (X : Type) n :
    partial_function X (extended_real_line R) :=
  if n is 0%N then partial_function_empty X (extended_real_line R)
  else partial_function_total (fun _ : X => (+oo : extended_real_line R)).

(** Source for [initially_undefined_common_domain_empty]: regression showing
    that the common domain can be smaller than the eventual domain in the
    limit assertion of Federer 2.3.2, p. 74 *)
Example initially_undefined_common_domain_empty (R : realType) (X : Type) :
  partial_function_common_domain setT (@initially_undefined_sequence R X) = set0.
Proof.
apply/seteqP; split=> x; last by [].
move=> hx; have h := hx 0%N Logic.I; by move: h=> [y []].
Qed.

(** Source for [initially_undefined_eventual_domain_whole]: regression for
    the full eventual domain of lower and upper limits in Federer 2.3.2, p.
    74 *)
Example initially_undefined_eventual_domain_whole (R : realType) (X : Type) :
  partial_function_eventual_domain (@initially_undefined_sequence R X) = setT.
Proof.
apply/seteqP; split=> x; first by [].
move=> _; exists 1%N=> -[|n] // hn.
exists +oo; by [].
Qed.

(** Source for [initially_undefined_limit_domains_regression]: regression
    that both sealed limit functions retain all eventually defined points,
    rather than only the common domain; Federer 2.3.2, p. 74. *)
Example initially_undefined_limit_domains_regression (R : realType) (X : Type) :
  partial_function_domain (@PartialFunctionUpperLimit.value R X (@initially_undefined_sequence R X)) = setT /\
  partial_function_domain (@PartialFunctionLowerLimit.value R X (@initially_undefined_sequence R X)) = setT.
Proof.
split.
- rewrite (partial_function_upper_limit_domain (PartialFunctionUpperLimit.laws _)).
  exact: initially_undefined_eventual_domain_whole.
- rewrite (partial_function_lower_limit_domain (PartialFunctionLowerLimit.laws _)).
  exact: initially_undefined_eventual_domain_whole.
Qed.

(** Source for [empty_set_metric_distance_infinite]: regression
    for the empty-set case of the positive-distance criteria in
    Federer 2.3.2(8)–(9), pp. 74–75, using the empty
    infimum convention of 2.1.1, p. 51. *)
Example empty_set_metric_distance_infinite (R : realType) (Y : metricType R) (B : set Y) :
  metric_set_distance_infimum set0 B = +oo.
Proof.
have he : metric_set_cross_distances (@set0 Y) B = set0.
  apply/seteqP; split=> t; [by move=> [x [[] _]]|by []].
by rewrite /metric_set_distance_infimum he extended_real_inf_empty.
Qed.

(** Regression examples for Federer (1969), 2.3.3, p. 76: equality at the
    greedy threshold, zero target, and infinite target. Source context:
    WeightedCharacteristicExpansionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import GreedyCharacteristicSystemUP WeightedCharacteristicExpansionUP
  CharacteristicFunctionUP GreedySystemPartialSums GreedyScalarBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [greedy_threshold_equality_selected]: regression
    for the non-strict comparison in the recursion of Federer
    2.3.3, p. 76. A target equal to the first weight
    selects the first set at every source point. *)
Example greedy_threshold_equality_selected (R : realType) (X : Type)
    (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  is_greedy_characteristic_system (fun _ : X => (r 0%N)%:E) r A g -> A 0%N = setT.
Proof.
move=> hs; apply/seteqP; split=> x; first by [].
move=> _; apply: (proj2 (greedy_system_threshold hs 0%N x)).
by rewrite big_ord0 addr0.
Qed.

(** Source for [greedy_infinite_target_selects_every_weight]: regression
    for the positive-infinity target permitted in Federer 2.3.3,
    p. 76. Every finite partial sum plus the next real weight
    lies below infinity, so all characteristic values are one. *)
Example greedy_infinite_target_selects_every_weight (R : realType) (X : Type)
    (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  is_greedy_characteristic_system (fun _ : X => (+oo : \bar R)) r A g ->
  forall n, A n = setT /\ forall x, g n x = 1%R.
Proof.
move=> hs n; have ha x : A n x.
  apply: (proj2 (greedy_system_threshold hs n x)); exact: leey.
split.
- apply/seteqP; split=> x; [by []|by move=> _; exact: ha].
- move=> x; exact (@characteristic_on_set R X (A n) (g n) (greedy_system_characteristic hs n) x (ha x)).
Qed.

(** Source for [greedy_zero_target_omits_every_weight]: regression
    for the zero target in Federer 2.3.3, p. 76.
    Strict positivity of the prescribed weights forces every set
    to be empty and every characteristic value to be zero. *)
Example greedy_zero_target_omits_every_weight (R : realType) (X : Type)
    (r : nat -> R) (A : nat -> set X) (g : nat -> X -> R) :
  (forall n, (0 < r n)%R) ->
  is_greedy_characteristic_system (fun _ : X => (0 : \bar R)) r A g ->
  forall n, A n = set0 /\ forall x, g n x = 0%R.
Proof.
move=> hr hs n; have ha x : ~ A n x.
  move=> hx; have hc := (proj1 (greedy_system_threshold hs n x)) hx.
  have hscalar := @greedy_system_scalar_laws R X (fun _ => (0 : \bar R)) r A g hs x.
  have hb := (@greedy_scalar_bounds R r 0 _ (fun k => ltW (hr k)) (lexx _) hscalar n).1.
  have hp : (0 < r n + greedy_system_partial_sum r g n x)%R.
    have hle : (r n <= r n + greedy_system_partial_sum r g n x)%R by rewrite lerDl.
    exact: lt_le_trans (hr n) hle.
  have hc' : (r n + greedy_system_partial_sum r g n x <= 0)%R.
    by move: hc; rewrite lee_fin.
  have hbad := lt_le_trans hp hc'; by rewrite ltxx in hbad.
split.
- apply/seteqP; split=> x; [by move=> hx; exact: ha x hx|by []].
- move=> x; exact (@characteristic_off_set R X (A n) (g n) (greedy_system_characteristic hs n) x (ha x)).
Qed.

(** Regression examples for Federer (1969), 2.3.4, p. 76: countable
    measurability allows infinite total measure, and the zero function does
    not require a countably measurable source. editions:
    CountablyMeasurableUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import CountingMeasure NonnegativeSum NonnegativeSumSupport
  CountablyMeasurableUP CountablyMeasurableSequences CountablyMeasurableFunctions
  PartialFunctionBasic MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_measurable_infinite_counting_source]: regression
    distinguishing countable measurability from finite measure in
    Federer 2.3.4, p. 76, using the counting measure of
    2.1.2, p. 54. The natural numbers have an infinite
    counting measure but are a countable union of finite measurable singletons. *)
Example countably_measurable_infinite_counting_source (R : realType) :
  measure_countably_measurable (@counting_measure R nat) setT /\
  counting_measure (R := R) (@setT nat) = +oo.
Proof.
split.
- apply: (proj2 (@countably_measurable_sequence_iff R nat _ (counting_measure_is_measure R nat) setT)).
  exists (fun n => [set n]); split.
  + apply/seteqP; split=> n; [by move=> _; exists n|by []].
  + move=> n; split; first exact: counting_measure_measurable.
    rewrite counting_measure_sum nonnegative_sum_singleton; first exact: ltry.
    by rewrite lee_fin ler01.
- apply: counting_measure_infinite; exact: infinite_nat.
Qed.

(** Source for [zero_function_countably_measurable_without_source_bound]:
    regression for the nonzero-locus definition of Federer 2.3.4,
    p. 76. Even with infinite total source measure, the
    zero function has empty support and is countably measurable. *)
Example zero_function_countably_measurable_without_source_bound (R : realType)
    (X : choiceType) (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (zero : Y) : mu setT = +oo ->
  is_countably_measure_measurable_function mu zero (partial_function_total (fun _ : X => zero)).
Proof. move=> _; exact: (@countably_measurable_zero_function R X Y mu hm zero). Qed.

(** Boundary regressions for Federer (1969), 2.3.5, pp. 76–77; Source
    context: LusinMetric.v. These check empty partial domains, infinite
    source measure outside the finite set, and agreement with ordinary
    subspace continuity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialContinuityUP
  PartialContinuityTotal MeasureUP MeasureBasic MeasureAlmostBasic
  MeasurableFunctionUP MeasurableFunctionBasic BorelRegularMeasureUP LusinMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lusin_empty_domain_null_source]: regression for
    Federer 2.3.5, pp. 76–77, with an empty function domain.
    Measurability forces a null source, and the empty closed set
    works even if the target is empty. *)
Example lusin_empty_domain_null_source (R : realType) (X Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (e : R) :
  is_measure_measurable_function mu (@partial_function_empty X Y) ->
  (0 < e)%R -> closed (@set0 X) /\ mu (A `\` set0) < e%:E /\
  partial_function_continuous_on set0 (@partial_function_empty X Y).
Proof.
move=> hf he; split; first exact: closed0.
split; last exact: partial_continuity_empty.
have ht := (proj1 (@measurable_empty_function_iff R X Y mu hm)) hf.
have hA : mu A = 0.
  apply: (@measure_null_subset R X mu hm A setT)=> //; by move=> x _.
by rewrite setD0 hA lte_fin.
Qed.

(** Source for [lusin_total_function_subspace_continuity]: regression
    that the conclusion of Federer 2.3.5, p. 77, gives ordinary
    continuous restriction for a total map. The whole source may
    have infinite measure; only the displayed A is finite. *)
Example lusin_total_function_subspace_continuity (R : realType)
    (X Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu) (D : set Y) (A : set X)
    (g : X -> Y) (e : R) : countable D -> dense D ->
  is_measure_measurable_function mu (partial_function_total g) ->
  measure_measurable mu A -> mu A < +oo -> mu setT = +oo -> (0 < e)%R ->
  exists C, closed C /\ C `<=` A /\ mu (A `\` C) < e%:E /\
    {within C, continuous g}.
Proof.
move=> hc hd hf hA hfin _ he.
have [C [hC [hCA [herr hcont]]]] := @lusin_borel_regular R X Y mu hm hr D A
  (partial_function_total g) e hc hd hf hA hfin he.
exists C; split=> //; split=> //; split=> //.
exact: (proj1 (partial_continuity_total_iff C g)) hcont.
Qed.

(** Boundary regressions for Federer (1969), 2.3.6, p. 77. Source context:
    LusinBorelVersion.v and MeasurableFiniteImageSupport.v. The two
    qualifications below are local clarifications, not entries in Federer's
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP
  MeasureUP MeasureBasic CountablyMeasurableUP CountablyMeasurableBasic
  MeasureRestriction MeasurePushforward MeasureSupport CountingMeasure NonnegativeSumSupport
  RealContinuousExtensionUP RealContinuousExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [borel_version_empty_target_counterexample]: local
    boundary correction to the total-map assertion in Federer
    2.3.6, p. 77. A countably measurable one-point null
    source admits the measurable empty partial function but no
    total map into the empty target. *)
Example borel_version_empty_target_counterexample (R : realType) :
  measure_countably_measurable (fun _ : set unit => (0 : \bar R)) setT /\
  is_measure_measurable_function (fun _ : set unit => (0 : \bar R))
    (@partial_function_empty unit (discrete_topology Empty_set)) /\
  ~ exists h : unit -> Empty_set, True.
Proof.
split.
- apply: finite_measurable_set_countably_measurable; last exact: ltry.
  by move=> T; rewrite adde0.
- split.
  + constructor; first by [].
    by move=> U hU T; rewrite adde0.
  + by move=> [h _]; case: (h tt).
Qed.

(** Source for [restricted_image_support_is_only_relative]: local
    clarification of the last sentence in Federer 2.3.6, p. 77.
    For A empty the restricted image support is empty, while the
    whole counting measure still has unit mass outside that support.
    Thus the support controls f on A, not on the whole source. *)
Example restricted_image_support_is_only_relative (R : realType) :
  let mu := @counting_measure R unit in
  let g := fun _ : unit => tt in
  let S := @measure_support R (discrete_topology unit)
    (measure_pushforward g (measure_restrict mu set0)) in
  S = set0 /\ mu (g @^-1` (~` S)) = 1.
Proof.
move=> mu g S.
have hnu : measure_pushforward g (measure_restrict mu set0) =
    (fun _ : set unit => (0 : \bar R)).
  apply: funext=> B; rewrite /measure_pushforward /measure_restrict set0I.
  exact: measure_empty (counting_measure_is_measure R unit).
have hS : S = set0 by rewrite /S hnu measure_support_zero.
split; first exact hS.
rewrite hS setC0 preimage_setT.
have hwhole : (@setT unit) = [set tt] by apply/seteqP; split=> [[] _|x _] //.
by rewrite hwhole /mu counting_measure_sum nonnegative_sum_singleton.
Qed.

(** Source for [tietze_extension_unbounded_identity]: regression
    that the Tietze step in Federer 2.3.6, p. 77, imposes
    no boundedness hypothesis. On the whole real line the extension
    of the identity retains every real value. *)
Example tietze_extension_unbounded_identity (R : realType) (hn : normal_space R^o) :
  exists h : R^o -> R^o, continuous h /\ forall x, h x = x.
Proof.
have hf : {within (@setT R^o), continuous (fun x : R^o => x)}.
  apply: continuous_subspaceT; move=> x; exact: cvg_id.
pose h := @RealContinuousExtension.value R R^o hn setT closedT (fun x => x) hf.
have hh := @RealContinuousExtension.laws R R^o hn setT closedT (fun x => x) hf.
exists h; split; first exact: hh.1.
move=> x; exact: hh.2 x Logic.I.
Qed.

(** Boundary regressions for Federer (1969), 2.3.7, pp. 77–78. Source
    context: UniformPartialConvergenceUP.v. These check exact partial
    domains and the null-source case without requiring a target point. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic UniformPartialConvergenceUP
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_constant_partial_sequence_regression]:
    zero-error boundary for the uniform convergence of Federer
    2.3.7, p. 77. A constant sequence of partial functions
    converges uniformly on precisely its given domain. *)
Example uniform_constant_partial_sequence_regression (R : realType) (X : Type)
    (Y : metricType R) (f : partial_function X Y) :
  partial_function_uniformly_converges_on (partial_function_domain f) (fun _ => f) f.
Proof.
constructor.
- move=> x hx; split=> // n _; exact hx.
- move=> e he; exists 0%N=> n _ x y z hx hy hz.
  have heq := @partial_function_single_valued X Y f x y z hy hz.
  by rewrite heq mdistxx.
Qed.

(** Source for [uniform_partial_domain_is_not_vacuous]: Supporting Federer
    2.3.7, pp. 77–78.Undefined values cannot make uniform convergence hold
    vacuously on a nonempty set. *)
Example uniform_partial_domain_is_not_vacuous (R : realType) (X : Type)
    (Y : metricType R) (B : set X) (f : nat -> partial_function X Y) :
  B !=set0 -> ~ partial_function_uniformly_converges_on B f (@partial_function_empty X Y).
Proof.
move=> [x hx] hu.
have hh := @uniform_partial_domain R X Y B f (@partial_function_empty X Y) hu x hx.
have [y hy] := hh.1; exact hy.
Qed.

(** Source for [egoroff_null_source_empty_functions]: regression
    for the null-source boundary of Federer 2.3.7, pp. 77–78.
    Empty partial functions admit the empty uniform-convergence set,
    even if the target itself is empty. *)
Example egoroff_null_source_empty_functions (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu) (A : set X) (e : R) :
  mu setT = 0 -> (0 < e)%R -> measure_measurable mu set0 /\
  mu (A `\` set0) < e%:E /\
  partial_function_uniformly_converges_on set0 (fun _ => @partial_function_empty X Y)
    (@partial_function_empty X Y).
Proof.
move=> ht he; split; first exact: measure_measurable_empty hm.
split.
- have hA : mu A = 0.
    apply: (@measure_null_subset R X mu hm A setT)=> //; by move=> x _.
  by rewrite setD0 hA lte_fin.
- constructor; first by move=> x [].
  move=> delta hd; exists 0%N=> n hn x y z [].
Qed.

(** Boundary regressions for Federer (1969), 2.3.8, pp. 78–79. Source
    context and the correction to the partial-domain collection:
    MeasurableNormedFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureBasic MeasureAlmostUP CountingMeasure NonnegativeSum
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureGauge MeasureGaugeComparison
  CountingMeasureInfiniteGauge MeasureGaugeNonhomogeneity FiniteCountingFunctionExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinite_gauge_zero_scalar_regression]: regression
    for the infinite-distance and zero-scalar conventions in Federer
    2.3.8, pp. 78–79. The natural-value function has
    infinite counting gauge; multiplying it by zero has gauge zero. *)
Example infinite_gauge_zero_scalar_regression (R : realType) :
  let f := partial_function_total (fun n : nat => (n%:R : R)) in
  measure_gauge (@counting_measure R nat) (fun y : R => `|y|%R) f = +oo /\
  measure_gauge (@counting_measure R nat) (fun y : R => `|y|%R) (@partial_vector_scale R nat R^o 0%R f) = 0.
Proof.
move=> f; split; first exact: counting_natural_function_infinite_gauge.
apply: measure_gauge_zero_of_null_superlevel.
have he : partial_norm_superlevel (fun y : R => `|y|%R) (@partial_vector_scale R nat R^o 0%R f) 0 = set0.
  apply/seteqP; split=> n; last by [].
  move=> [y [hy hn]]; have [z [_ hz]] := proj1 (@partial_vector_scale_graph R nat R^o 0%R f n y) hy.
  have hn' : (0 < `|y|)%R := hn.
  by rewrite hz scale0r normr0 ltxx in hn'.
rewrite he; exact: measure_empty (counting_measure_is_measure R nat).
Qed.

(** Source for [partial_null_zero_domain_regression]: the partial zero on an
    empty domain belongs to A(mu,R) for the null measure on a nonempty
    source. It is idempotent under pointwise addition but differs from the
    total zero. This regression reflects Federer's erratum p. 1, book p. 78
    line 7; our null-measure witness is simpler than the Lebesgue-null
    deletion used in that footnote. *)
Example partial_null_zero_domain_regression (R : realType) :
  let M := real_norm_metric_space (scalar_absolute_value_norm R) in
  let mu := fun _ : set unit => (0 : \bar R) in
  let f := @partial_function_empty unit M in
  @is_measurable_normed_function R unit R^o _ (scalar_absolute_value_norm R) mu f /\
  (forall x y, partial_function_graph (partial_vector_add f f) x y <-> partial_function_graph f x y) /\
  f <> partial_function_total (fun _ : unit => (0%R : M)).
Proof.
move=> M mu f.
have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hzero := @measurable_normed_total_constant R unit R^o _ (scalar_absolute_value_norm R) mu hm (0%R : M).
split.
- apply: (@measurable_normed_almost_equal R unit R^o _ (scalar_absolute_value_norm R) mu hm
    (partial_function_total (fun _ => (0%R : M))) f hzero).
  by [].
split.
- move=> x y; split; last by [].
  move/partial_vector_add_graph=> [a [b [ha _]]]; exact ha.
- move=> heq.
  have ht : partial_function_graph (partial_function_total (fun _ : unit => (0%R : M))) tt (0%R : M) by [].
  by rewrite -heq in ht.
Qed.

(** Source for [unit_counting_gauge_saturation_regression]: the
    characteristic formula of Federer 2.3.8, p. 78,
    saturates at the source mass. The zero constant has gauge
    zero; every constant at least one on a point of mass one
    has gauge one. This checks both branches of the minimum. *)
Example unit_counting_gauge_saturation_regression (R : realType) (c : R) : (1 <= c)%R ->
  measure_gauge (@counting_measure R unit) (fun y : R => `|y|%R)
    (partial_function_total (fun _ => 0%R)) = 0 /\
  measure_gauge (@counting_measure R unit) (fun y : R => `|y|%R)
    (partial_function_total (fun _ => c)) = 1.
Proof.
move=> hc; split.
- by rewrite unit_counting_constant_gauge // min_l // lee_fin ler01.
- rewrite unit_counting_constant_gauge; last exact: le_trans ler01 hc.
  by rewrite min_r // lee_fin.
Qed.

(** Boundary regressions for Federer (1969), 2.3.9, pp. 79–80. Source
    context: MeasureSummableConvergence.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP PartialFunctionPointwiseLimitUP PartialFunctionPointwiseLimitSealed
  NonnegativeSum MeasureUP MeasureAlmostUP CountingMeasure
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureGauge MeasureConvergenceUP MeasureDistanceLaws
  CountingMeasureInfiniteGauge ScalarNormMetricCompleteness MeasureSummableConvergence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinite_gauge_stationary_convergence_regression]:
    regression for Federer 2.3.9, pp. 79–80. A stationary
    sequence of functions with infinite gauge still satisfies the
    summable-increment hypothesis and converges; no finite total
    measure or finite individual gauge is required. *)
Example infinite_gauge_stationary_convergence_regression (R : realType) :
  let M := real_norm_metric_space (scalar_absolute_value_norm R) in
  let mu := @counting_measure R nat in
  let f := partial_function_total (fun n : nat => (n%:R : M)) in
  measure_gauge mu (fun y : R => `|y|%R) f = +oo /\
  exists h : partial_function nat M,
    @is_measurable_normed_function R nat R^o _ (scalar_absolute_value_norm R) mu h /\
    measure_almost_everywhere mu (partial_function_limit_locus (fun _ => f) h) /\
    @converges_in_measure R nat R^o mu (fun y : R => `|y|%R) (fun _ => f) h.
Proof.
move=> M mu f; split; first exact: counting_natural_function_infinite_gauge.
have hm := counting_measure_is_measure R nat.
have hf := counting_natural_function_measurable_normed R.
have hs : nonnegative_sum setT (fun _ : nat => @measure_normed_distance R nat R^o mu
    (fun y : R => `|y|%R) f f) < +oo.
  have hz : forall n, (@setT nat) n -> @measure_normed_distance R nat R^o mu
      (fun y : R => `|y|%R) f f = 0.
    move=> n _; exact: (@measure_normed_distance_self R nat R^o _ (scalar_absolute_value_norm R) mu hm f hf).
  rewrite (nonnegative_sum_zero hz); exact: ltry.
exact (@summable_successive_measure_distances_converge R nat R^o _ (scalar_absolute_value_norm R)
  (@scalar_norm_metric_complete R) mu hm (fun _ => f) (fun _ => hf) hs).
Qed.

(** Source for [empty_partial_pointwise_limit_regression]: the
    sealed pointwise-limit graph retains an empty common domain,
    supporting the partial-function convention in Federer 2.3.9,
    pp. 79–80. It does not fabricate a default limit value. *)
Example empty_partial_pointwise_limit_regression (R : realType) (X : Type)
    (Y : metricType R) :
  partial_function_domain (@PartialFunctionPointwiseLimit.value R X Y
    (fun _ => @partial_function_empty X Y)) = set0.
Proof.
apply/seteqP; split; last by move=> x [].
move=> x [y hy].
have [u [hu _]] := (proj1 (@PartialFunctionPointwiseLimit.laws R X Y
  (fun _ => @partial_function_empty X Y) x y)) hy.
exact: hu 0%N.
Qed.

(** Boundary regressions for Federer (1969), 2.3.10, p. 80. Source context:
    CauchyIndexSelectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitUP NonnegativeSum MeasureUP MeasureAlmostUP
  MeasurableNormedFunctionUP MeasurableNormedBasic MeasureGauge MeasureConvergenceUP
  CauchyIndexSelectionUP CauchyIndexSelectionSealed CauchyIndexSelectionLaws MeasureFunctionCompleteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_distance_strict_subsequence_regression]:
    even when all distances vanish, the selected indices form a
    genuine cofinal subsequence for Federer 2.3.10, p. 80;
    they do not repeat a single index forever. *)
Example zero_distance_strict_subsequence_regression (R : realType) :
  exists s : nat -> nat, (forall n, (s n < s n.+1)%N) /\ forall n, (n <= s n)%N.
Proof.
have hc (n : nat) : exists K, forall i j, (K <= i)%N -> (K <= j)%N ->
    (0 : \bar R) < (1%R : R)%:E.
  exists 0%N=> i j hi hj; exact: ltr01.
pose s := @CauchyIndexSelection.value R (fun _ _ => 0) (fun _ => 1%R) hc.
have hs := @CauchyIndexSelection.laws R (fun _ _ => 0) (fun _ => 1%R) hc.
exists s; split; first exact hs.1.
exact: strict_index_sequence_dominates hs.1.
Qed.

(** Source for [null_measure_partial_sequence_completeness_regression]:
    completeness in Federer 2.3.10, p. 80, includes
    zero measures and arbitrary partial domains. Every sequence
    satisfies the conclusion in this case. *)
Example null_measure_partial_sequence_completeness_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (f : nat -> partial_function X (real_norm_metric_space hN)) :
  let mu := fun _ : set X => (0 : \bar R) in
  exists (h : partial_function X (real_norm_metric_space hN)) (s : nat -> nat),
    is_measurable_normed_function mu h /\ (forall n, (s n < s n.+1)%N) /\
    measure_almost_everywhere mu (partial_function_limit_locus (fun n => f (s n)) h) /\
    converges_in_measure mu N (fun n => f (s n)) h /\ converges_in_measure mu N f h.
Proof.
move=> mu.
have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf n : is_measurable_normed_function mu (f n).
  have hz := @measurable_normed_total_constant R X V N hN mu hm (0%R : real_norm_metric_space hN).
  apply: (@measurable_normed_almost_equal R X V N hN mu hm _ (f n) hz); by [].
apply: (@measurable_function_space_complete R X V N hN hY mu hm f hf).
move=> e he; exists 0%N=> n m hn hm'.
have hee : (0 : \bar R) < e%:E by rewrite lte_fin.
apply: le_lt_trans _ hee.
apply: measure_gauge_bound; split; exact: lexx.
Qed.

(** Boundary regressions for Federer (1969), 2.4.1, pp. 80–81. Source
    context and extended-sum convention: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP CountingMeasure ExtendedRealPartial MeasureStepFunctionUP MeasureStepConstants
  MeasureStepScalarOperation MeasureStepScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinite_step_zero_scale_regression]: the
    step sum may be infinite, and zero scaling has assigned
    value zero, under Federer 2.4.1, p. 80. *)
Example infinite_step_zero_scale_regression (R : realType) :
  let mu := @counting_measure R nat in
  let u := partial_function_total (fun _ : nat => (1%R : real_line_metric R)) in
  is_measure_step_function mu u /\ is_measure_step_integral mu u +oo /\
  is_measure_step_integral mu (partial_real_function_scale 0%R u) 0.
Proof.
move=> mu u; have hm := counting_measure_is_measure R nat.
have ht : mu setT = +oo := @counting_measure_infinite R nat setT infinite_nat.
split; first exact: measure_step_constant.
split; last exact: measure_step_integral_zero_scale.
have h := @measure_step_constant_integral R nat mu hm 1%R.
by rewrite ht mul1e in h.
Qed.

(** Source for [opposite_infinite_step_sums_regression]: the
    defined-addition hypothesis of Federer 2.4.1, pp. 80–81,
    excludes opposite infinite assigned sums, even though each
    constant function separately satisfies the step definition. *)
Example opposite_infinite_step_sums_regression (R : realType) :
  let mu := @counting_measure R nat in
  let u := partial_function_total (fun _ : nat => (1%R : real_line_metric R)) in
  let v := partial_function_total (fun _ : nat => ((-1)%R : real_line_metric R)) in
  is_measure_step_function mu u /\ is_measure_step_function mu v /\
  is_measure_step_integral mu u +oo /\ is_measure_step_integral mu v -oo /\
  extended_add (+oo : \bar R) (-oo) = None.
Proof.
move=> mu u v; have hm := counting_measure_is_measure R nat.
have ht : mu setT = +oo := @counting_measure_infinite R nat setT infinite_nat.
split; first exact: measure_step_constant.
split; first exact: measure_step_constant.
split.
- have h := @measure_step_constant_integral R nat mu hm 1%R.
  by rewrite ht mul1e in h.
- split; last by [].
  have h := @measure_step_constant_integral R nat mu hm (-1)%R.
  by rewrite ht mulN1e in h.
Qed.

(** Source for [null_source_constant_step_regression]: a constant
    has assigned value zero on a null source, including an empty
    source, under the definition in Federer 2.4.1, p. 80. *)
Example null_source_constant_step_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (c : R) :
  mu setT = 0 -> is_measure_step_function mu
    (partial_function_total (fun _ : X => (c : real_line_metric R))) /\
  is_measure_step_integral mu (partial_function_total (fun _ : X => (c : real_line_metric R))) 0.
Proof.
move=> hz; split; first exact: measure_step_constant.
have h := @measure_step_constant_integral R X mu hm c; by rewrite hz mule0 in h.
Qed.

(** Empty-approximant regressions for Federer (1969), 2.4.2, p. 81. Source
    context: MeasureIntegralUP.v. The source has counting mass one, so an
    everywhere false inequality is not an almost-everywhere assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureAlmostUP CountingMeasure FiniteCountingFunctionExamples MeasureIntegralUP
  MeasureIntegralBounds MeasureIntegralEmptyBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_infinity_no_upper_step_regression]:
    the no-upper-function case in Federer 2.4.2, p. 81,
    actually occurs for the constant positive infinity on a source
    of positive measure; step approximants remain real-valued. *)
Example positive_infinity_no_upper_step_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_function_total (fun _ : unit => (+oo : extended_real_line R)) in
  (~ exists u, is_measure_upper_function mu f u) /\ measure_upper_integral mu f = +oo.
Proof.
move=> mu f.
have hn : ~ exists u, is_measure_upper_function mu f u.
  move=> [u [_ hu]].
  have he : partial_step_upper_locus u f = set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [y [z [hy [hz hb]]]].
    have hb' : (+oo : \bar R) <= y%:E by rewrite hz.
    by move: hb'; rewrite leNgt ltry.
  move: hu; rewrite /measure_almost_everywhere he setC0 /mu counting_unit_whole_value.
  by move=> /eqP; rewrite onee_eq0.
split=> //; exact: measure_upper_integral_no_upper_function.
Qed.

(** Source for [negative_infinity_no_lower_step_regression]:
    dual no-lower-function boundary in Federer 2.4.2, p. 81,
    for the constant negative infinity on a source of mass one. *)
Example negative_infinity_no_lower_step_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_function_total (fun _ : unit => (-oo : extended_real_line R)) in
  (~ exists u, is_measure_lower_function mu f u) /\ measure_lower_integral mu f = -oo.
Proof.
move=> mu f.
have hn : ~ exists u, is_measure_lower_function mu f u.
  move=> [u [_ hu]].
  have he : partial_step_lower_locus u f = set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [y [z [hy [hz hb]]]].
    have hb' : y%:E <= (-oo : \bar R) by rewrite hz.
    by move: hb'; rewrite leNgt ltNyr.
  move: hu; rewrite /measure_almost_everywhere he setC0 /mu counting_unit_whole_value.
  by move=> /eqP; rewrite onee_eq0.
split=> //; exact: measure_lower_integral_no_lower_function.
Qed.

(** Boundary regressions for Federer (1969), 2.4.3, pp. 81–82. Source
    context: PartialExtendedOrderLoci.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPostcomposition PartialExtendedArithmetic MeasureUP CountingMeasure
  MeasureStepFunctionUP MeasureStepConstants MeasureStepPositivePart ExtendedRealPartial MeasureBasic NumericalSum NonnegativeSum
  MeasureIntegralBounds MeasureIntegralEmptyBounds MeasureIntegralBoundsOrder.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [negative_infinite_step_positive_part_regression]:
    Federer 2.4.3(4), p. 82, permits a negative-infinite
    assigned sum. The positive part of the constant -1 on an
    infinite counting space has assigned sum zero. *)
Example negative_infinite_step_positive_part_regression (R : realType) :
  let mu := @counting_measure R [the choiceType of (nat : Type)] in
  let u := partial_function_total (fun _ : nat => ((-1)%R : real_line_metric R)) in
  is_measure_step_integral mu u (-oo) /\
  is_measure_step_integral mu (partial_real_function_positive_part u) 0.
Proof.
move=> mu u; split.
- have ha := @measure_step_constant_integral R [the choiceType of (nat : Type)] mu
    (@counting_measure_is_measure R [the choiceType of (nat : Type)]) (-1)%R.
  have ht : mu setT = +oo := @counting_measure_infinite R [the choiceType of (nat : Type)] setT infinite_nat.
  by move: ha; rewrite ht mulN1e.
- have hz y : y%:E * mu (partial_function_preimage (partial_real_function_positive_part u) [set y]) = 0.
    case: (eqVneq y 0%R)=> [->|hy]; first exact: mul0e.
    have he : partial_function_preimage (partial_real_function_positive_part u) [set y] = set0.
      apply/seteqP; split=> x; last by case.
      move=> [z [[w [hw hwz]] hzy]].
      have he : (0%R : R) = y.
        by move: hwz; rewrite -hw max_r ?lerN10 // hzy.
      by move: hy; rewrite -he eqxx.
    by rewrite he /mu (measure_empty (counting_measure_is_measure R _)) mule0.
  have hp y : (@setT R) y -> 0 <= y%:E * mu (partial_function_preimage (partial_real_function_positive_part u) [set y]).
    by move=> _; rewrite hz.
  by rewrite /is_measure_step_integral (numerical_sum_nonnegative hp)
    (nonnegative_sum_zero (fun y (_ : (@setT R) y) => hz y)).

Qed.

(** Source for [undefined_self_difference_regression]: the
    subtraction used in Federer 2.4.3(7), p. 82, must
    keep its partial domain; positive infinity minus itself is
    nowhere defined on a singleton source. *)
Example undefined_self_difference_regression (R : realType) :
  let f := partial_function_total (fun _ : unit => (+oo : extended_real_line R)) in
  partial_function_domain (partial_extended_function_subtract f f) = set0.
Proof.
move=> f; apply/seteqP; split=> x; last by case.
move=> [z hz].
have [a [b [ha [[c [hc he]] hab]]]] :=
  (@partial_extended_function_add_graph R unit f
    (partial_function_postcompose f (fun y => (-y : extended_real_line R))) x z).1 hz.
rewrite -hc in he; rewrite -ha -he in hab.
by rewrite extended_add_opposite_infinities in hab.
Qed.

(** Boundary regressions for Federer (1969), 2.4.4, pp. 82–83. Source
    context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP
  PartialFunctionBasic PartialFunctionPostcomposition PartialExtendedArithmetic MeasureUP MeasureBasic MeasureAlmostUP
  MeasurableFunctionUP MeasurableTotalBasic CountingMeasure FiniteCountingFunctionExamples NonnegativeSum
  MeasureStepFunctionUP MeasureStepConstants MeasureStepIntegralIdentification MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralSqueeze MeasureNonnegativeIntegral MeasureInfiniteLevelLowerBound PartialExtendedOrderLoci
  MeasureIntegralAddition MeasureIntegralScaleLaw MeasureUpperIntegralScale PartialAbsolutePartsGraph MeasureIntegralAbsolute.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_infinite_function_integrable_regression]:
    the first case of Federer 2.4.4(2), proof p. 83,
    gives integral infinity for a function equal to infinity
    on a set of positive measure. *)
Example positive_infinite_function_integrable_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_function_total (fun _ : unit => (+oo : extended_real_line R)) in
  is_measure_integral mu f +oo.
Proof.
move=> mu f; have hm := counting_measure_is_measure R unit.
have hf : is_measure_measurable_function mu f := @measurable_total_constant R unit (extended_real_line R) mu hm +oo.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus f).
  have he : partial_extended_nonnegative_locus f = setT.
    apply/seteqP; split=> // x _; exists +oo; split=> //; exact: leey.
  by rewrite /measure_almost_everywhere he setCT /mu (measure_empty hm).
have he : partial_function_preimage f [set y | y == +oo] = setT.
  apply/seteqP; split=> // x _; exists +oo; by split.
have hA : 0 < mu (partial_function_preimage f [set y | y == +oo]).
  by rewrite he /mu counting_unit_whole_value lte_fin ltr01.
have hL := @positive_infinite_level_lower_integral R unit mu hm f hf hp hA.
have hi := (@nonnegative_measurable_function_integral R unit mu hm f hf hp).1.
by rewrite hL in hi.
Qed.

(** Source for [finite_values_infinite_integral_addition_regression]:
    the second case of Federer 2.4.4(2), p. 83,
    may still give an infinite integral. The addition law (4)
    permits adding two such positive-infinite integral values. *)
Example finite_values_infinite_integral_addition_regression (R : realType) :
  let mu := @counting_measure R [the choiceType of (nat : Type)] in
  let u := partial_function_total (fun _ : nat => (1%R : real_line_metric R)) in
  let f := partial_real_function_embed u in
  is_measure_integral mu f +oo /\ is_measure_integral mu (partial_extended_function_add f f) +oo.
Proof.
move=> mu u f; have hm := counting_measure_is_measure R [the choiceType of (nat : Type)].
have hu := @measure_step_constant R [the choiceType of (nat : Type)] mu hm 1%R.
have ha := @measure_step_constant_integral R [the choiceType of (nat : Type)] mu hm 1%R.
have ht : mu setT=+oo := @counting_measure_infinite R [the choiceType of (nat : Type)] setT infinite_nat.
rewrite ht mul1e in ha.
have hi := @measure_step_function_integral R [the choiceType of (nat : Type)] mu hm u +oo hu ha.
split=> //; apply: (@measure_integral_add R [the choiceType of (nat : Type)] mu hm f f +oo +oo +oo hi hi).
by [].
Qed.

(** Source for [negative_scale_infinite_integral_regression]:
    Federer 2.4.4(3), p. 82, allows an infinite
    original integral and a negative nonzero scalar. *)
Example negative_scale_infinite_integral_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_function_total (fun _ : unit => (+oo : extended_real_line R)) in
  is_measure_integral mu (partial_extended_function_scale (-1)%R f) (-oo).
Proof.
move=> mu f; have hc : (-1 : R)%R != 0%R by rewrite oppr_eq0 oner_eq0.
have hi := @measure_integral_nonzero_scale R unit mu (counting_measure_is_measure R unit) (-1)%R f +oo hc
  (@positive_infinite_function_integrable_regression R).
by rewrite mulN1e in hi.
Qed.

(** Source for [null_measure_empty_function_absolute_summable_regression]:
    Federer 2.4.4(8), p. 82, includes null measures
    and empty partial domains. Absolute-value summability must
    preserve this boundary rather than impose total domains. *)
Example null_measure_empty_function_absolute_summable_regression (R : realType) :
  let mu := fun _ : set unit => (0 : \bar R) in
  let f := @partial_function_empty unit (extended_real_line R) in
  is_measure_summable mu f /\ is_measure_summable mu (partial_extended_function_absolute_value f).
Proof.
move=> mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf : is_measure_measurable_function mu f.
  constructor; first by [].
  by move=> U hU T; rewrite /mu add0e.
pose u := partial_function_total (fun _ : unit => (0%R : real_line_metric R)).
have hu := @measure_step_constant R unit mu hm 0%R.
have ha := @measure_step_constant_integral R unit mu hm 0%R; rewrite mul0e in ha.
have hup : is_measure_upper_function mu f u by split.
have hlo : is_measure_lower_function mu f u by split.
have hi := @measure_integral_squeeze R unit mu hm f 0 hf
  (@measure_upper_integral_bound R unit mu f u 0 hup ha)
  (@measure_lower_integral_bound R unit mu f u 0 hlo ha).
have hs : is_measure_summable mu f by exists 0%R.
split=> //; exact (@measure_summable_absolute_value R unit mu hm f hs).
Qed.

(** Boundary regressions for Federer (1969), 2.4.5, pp. 83–84. Source
    context: MeasureCharacteristicUpperBound.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureSplit CountingMeasure
  CharacteristicFunctionSealed PartialFunctionBasic MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_characteristic_integral_regression]: the
    first formula in Federer 2.4.5, p. 83, gives zero
    on the empty set without requiring a finite measure of X. *)
Example empty_characteristic_integral_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_measure_integral mu
    (partial_real_function_embed (partial_function_total (@CharacteristicFunction.value R X set0))) 0.
Proof.
rewrite -(measure_empty hm).
exact (@measure_characteristic_integral R X mu hm set0 _
  (@CharacteristicFunction.laws R X set0) (measure_measurable_empty hm)).
Qed.

(** Source for [infinite_characteristic_integral_regression]: the
    first formula in Federer 2.4.5, p. 83, retains
    infinite values, here for all natural numbers with counting measure. *)
Example infinite_characteristic_integral_regression (R : realType) :
  is_measure_integral (@counting_measure R [the choiceType of (nat : Type)])
    (partial_real_function_embed (partial_function_total (@CharacteristicFunction.value R nat setT))) +oo.
Proof.
rewrite -(@counting_measure_infinite R [the choiceType of (nat : Type)] setT infinite_nat).
exact (@measure_characteristic_integral R [the choiceType of (nat : Type)]
  (@counting_measure R [the choiceType of (nat : Type)])
  (counting_measure_is_measure R [the choiceType of (nat : Type)]) setT _
  (@CharacteristicFunction.laws R nat setT) (@counting_measure_measurable R [the choiceType of (nat : Type)] setT)).
Qed.

(** A strict-inequality regression for Federer (1969), 2.4.6, p. 84: unit
    masses escape along the natural numbers. This example is not asserted to
    occur in the source; it tests the direction and non-equality of Fatou's
    bound. Source context: MeasureFatou.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionLimitExtremaUP MeasureUP CountingMeasure FiniteCountingFunctionExamples
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureCharacteristicIntegral MeasureCharacteristicUpperBound ExtendedLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fatou_escaping_unit_masses_regression]: regression
    for Federer 2.4.6, p. 84. The lower-limit function
    has integral zero, strictly below the lower limit of the
    integrals, which are all one. *)
Example fatou_escaping_unit_masses_regression (R : realType) :
  let mu := @counting_measure R [the choiceType of (nat : Type)] in
  let s n := @CharacteristicFunction.value R nat [set n] in
  let f n := partial_real_function_embed (partial_function_total (s n)) in
  let g := partial_real_function_embed (partial_function_total (fun _ : nat => (0%R : real_line_metric R))) in
  is_partial_function_lower_limit f g /\
  is_measure_integral mu g 0 /\
  (forall n, is_measure_integral mu (f n) 1) /\
  (0 : \bar R) < extended_lower_limit (fun _ : nat => 1).
Proof.
move=> mu s f g; have hm := counting_measure_is_measure R [the choiceType of (nat : Type)].
have hs n : is_characteristic_function [set n] (s n) := @CharacteristicFunction.laws R nat [set n].
have hzero x n : (x < n)%N -> s n x = 0%R.
  move=> hxn; apply: (@characteristic_off_set R nat [set n] (s n) (hs n) x).
  move=> he; by move: hxn; rewrite he ltnn.
have hg x : partial_function_graph g x 0 by exists 0%R; split.
split.
- constructor.
  + apply/seteqP; split=> x _.
    * exists 0%N=> n _; exists (s n x)%:E; exists (s n x); by split.
    * exists 0; exact: hg.
  + move=> x y hy b [N hN].
    have ey : y=0 := esym (partial_function_single_valued (hg x) hy).
    rewrite ey; pose k := maxn N x.+1.
    have hxk : (x < k)%N := leq_trans (ltnSn x) (leq_maxr N x.+1).
    have hk : partial_function_graph (f k) x 0.
      exists 0%R; split=> //; exact: hzero hxk.
    exact: hN k (leq_maxl N x.+1) 0 hk.
  + move=> x y hy b hb.
    have ey : y=0 := esym (partial_function_single_valued (hg x) hy).
    rewrite ey; apply: hb; exists 0%N=> n _ z [r [hr erz]].
    rewrite -erz lee_fin -(hr : s n x = r).
    exact: (andP (characteristic_function_scalar_bounds (hs n) x)).1.
- split.
  + have ha := @measure_step_constant_integral R [the choiceType of (nat : Type)] mu hm 0%R.
    rewrite mul0e in ha.
    exact (@measure_step_function_integral R [the choiceType of (nat : Type)] mu hm _ 0
      (@measure_step_constant R [the choiceType of (nat : Type)] mu hm 0%R) ha).
  + split.
    * move=> n; have hi := @measure_characteristic_integral R [the choiceType of (nat : Type)]
        mu hm [set n] (s n) (hs n) (@counting_measure_measurable R [the choiceType of (nat : Type)] [set n]).
      by rewrite /mu counting_singleton_value in hi.
    * by rewrite extended_lower_limit_constant lte_fin ltr01.
Qed.

(** Hypothesis regression for Federer (1969), 2.4.7, p. 84. Negative
    characteristic functions of shrinking infinite tails of the natural
    numbers give a solution. Source context: MeasureIncreasingConvergence.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealOrderLimit
  PartialFunctionUP PartialFunctionBasic MeasureUP CountingMeasure
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralNegation MeasureIntegralNegationLaw
  MeasureCharacteristicIntegral MeasureCharacteristicUpperBound PartialIncreasingLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [increasing_convergence_requires_nonnegative_regression]:
    counterexample to omitting the nonnegativity hypothesis of Federer
    2.4.7, p. 84, solving the exercise. All functions increase pointwise to
    zero, but all integrals are minus infinity. *)
Example increasing_convergence_requires_nonnegative_regression (R : realType) :
  let mu := @counting_measure R [the choiceType of (nat : Type)] in
  let A n := [set k : nat | (n <= k)%N] in
  let s n := @CharacteristicFunction.value R nat (A n) in
  let f n := partial_extended_function_negate (partial_real_function_embed (partial_function_total (s n))) in
  let g := partial_real_function_embed (partial_function_total (fun _ : nat => (0%R : real_line_metric R))) in
  (forall x, partial_extended_increasing_limit_locus f g x) /\
  (forall n, is_measure_integral mu (f n) (-oo)) /\
  is_measure_integral mu g 0 /\
  ~ extended_order_limit (fun _ : nat => (-oo : \bar R)) 0.
Proof.
move=> mu A s f g; have hm := counting_measure_is_measure R [the choiceType of (nat : Type)].
have hs n : is_characteristic_function (A n) (s n) := @CharacteristicFunction.laws R nat (A n).
have hzero x n : (x < n)%N -> s n x = 0%R.
  move=> hxn; apply: (@characteristic_off_set R nat (A n) (s n) (hs n) x).
  move=> hn; by move: hn; rewrite /A /= leqNgt hxn.
split.
- move=> x; pose u n := -(s n x)%:E.
  have hu0 n : (x < n)%N -> u n = 0 by move=> hn; rewrite /u (hzero x n hn) oppe0.
  exists u,0; split.
  + move=> n; exists (s n x)%:E; split=> //; exists (s n x); by split.
  + split; first by exists 0%R; split.
    split.
    * move=> n m hnm; rewrite /u leeN2 lee_fin.
      have [hmx|hmx] := leqP m x.
      -- have hnx : A n x := leq_trans hnm hmx.
         by rewrite (characteristic_on_set (hs m) hmx) (characteristic_on_set (hs n) hnx).
      -- rewrite (hzero x m hmx); exact: (andP (characteristic_function_scalar_bounds (hs n) x)).1.
    * split.
      -- move=> a ha; exists x.+1=> n hn; by rewrite (hu0 n hn).
      -- move=> b hb; exists x.+1=> n hn; by rewrite (hu0 n hn).
- split.
  + move=> n; have hA : mu (A n) = +oo.
      apply: counting_measure_infinite.
      have he : A n = setT `\` [set k : nat | (k < n)%N].
        apply/seteqP; split=> k.
        * move=> hk; split=> // hkn; by move: hk; rewrite /A /= leqNgt hkn.
        * move=> [_ hk]; rewrite /A /= leqNgt; apply/negP; exact: hk.
      rewrite he; apply: infinite_setD infinite_nat _; exact: finite_II.
    have hi := @measure_characteristic_integral R [the choiceType of (nat : Type)] mu hm (A n)
      (s n) (hs n) (@counting_measure_measurable R [the choiceType of (nat : Type)] (A n)).
    rewrite hA in hi; exact (@measure_integral_negation R [the choiceType of (nat : Type)] mu hm _ +oo hi).
  + split.
    * have ha := @measure_step_constant_integral R [the choiceType of (nat : Type)] mu hm 0%R.
      rewrite mul0e in ha.
      exact (@measure_step_function_integral R [the choiceType of (nat : Type)] mu hm _ 0
        (@measure_step_constant R [the choiceType of (nat : Type)] mu hm 0%R) ha).
    * move=> [hl _]; have [N hN] := hl (-oo) (ltNyr 0%R).
      have h := hN N (leqnn N); by move: h; rewrite ltxx.
Qed.

(** Empty and infinite-sum regressions for Federer (1969), 2.4.8, p. 84.
    Source context: MeasureCountableNonnegativeSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP CountingMeasure FiniteCountingFunctionExamples MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralUP NonnegativeSum NonnegativeSumConstant NumericalSum
  PartialNumericalSumUP PartialNumericalSum MeasureCountableNonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_family_sum_integral_regression]: the empty
    family in Federer 2.4.8, p. 84, has integral
    zero without a finite-total-measure or inhabited-index premise. *)
Example empty_family_sum_integral_regression (R : realType) (X J : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : J -> partial_function X (extended_real_line R)) :
  is_measure_integral mu (partial_function_numerical_sum set0 f) 0.
Proof.
have h := @measure_countable_nonnegative_integral_values R X J mu hm set0 f
  (partial_function_numerical_sum set0 f) (fun _ => 0)
  (countable0 J) (partial_function_numerical_sum_laws set0 f)
  (fun j hj => False_rect _ hj) (fun j hj => False_rect _ hj).
by rewrite nonnegative_sum_empty in h.
Qed.

(** Source for [infinite_family_sum_integral_regression]: an
    infinite sum of nonnegative functions in Federer 2.4.8,
    p. 84, may equal infinity everywhere and have infinite
    integral. Here every summand is one on a unit mass. *)
Example infinite_family_sum_integral_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_real_function_embed (partial_function_total (fun _ : unit => (1%R : real_line_metric R))) in
  let g := @partial_function_numerical_sum R unit [the choiceType of (nat : Type)] setT (fun _ => f) in
  (forall x, partial_function_graph g x +oo) /\ is_measure_integral mu g +oo.
Proof.
move=> mu f g; have hm := counting_measure_is_measure R unit.
have hsum : @nonnegative_sum R [the choiceType of (nat : Type)] setT (fun _ => 1) = +oo.
  exact (@nonnegative_sum_infinite_constant R [the choiceType of (nat : Type)] setT 1%R ltr01 infinite_nat).
have hf : is_measure_integral mu f 1.
  have ha := @measure_step_constant_integral R unit mu hm 1%R.
  rewrite /mu counting_unit_whole_value mul1e in ha.
  exact (@measure_step_function_integral R unit mu hm _ 1 (@measure_step_constant R unit mu hm 1%R) ha).
have hp : forall x y, partial_function_graph f x y -> 0 <= y.
  move=> x y [r [hr ery]]; by rewrite -ery -(hr : 1%R=r) lee_fin ler01.
split.
- move=> x; apply: (partial_function_numerical_sum_graph setT (fun _ : nat => f) x +oo).2.
  exists (fun _ : nat => (1 : \bar R)); split.
  + move=> n _; exists 1%R; by split.
  + have hn n : (@setT nat) n -> (0 : \bar R) <= 1 by move=> _; rewrite lee_fin ler01.
    by rewrite (numerical_sum_nonnegative hn) hsum.
- rewrite -hsum; apply: (@measure_countable_nonnegative_integral_values R unit [the choiceType of (nat : Type)]
    mu hm setT (fun _ => f) g (fun _ => 1) (countableP _)
    (partial_function_numerical_sum_laws setT (fun _ => f))).
  + by move=> n _; exact hp.
  + by move=> n _; exact hf.
Qed.

(** Boundary regressions for Federer (1969), 2.4.9, p. 85. Source context:
    MeasureBoundedConvergence.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasurableFunctionUP MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralSqueeze MeasureBoundedConvergence PartialDominatedConvergence
  DominatedErrorGraphs NonnegativeSum CountingMeasure FiniteCountingFunctionExamples MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_measure_empty_bounded_convergence_regression]:
    Federer 2.4.9, p. 85, retains the almost-everywhere
    convention of 2.3.1: for a null measure even empty
    partial domains satisfy the convergence conclusion. *)
Example null_measure_empty_bounded_convergence_regression (R : realType) :
  let mu := fun _ : set unit => (0 : \bar R) in
  let f := @partial_function_empty unit (extended_real_line R) in
  exists (a e : nat -> R) (b : R),
    (forall n, is_measure_integral mu f (a n)%:E) /\
    is_measure_integral mu f b%:E /\
    (forall n, is_measure_integral mu (partial_absolute_difference f f) (e n)%:E) /\
    extended_order_limit (fun n => (e n)%:E) 0 /\
    extended_order_limit (fun n => (a n)%:E) b%:E.
Proof.
move=> mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf : is_measure_measurable_function mu f.
  constructor; first by [].
  by move=> U hU T; rewrite /mu add0e.
pose u := partial_function_total (fun _ : unit => (0%R : real_line_metric R)).
have hu := @measure_step_constant R unit mu hm 0%R.
have ha := @measure_step_constant_integral R unit mu hm 0%R; rewrite mul0e in ha.
have hup : is_measure_upper_function mu f u by split.
have hlo : is_measure_lower_function mu f u by split.
have hi := @measure_integral_squeeze R unit mu hm f 0 hf
  (@measure_upper_integral_bound R unit mu f u 0 hup ha)
  (@measure_lower_integral_bound R unit mu f u 0 hlo ha).
have hs : is_measure_summable mu f by exists 0%R.
apply: (@measure_bounded_convergence R unit mu hm (fun _ => f) f f hs (fun _ => hf) hf).
- by move=> n.
- by [].
Qed.

(** Source for [negative_constant_bounded_convergence_regression]:
    Federer 2.4.9, p. 85, applies to signed functions;
    a constant negative sequence on a unit mass is dominated
    by its absolute value and its error integral tends to zero. *)
Example negative_constant_bounded_convergence_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_real_function_embed (partial_function_total (fun _ : unit => ((-1)%R : real_line_metric R))) in
  let h := partial_real_function_embed (partial_function_total (fun _ : unit => (1%R : real_line_metric R))) in
  exists (a e : nat -> R) (b : R),
    (forall n, is_measure_integral mu f (a n)%:E) /\
    is_measure_integral mu f b%:E /\
    (forall n, is_measure_integral mu (partial_absolute_difference f f) (e n)%:E) /\
    extended_order_limit (fun n => (e n)%:E) 0 /\
    extended_order_limit (fun n => (a n)%:E) b%:E.
Proof.
move=> mu f h; have hm := counting_measure_is_measure R unit.
have hi (c : R) : is_measure_integral mu
    (partial_real_function_embed (partial_function_total (fun _ : unit => (c : real_line_metric R)))) c%:E.
  have hs := @measure_step_constant R unit mu hm c.
  have hv := @measure_step_constant_integral R unit mu hm c.
  rewrite /mu counting_unit_whole_value mule1 in hv.
  exact (@measure_step_function_integral R unit mu hm _ c%:E hs hv).
have hfi := hi (-1)%R; have hhi := hi 1%R.
have hs : is_measure_summable mu h by exists 1%R.
apply: (@measure_bounded_convergence R unit mu hm (fun _ => f) f h hs (fun _ => hfi.1) hfi.1).
- move=> n; apply: (@measure_almost_everywhere_mono R unit mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists 1,1; split.
  + exists (-1); split; last by rewrite abseN abse1.
    exists (-1)%R; by split.
  + split; first by exists 1%R; split.
    exact: lexx.
- apply: (@measure_almost_everywhere_mono R unit mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists (fun _ : nat => (-1 : \bar R)),(-1); split.
  + move=> n; exists (-1)%R; by split.
  + split; first by exists (-1)%R; split.
    split; [move=> a ha|move=> b hb]; exists 0%N=> n _; assumption.
Qed.

(** Boundary regressions for Federer (1969), 2.4.10, p. 85. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  PartialZeroExtensionLaws MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasurableTotalBasic
  PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureDensity MeasureDensityNullSets
  MeasureChangeOfDensity PartialDensityProduct CountingMeasure MeasureSubsetIntegral MeasureIntervalIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinite_density_zero_integrand_regression]: zero times
    infinity must equal zero in the product of Federer 2.4.10, p. 85,
    explicitly required. On a unit mass with density infinity, the zero
    integrand still has integral zero under both sides of the density
    formula. *)
Example infinite_density_zero_integrand_regression (R : realType) :
  let mu := @counting_measure R unit in
  let h := partial_function_total (fun _ : unit => (+oo : extended_real_line R)) in
  let f := partial_function_total (fun _ : unit => (0 : extended_real_line R)) in
  let nu := measure_with_density mu h in
  is_measure_integral nu f 0 /\ is_measure_integral mu (partial_density_product f h) 0 /\
    (forall x, partial_function_graph (partial_density_product f h) x 0).
Proof.
move=> mu h f nu; have hm := counting_measure_is_measure R unit.
have hh := @measurable_total_constant R unit (extended_real_line R) mu hm +oo.
have hf := @measurable_total_constant R unit (extended_real_line R) mu hm 0.
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus h).
  apply: (@measure_almost_everywhere_mono R unit mu hm setT _ _ (measure_almost_everywhere_true hm)).
  move=> x _; exists +oo; split=> //; exact: leey.
have hnu := @measure_with_density_is_measure R unit mu hm h hp.
have hi := @measure_extended_zero_integral R unit nu hnu.
split=> //; split.
- exact: (@measure_density_integral_iff R unit mu nu hm h f (measure_with_density_laws mu h) hh hp hf 0).1 hi.
- move=> x; apply/partial_density_product_graph; exists 0,+oo; split=> //; split=> //; exact: mul0e.
Qed.

(** Source for [coincident_interval_integral_regression]:
    the half-open interval with coincident endpoints in
    Federer 2.4.10, p. 85, is empty. Its
    integral is zero even for a function with no values. *)
Example coincident_interval_integral_regression (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (coordinate : X -> \bar R)
    (a : \bar R) (f : partial_function X (extended_real_line R)) :
  is_measure_interval_integral mu coordinate a a f 0.
Proof.
have he : measure_half_open_interval coordinate a a = set0.
  apply/seteqP; split=> x; last by move=> [].
  move=> /andP[ha hb]; have hh := lt_le_trans ha hb; by move: hh; rewrite ltxx.
rewrite /is_measure_interval_integral /is_measure_subset_integral he.
apply: (@measure_integral_graph_equivalent R X mu _ _ 0 _ (measure_extended_zero_integral hm))=> x y.
rewrite partial_zero_extension_empty_graph; split; by move=> ->.
Qed.

(** Boundary regressions for Federer (1969), 2.4.11, pp. 85–86. Source
    context: PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialAbsolutePartsGraph MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasureStepConstants
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralSqueeze MeasureSubsetIntegral
  MeasureIntegralAbsoluteContinuity CharacteristicFunctionSealed MeasureStepIntegralIdentification
  MeasureCharacteristicIntegral CountingMeasure FiniteCountingFunctionExamples NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_empty_absolute_continuity_regression]:
    Federer 2.4.11, pp. 85–86, includes functions
    defined only almost everywhere: for a null measure the
    empty function satisfies the strict estimate at every
    positive tolerance. *)
Example null_empty_absolute_continuity_regression (R : realType) (epsilon : R) :
  (0 < epsilon)%R ->
  let mu := fun _ : set unit => (0 : \bar R) in
  let f := @partial_function_empty unit (extended_real_line R) in
  exists delta : R, (0 < delta)%R /\ forall A : set unit,
    measure_measurable mu A -> mu A <= delta%:E ->
    exists a : R, is_measure_subset_integral mu A
      (partial_extended_function_absolute_value f) a%:E /\ (a < epsilon)%R.
Proof.
move=> he mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf : is_measure_measurable_function mu f.
  constructor; first by [].
  by move=> U hU T; rewrite /mu add0e.
pose u := partial_function_total (fun _ : unit => (0%R : real_line_metric R)).
have hu := @measure_step_constant R unit mu hm 0%R.
have ha := @measure_step_constant_integral R unit mu hm 0%R; rewrite mul0e in ha.
have hup : is_measure_upper_function mu f u by split.
have hlo : is_measure_lower_function mu f u by split.
have hi := @measure_integral_squeeze R unit mu hm f 0 hf
  (@measure_upper_integral_bound R unit mu f u 0 hup ha)
  (@measure_lower_integral_bound R unit mu f u 0 hlo ha).
have hs : is_measure_summable mu f by exists 0%R.
exact (@measure_integral_absolute_continuity R unit mu hm f epsilon hs he).
Qed.

(** Source for [infinite_ambient_absolute_continuity_regression]:
    Federer 2.4.11, pp. 85–86, assumes summability
    of f rather than finite measure of the ambient space.
    Apply the strict estimate to a singleton characteristic
    function under counting measure on the natural numbers. *)
Example infinite_ambient_absolute_continuity_regression (R : realType) (epsilon : R) :
  (0 < epsilon)%R ->
  let mu := @counting_measure R [the choiceType of (nat : Type)] in
  let f := partial_real_function_embed
    (partial_function_total (@CharacteristicFunction.value R nat [set 0%N])) in
  exists delta : R, (0 < delta)%R /\ forall A : set nat,
    measure_measurable mu A -> mu A <= delta%:E ->
    exists a : R, is_measure_subset_integral mu A
      (partial_extended_function_absolute_value f) a%:E /\ (a < epsilon)%R.
Proof.
move=> he mu f; have hm := counting_measure_is_measure R [the choiceType of (nat : Type)].
have hi := @measure_characteristic_integral R [the choiceType of (nat : Type)] mu hm
  [set 0%N] _ (@CharacteristicFunction.laws R nat [set 0%N])
  (@counting_measure_measurable R [the choiceType of (nat : Type)] [set 0%N]).
rewrite /mu counting_singleton_value in hi.
have hs : is_measure_summable mu f by exists 1%R.
exact (@measure_integral_absolute_continuity R [the choiceType of (nat : Type)] mu hm f epsilon hs he).
Qed.

(** Boundary checks for Federer (1969), 2.4.13, p. 88, with the
    nonnegative-base extension. Source context:
    WeightedArithmeticGeometricMean.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealPower WeightedArithmeticGeometricMean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [weighted_means_zero_regression]: Supporting Federer 2.4.13,
    p. 88. *)
Example weighted_means_zero_regression (R : realType) (a b : R) :
  0 < a -> 0 < b -> a+b = 1 ->
  real_power 0 a * real_power 0 b = a*0+b*0.
Proof.
move=> ha hb hab.
exact: (proj2 (weighted_arithmetic_geometric_mean_equality ha hb hab (lexx 0) (lexx 0))) erefl.
Qed.

(** Source for [weighted_means_one_zero_strict_regression]: one zero and one
    positive base cannot give equality; this checks the boundary extension
    of Federer 2.4.13, p. 88. *)
Example weighted_means_one_zero_strict_regression (R : realType) (a b : R) :
  0 < a -> 0 < b -> a+b = 1 ->
  real_power 0 a * real_power 1 b < a*0+b*1.
Proof.
move=> ha hb _; rewrite real_power_zero_base ?gt_eqF // mul0r mulr0 mulr1 add0r.
exact hb.
Qed.

(** Source for [weighted_means_equal_unit_regression]: equal
    positive bases give equality in Federer 2.4.13, p. 88. *)
Example weighted_means_equal_unit_regression (R : realType) (a b : R) :
  0 < a -> 0 < b -> a+b = 1 ->
  real_power 1 a * real_power 1 b = 1.
Proof. by move=> _ _ _; rewrite !real_power_one_base mul1r. Qed.

(** Regressions for the currently formalised parts of Federer (1969),
    2.4.12, pp. 86–87. These examples cover the null-measure essential-norm
    convention and the zero finite-p norm even when the ambient measure is
    infinite. They do not assert completion of the remaining claims in
    2.4.12. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasurableTotalBasic MeasureEssentialNormUP MeasureEssentialNorm
  PartialNormPower RealPower ExtendedPositivePower MeasureLpNorm
  MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureDensityNullSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [essential_norm_null_measure_regression]: boundary
    check of the defining infimum in Federer 2.4.12,
    p. 86. Nonnegative thresholds give zero for every
    partial function under the null measure, including the
    empty function; unrestricted thresholds would fail this. *)
Example essential_norm_null_measure_regression (R : realType) (X : choiceType)
    (Y : Type) (N : Y -> R) (f : partial_function X Y) :
  measure_essential_norm (fun _ : set X => (0 : \bar R)) N f = 0.
Proof.
apply/eqP; rewrite eq_le measure_essential_norm_nonnegative andbT.
apply: measure_essential_norm_bound; by split.
Qed.

(** Source for [lp_norm_zero_total_regression]: zero-function
    case of the finite-p formula of Federer 2.4.12,
    p. 86. The result holds for an arbitrary measure,
    including infinite total mass, and any normed target. *)
Example lp_norm_zero_total_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) :
  (1 <= p)%R -> measure_lp_norm mu N p
    (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN))) = 0.
Proof.
move=> hp; have hp0 : (0 < p)%R := lt_le_trans (ltr01) hp.
pose f := partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN)).
have hf := @measurable_total_constant R X [the topologicalType of real_norm_metric_space hN] mu hm 0%R.
have hi : is_measure_integral mu (partial_norm_power N p f) 0.
  apply: (@measure_integral_graph_equivalent R X mu
    (partial_function_total (fun _ : X => (0 : extended_real_line R))) _ 0 _
    (@measure_extended_zero_integral R X mu hm)).
  move=> x y; split.
  - move=> hy; exists (0%R : real_norm_metric_space hN); split=> //.
    by rewrite (real_seminorm_zero hN.1) real_power_zero_base ?gt_eqF.
  - move=> [z [hz he]].
    have hz' : (0%R : V)=z := hz.
    by rewrite -hz' (real_seminorm_zero hN.1) real_power_zero_base ?gt_eqF in he.
rewrite (@measure_lp_norm_of_integral R X V N hN mu p f 0 hm hp hf hi).
apply: extended_positive_power_zero; by rewrite invr_gt0.
Qed.

(** Regression examples for Federer (1969), 2.4.14, p. 88. The examples
    check empty partial domains under a null measure and negative signed
    equality on a unit counting mass. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialFunctionBasic PartialNormPower PartialScalarProduct RealPower ExtendedPositivePower
  MeasureUP MeasureAlmostUP MeasureAlmostBasic NonnegativeSum MeasureIntegralUP MeasureIntegralUniqueness
  MeasurableFunctionUP MeasurableTotalBasic MeasurableNormedBasic
  MeasureLpNorm MeasureLpZero MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureHolder MeasureHolderScalar MeasureHolderEquality MeasureSignedPowerDependenceUP
  MeasureStepConstants MeasureStepIntegralIdentification MeasureIntegralGraphEquivalence
  CountingMeasure FiniteCountingFunctionExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [holder_null_empty_regression]: zero-norm and
    empty-domain boundary of Federer 2.4.14, p. 88.
    Under the null measure, the empty function has zero
    norm and its empty product attains equality. *)
Example holder_null_empty_regression (R : realType) :
  let mu := fun _ : set unit => (0 : \bar R) in
  let f := @partial_function_empty unit (real_norm_metric_space (scalar_absolute_value_norm R)) in
  is_measure_integral mu (partial_scalar_product f f) 0 /\
    is_almost_signed_power_dependent mu 2%R 2%R f f.
Proof.
move=> mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf : is_measure_measurable_function mu f.
  constructor; first by [].
  by move=> U hU T; rewrite /mu add0e.
have hp : (1 <= (2 : R))%R by rewrite ler1n.
have hpq : ((2 : R)^-1+2^-1 = 1)%R.
  have h := splitr (1%R : R); rewrite !mul1r in h; exact: esym h.
have hn : measure_lp_norm mu (fun x : R => `|x|%R) 2%R f = 0.
  apply: (@lp_norm_zero_iff R unit R^o _ (scalar_absolute_value_norm R) mu hm 2%R f hp hf).2.
  by [].
have [c [hci hc]] := @measure_holder_scalar_finite R unit mu hm 2%R 2%R 0%R 0%R f f hp hp hpq hf hf hn hn.
have hz : c=0%R.
  have habs : (`|c| = 0)%R.
    apply/eqP; rewrite eq_le normr_ge0 andbT; by move: hc; rewrite mul0r.
  by move/eqP: habs; rewrite normr_eq0=> /eqP.
rewrite hz in hci; split=> //.
apply: (@measure_holder_equality_iff R unit mu hm 2%R 2%R 0%R 0%R 0%R f f hp hp hpq hf hf hn hn hci).1.
by rewrite normr0 mul0r.
Qed.

(** Source for [holder_opposite_unit_constants_regression]:
    negative-sign equality in Federer 2.4.14, p. 88.
    The constant functions one and minus one on a unit
    counting mass belong to L2, have norms one, and
    attain equality with signed integral minus one. *)
Example holder_opposite_unit_constants_regression (R : realType) :
  let mu := @counting_measure R unit in
  let f := partial_function_total (fun _ : unit => (1%R : real_norm_metric_space (scalar_absolute_value_norm R))) in
  let g := partial_function_total (fun _ : unit => ((-1)%R : real_norm_metric_space (scalar_absolute_value_norm R))) in
  is_measure_lp_function mu 2%R f /\ is_measure_lp_function mu 2%R g /\
    is_measure_integral mu (partial_scalar_product f g) (-1) /\
    is_almost_signed_power_dependent mu 2%R 2%R f g.
Proof.
move=> mu f g; have hm := counting_measure_is_measure R unit.
have hp : (1 <= (2 : R))%R by rewrite ler1n.
have hpq : ((2 : R)^-1+2^-1 = 1)%R.
  have h := splitr (1%R : R); rewrite !mul1r in h; exact: esym h.
have hconst (v : R) : is_measure_integral mu
    (partial_real_function_embed (partial_function_total (fun _ : unit => (v : real_line_metric R)))) v%:E.
  have hs := @measure_step_constant R unit mu hm v.
  have hv := @measure_step_constant_integral R unit mu hm v.
  rewrite /mu counting_unit_whole_value mule1 in hv.
  exact (@measure_step_function_integral R unit mu hm _ v%:E hs hv).
have hnorm (v : R) (hv : (`|v| = 1)%R) : measure_lp_norm mu (fun x : R => `|x|%R) 2%R
    (partial_function_total (fun _ : unit => (v : real_norm_metric_space (scalar_absolute_value_norm R)))) = 1.
  pose h := partial_function_total (fun _ : unit => (v : real_norm_metric_space (scalar_absolute_value_norm R))).
  have hmeas := @measurable_total_constant R unit [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm v.
  have hi : is_measure_integral mu (partial_norm_power (fun x : R => `|x|%R) 2%R h) 1.
    apply: (@measure_integral_graph_equivalent R unit mu _ _ 1 _ (hconst 1%R))=> x z; split.
    - move=> [a [ha haz]]; exists v; split=> //.
      have ha' : (1%R : R)=a := ha.
      by rewrite hv real_power_one_base -ha' in haz *.
    - move=> [a [ha haz]]; exists 1%R; split=> //.
      have ha' : v=a := ha.
      by rewrite -ha' hv real_power_one_base in haz.
  rewrite (@measure_lp_norm_of_integral R unit R^o _ (scalar_absolute_value_norm R) mu 2%R h 1 hm hp hmeas hi).
  change ((@real_power R 1%R (2%R)^-1)%:E = 1); by rewrite real_power_one_base.
have hfn := hnorm 1%R (@normr1 R).
have hgn := hnorm (-1)%R (@normrN1 R).
have hA v := @measurable_normed_total_constant R unit R^o _ (scalar_absolute_value_norm R) mu hm v.
have hflp : is_measure_lp_function mu 2%R f.
  split=> //; split; first exact (hA 1%R).
  have hfin : measure_lp_norm mu (fun x : R => `|x|%R) 2%R f < +oo by rewrite hfn ltry.
  split=> //; exact (@finite_lp_norm_countably_measurable R unit R^o _ (scalar_absolute_value_norm R) mu hm 2%R f hp (hA 1%R).1 hfin).
have hglp : is_measure_lp_function mu 2%R g.
  split=> //; split; first exact (hA (-1)%R).
  have hfin : measure_lp_norm mu (fun x : R => `|x|%R) 2%R g < +oo by rewrite hgn ltry.
  split=> //; exact (@finite_lp_norm_countably_measurable R unit R^o _ (scalar_absolute_value_norm R) mu hm 2%R g hp (hA (-1)%R).1 hfin).
have hprod : is_measure_integral mu (partial_scalar_product f g) (-1).
  apply: (@measure_integral_graph_equivalent R unit mu _ _ (-1) _ (hconst (-1)%R))=> x z; split.
  - move=> [a [ha haz]]; apply/partial_scalar_product_graph.
    exists 1%R,(-1)%R; split=> //; split=> //.
    have ha' : (-1)%R=a := ha; by rewrite mul1r -ha' in haz *.
  - move=> hz; have [a [b [ha [hb hab]]]] := (partial_scalar_product_graph f g x z).1 hz.
    exists (-1)%R; split=> //.
    have ha' : 1%R=a := ha; have hb' : (-1)%R=b := hb.
    by rewrite -ha' -hb' mul1r in hab.
split=> //; split=> //; split=> //.
apply: (@measure_holder_equality_iff R unit mu hm 2%R 2%R 1%R 1%R (-1)%R f g
  hp hp hpq hflp.2.1.1 hglp.2.1.1 hfn hgn hprod).1.
by rewrite normrN1 mulr1.
Qed.

(** Regression examples for Federer (1969), 2.4.15, p. 89. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP MeasureAlmostUP MeasureAlmostBasic NonnegativeSum
  MeasurableNormedBasic MeasurableFunctionUP MeasureLpNorm MeasureLpZero MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureMinkowski MeasureMinkowskiEquality MeasureMinkowskiInnerEquality MinkowskiEqualityUP
  PositiveProportionalityUP PositiveMultipleNormProportions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_null_empty_regression]: empty partial-domain
    boundary of Federer 2.4.15, p. 89. For the null measure
    on any source and any normed target, the empty function belongs
    to every finite Lp, and adding it to itself attains equality.
    This also covers a zero-dimensional target. *)
Example minkowski_null_empty_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) (p : R) :
  (1 < p)%R ->
  let mu := fun _ : set X => (0 : \bar R) in
  let f := @partial_function_empty X (real_norm_metric_space hN) in
  is_measure_lp_function mu p f /\
    measure_lp_norm mu N p (partial_vector_add f f) = measure_lp_norm mu N p f + measure_lp_norm mu N p f.
Proof.
move=> hp mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hA := @measurable_normed_total_constant R X V N hN mu hm 0%R.
have hfA := @measurable_normed_almost_equal R X V N hN mu hm _ f hA (erefl 0).
have hp1 : (1 <= p)%R := ltW hp.
have hnorm : measure_lp_norm mu N p f = 0.
  apply: (@lp_norm_zero_iff R X V N hN mu hm p f hp1 hfA.1).2; by [].
have hfin : measure_lp_norm mu N p f < +oo by rewrite hnorm ltry.
have hflp : is_measure_lp_function mu p f.
  split=> //; split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm p f hp1 hfA.1 hfin).
split=> //; apply: (proj2 (@minkowski_equality_iff R X V N hN mu hm p f f hp hflp hflp)).
exists 0%R,1%R; split=> //; split=> //; split; first by rewrite add0r.
by [].
Qed.

(** Source for [minkowski_reverse_zero_coefficient_regression]: the
    second orientation and zero coefficient in the bracketed criterion
    of Federer 2.4.15, p. 89. A constant nonzero first
    function and the zero second function are positively proportional
    in the reverse orientation. This condition is independent of finite
    measure and does not assert Lp membership for arbitrary constants. *)
Example minkowski_reverse_zero_coefficient_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (y : V) :
  let f := partial_function_total (fun _ : X => y) in
  let g := partial_function_total (fun _ : X => (0%R : V)) in
  measure_almost_positively_proportional mu f g /\ is_minkowski_equality_condition N mu f g.
Proof.
move=> f g.
have he : measure_almost_positively_proportional mu f g.
  exists 0%R; split=> //; right.
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (@measure_almost_everywhere_true R X mu hm)).
  move=> x _; exists 0%R,y; split=> //; split=> //; by rewrite scale0r.
split=> //; exact (@positive_proportionality_minkowski_condition R X V N hN mu hm f g he).
Qed.

(** Regression examples for the finite-p completion of Federer (1969),
    2.4.12, pp. 86-87. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureAlmostUP NonnegativeSum MeasurableNormedBasic
  MeasureLpNorm MeasureLpZero MeasureLpMembershipUP MeasureLpCountableMeasurability
  MeasureLpConvergence MeasureLpFiniteImageDensity MeasureStepFunctionUP
  FiniteNearestApproximationUP FiniteNearestApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lone_null_empty_finite_density_regression]: p=1,
    null-measure and empty-domain boundary of the finite-image density
    assertion in Federer 2.4.12, p. 87. Any normed target
    is allowed, including zero dimension, and the approximant satisfies
    every L1 membership condition. *)
Example lone_null_empty_finite_density_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) (epsilon : R) :
  (0 < epsilon)%R ->
  let mu := fun _ : set X => (0 : \bar R) in
  let f := @partial_function_empty X (real_norm_metric_space hN) in
  exists g : partial_function X (real_norm_metric_space hN),
    is_measure_lp_function mu 1%R g /\ finite_set (partial_function_range g) /\
    measure_lp_distance mu N 1%R f g < epsilon%:E.
Proof.
move=> he mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hA := @measurable_normed_total_constant R X V N hN mu hm 0%R.
have hfA := @measurable_normed_almost_equal R X V N hN mu hm _ f hA (erefl 0).
have hp : (1 <= (1:R))%R := lexx _.
have hnorm : measure_lp_norm mu N 1%R f = 0.
  apply: (@lp_norm_zero_iff R X V N hN mu hm 1%R f hp hfA.1).2; by [].
have hfin : measure_lp_norm mu N 1%R f < +oo by rewrite hnorm ltry.
have hf : is_measure_lp_function mu 1%R f.
  split=> //; split=> //; split=> //.
  exact (@finite_lp_norm_countably_measurable R X V N hN mu hm 1%R f hp hfA.1 hfin).
exact (@measure_lp_finite_image_dense R X V N hN mu hm 1%R f epsilon hf he).
Qed.

(** Source for [finite_nearest_zero_preserved_regression]: zero-vector
    boundary of the finite approximation used for Federer 2.4.12,
    p. 87. If zero is the first candidate, every approximant
    sends zero to zero, even if labels repeat and closest-point ties occur. *)
Example finite_nearest_zero_preserved_regression (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (y : nat -> real_norm_metric_space hN) (q : nat -> real_norm_metric_space hN -> nat) :
  y 0%N=0%R -> is_finite_nearest_approximation y q -> forall n, y (q n 0%R)=0%R.
Proof.
move=> hy hq n; have hb := @finite_nearest_map_reference_bound R [the metricType R of real_norm_metric_space hN] y q hq n 0%R.
rewrite hy mdistxx in hb.
have he : mdist (0%R : real_norm_metric_space hN) (y (q n 0%R))=0%R.
  apply/eqP; rewrite eq_le; apply/andP; split=> //; exact: mdist_ge0.
symmetry; exact: mdist_positivity he.
Qed.

(** Regression examples for Federer (1969), 2.4.12, p. 87, corrected
    infinity-endpoint density (erratum p. 2, book p. 87 line 18). *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric LinearBasis PartialFunctionUP PartialFunctionBasic
  MeasureUP NonnegativeSum MeasurableNormedBasic MeasureStepFunctionUP
  CountablyMeasurableUP CountablyMeasurableBasic MeasureLinfinityUP
  MeasureEssentialNorm MeasureEssentialNormAttainment MeasureEssentialConvergence
  CompactFiniteApproximationUP CompactFiniteApproximationSealed MeasureLinfinityFiniteImageDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [linfinity_null_empty_finite_density_regression]:
    null-measure and empty-domain boundary of corrected Federer
    2.4.12 density, p. 87. Any finite basis is allowed,
    including an empty basis for a zero-dimensional target. *)
Example linfinity_null_empty_finite_density_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) n (e : 'I_n -> V) (epsilon : R) :
  is_basis e -> (0 < epsilon)%R ->
  let mu := fun _ : set X => (0 : \bar R) in
  let f := @partial_function_empty X (real_norm_metric_space hN) in
  exists g : partial_function X (real_norm_metric_space hN),
    is_measure_linfinity_function mu g /\ finite_set (partial_function_range g) /\
    measure_essential_distance mu N f g < epsilon%:E.
Proof.
move=> he heps mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hA := @measurable_normed_total_constant R X V N hN mu hm 0%R.
have hfA := @measurable_normed_almost_equal R X V N hN mu hm _ f hA (erefl 0).
have hf : is_measure_linfinity_function mu f.
  split=> //; split.
  - rewrite null_measure_essential_norm_zero; exact: ltry.
  - constructor; first exact hfA.1.
    have hl : partial_function_nonzero_locus 0%R f = set0.
      apply/seteqP; split; last by move=> x [].
      by move=> x [y []].
    rewrite hl; exact: empty_set_countably_measurable.
exact (@measure_linfinity_finite_image_dense R X V N hN n e mu hm f epsilon he hf heps).
Qed.

(** Source for [compact_finite_empty_zero_regression]: empty compact set and
    fixed zero in the approximation underlying Federer 2.4.12, p. 87 The
    seal still supplies a finite-image Borel map and its zero value is
    forced. *)
Example compact_finite_empty_zero_regression (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (epsilon : R) (he : (0 < epsilon)%R) :
  let a := @CompactFiniteApproximation.value R [the metricType R of real_norm_metric_space hN]
    set0 epsilon 0%R compact0 he in a 0%R=0%R.
Proof.
move=> a.
have ha := @CompactFiniteApproximation.laws R [the metricType R of real_norm_metric_space hN]
  set0 epsilon 0%R compact0 he.
have hb := @compact_finite_reference_error R [the metricType R of real_norm_metric_space hN]
  set0 epsilon 0%R a ha 0%R.
rewrite mdistxx in hb.
have hz : mdist (0%R : real_norm_metric_space hN) (a 0%R)=0%R.
  apply/eqP; rewrite eq_le; apply/andP; split=> //; exact: mdist_ge0.
symmetry; exact: mdist_positivity hz.
Qed.

(** Regression examples for vector-integral laws in Federer (1969), 2.4.12,
    pp. 87–88. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic PartialNormedArithmetic
  MeasureUP NonnegativeSum MeasureVectorIntegralUP MeasureVectorIntegralZero
  MeasureVectorIntegralAlmostEquality MeasureVectorIntegralScale MeasureVectorIntegralBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [vector_integral_null_empty_regression]: null measure
    and empty partial-domain boundary of the vector-integral specification
    in Federer 2.4.12, pp. 87–88. Existence follows from
    the checked zero integral and almost equality, without target completeness. *)
Example vector_integral_null_empty_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N) :
  is_measure_vector_integral (fun _ : set X => (0 : \bar R))
    (@partial_function_empty X (real_norm_metric_space hN)) 0%R.
Proof.
pose mu := fun _ : set X => (0 : \bar R).
have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
exact (@measure_vector_integral_almost_equal R X V N hN mu hm _ _ 0%R
  (@measure_vector_integral_zero R X V N hN mu hm) (erefl 0)).
Qed.

(** Source for [vector_integral_zero_scalar_regression]: scalar-zero
    boundary of linearity in Federer 2.4.12, pp. 87–88.
    Multiplication by zero preserves the original partial domain and
    has integral zero, including on a source of infinite measure. *)
Example vector_integral_zero_scalar_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (real_norm_metric_space hN)) (y : V) :
  is_measure_vector_integral mu f y ->
  is_measure_vector_integral mu (partial_vector_scale 0%R f) 0%R /\
  partial_function_domain (partial_vector_scale 0%R f)=partial_function_domain f.
Proof.
move=> hi; split.
- have h := @measure_vector_integral_scale R X V N hN mu hm 0%R f y hi.
  by rewrite scale0r in h.
- apply/seteqP; split=> x.
  + move=> [z [u [hu _]]]; by exists u.
  + move=> [u hu]; exists (0%R : V); exists u; split=> //; by rewrite scale0r.
Qed.

(** Regression examples for finite-image vector integrals in Federer (1969),
    2.4.12, pp. 87–88. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureUP MeasureStepFunctionUP CharacteristicFunctionUP MeasureVectorIntegralUP
  MeasureVectorIntegralZero FiniteVectorIntegralSealed MeasureVectorCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_vector_integral_zero_fibre_regression]:
    zero-fibre boundary of the finite-image step in Federer 2.4.12,
    pp. 87–88. The sealed integral is zero even if the
    zero fibre is the entire source and has infinite measure. *)
Example finite_vector_integral_zero_fibre_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hfinite : finite_set (partial_function_range
      (partial_function_total (fun _ : X => (0%R : real_norm_metric_space hN))))) :
  @FiniteVectorIntegral.value R X V N hN mu hm _
    (@measure_lp_total_zero_membership R X V N hN mu hm 1%R (lexx _)) hfinite = 0%R.
Proof.
exact (@measure_vector_integral_unique R X V N hN mu _ _ _
  (@FiniteVectorIntegral.laws R X V N hN mu hm _
    (@measure_lp_total_zero_membership R X V N hN mu hm 1%R (lexx _)) hfinite)
  (@measure_vector_integral_zero R X V N hN mu hm)).
Qed.

(** Source for [vector_characteristic_null_set_regression]: measure-zero
    boundary of the elementary vector integral in Federer 2.4.12, pp. 87–88
    Any vector coefficient has integral zero on a measurable null set. *)
Example vector_characteristic_null_set_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> real_line_metric R) (y : V) :
  is_characteristic_function A s -> measure_measurable mu A -> mu A=0 ->
  is_measure_vector_integral mu
    (partial_function_total (fun x => (s x *: y : real_norm_metric_space hN))) 0%R.
Proof.
move=> hs hA hz.
have hi := @measure_vector_characteristic_integral R X V N hN mu hm A s 0%R y hs hA hz.
by rewrite scale0r in hi.
Qed.

(** Regression examples for the constructed vector integral in Federer
    (1969), 2.4.12, pp. 87–88. These examples use only the public integral
    specification and its uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP PartialFunctionUP PartialFunctionBasic
  MeasureUP NonnegativeSum MeasureLpMembershipUP MeasureVectorIntegralUP MeasureVectorIntegralZero
  MeasureVectorIntegralAlmostEquality MeasureVectorIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [constructed_vector_integral_zero_regression]: zero
    boundary of the actual integral in Federer 2.4.12, pp. 87–88.
    The ambient measure may be infinite and target dimension may be zero. *)
Example constructed_vector_integral_zero_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) :
  @measure_vector_integral R X V N hN hY mu hm _
    (@measure_lp_total_zero_membership R X V N hN mu hm 1%R (lexx _)) = 0%R.
Proof.
exact (@measure_vector_integral_unique R X V N hN mu _ _ _
  (@measure_vector_integral_specification R X V N hN hY mu hm _
    (@measure_lp_total_zero_membership R X V N hN mu hm 1%R (lexx _)))
  (@measure_vector_integral_zero R X V N hN mu hm)).
Qed.

(** Source for [constructed_vector_integral_empty_null_regression]:
    empty-domain boundary of Federer's partial-function integral,
    2.4.12, pp. 87–88. Under null measure the empty
    function is L1 and the public chosen integral is zero. *)
Example constructed_vector_integral_empty_null_regression (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN]) :
  let mu := fun _ : set X => (0 : \bar R) in
  let f := @partial_function_empty X (real_norm_metric_space hN) in
  exists (hm : is_measure mu) (hf : is_measure_lp_function mu 1%R f),
    @measure_vector_integral R X V N hN hY mu hm f hf=0%R.
Proof.
move=> mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hi := @measure_vector_integral_almost_equal R X V N hN mu hm _ f 0%R
  (@measure_vector_integral_zero R X V N hN mu hm) (erefl 0).
exists hm,hi.1.
exact (@measure_vector_integral_unique R X V N hN mu f _ 0%R
  (@measure_vector_integral_specification R X V N hN hY mu hm f hi.1) hi).
Qed.

(** Regression examples for the normed dual and bidual in Federer (1969),
    2.4.12, pp. 87–88. Source context: ContinuousBidualUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom LinearBasis RealNormUP ContinuousDualUP
  ContinuousDualNorm ContinuousBidualUP ContinuousBidualIsometry
  ContinuousBidualSealed FiniteContinuousReflexivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [measure_bidual_zero_norm_example]: regression at
    the zero vector for Federer's isometry, 2.4.12, p. 87.
    The actual sealed embedding is used, with no dimension restriction. *)
Example measure_bidual_zero_norm_example (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN) :
  BN (ContinuousBidual.value hB 0) = 0.
Proof.
rewrite (continuous_bidual_isometry hB (ContinuousBidual.laws hB)).
exact: real_seminorm_zero hN.1.
Qed.

(** Source for [measure_zero_dimensional_bidual_example]: regression
    for the zero-dimensional case of finite-dimensional reflexivity,
    Federer 2.4.12, p. 88. An empty basis forces every bidual vector to zero. *)
Example measure_zero_dimensional_bidual_example (R : realType) (V D B : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom V R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (e : 'I_0 -> V) (he : is_basis e) : forall b : B, b = 0.
Proof.
have hv : forall y : V, y = 0.
  apply: (basis_induction he)=> [|x y -> ->|c y ->|i].
  - by [].
  - exact: addr0.
  - exact: scaler0.
  - exfalso; have hi := ltn_ord i; by move: hi; rewrite ltn0.
move=> b; have [y hy] := finite_continuous_dual_reflexive he hB
  (ContinuousBidual.laws hB) b.
by rewrite -hy (hv y) linear0.
Qed.

(** Regression examples for Federer (1969), 2.4.16, pp. 89–90, with the
    unit-ball correction from erratum p. 2, book p. 89 line 19. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic NonnegativeSum MeasureUP
  MeasurableNormedBasic CountablyMeasurableUP CountablyMeasurableSubsets MeasureLpNorm MeasureLpZero
  MeasureEssentialNormAttainment ConjugateExponents ExtendedRealBoundsUP MeasureDualTestUP
  MeasureFiniteZeroDualSupremum MeasureLinfinityDuality DualTestSign.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_dual_null_nonzero_regression]: regression
    for the norm-at-most-one correction to Federer 2.4.16, p. 89.
    A pointwise nonzero constant has norm zero under the null measure;
    both the ordinary and exact-sign dual suprema must be zero. *)
Example finite_dual_null_nonzero_regression (R : realType) (X : choiceType) (p : R) :
  (1 < p)%R ->
  let mu := fun _ : set X => (0 : \bar R) in
  let f := partial_function_total (fun _ : X => (1%R : real_norm_metric_space (scalar_absolute_value_norm R))) in
  is_extended_real_supremum (finite_dual_integral_values mu (finite_conjugate_exponent p) f) 0 /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu (finite_conjugate_exponent p) f) 0.
Proof.
move=> hp mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf := @measurable_normed_total_constant R X R^o _ (scalar_absolute_value_norm R) mu hm 1%R.
have hz : measure_lp_norm mu (fun y : R => `|y|%R) p f=0.
  apply: (@lp_norm_zero_iff R X R^o _ (scalar_absolute_value_norm R) mu hm p f (ltW hp) hf.1).2.
  by [].
exact: (@finite_zero_dual_supremum R X mu hm p f hp hf.1 hz).
Qed.

(** Source for [linfinity_dual_null_nonzero_regression]: zero
    essential-norm boundary of Federer 2.4.16, pp. 89–90.
    The exact-sign test family is nonempty even for a nonzero
    function on a null space; no norm-one test is required. *)
Example linfinity_dual_null_nonzero_regression (R : realType) (X : choiceType) :
  let mu := fun _ : set X => (0 : \bar R) in
  let f := fun _ : X => (1%R : real_norm_metric_space (scalar_absolute_value_norm R)) in
  is_extended_real_supremum (finite_dual_integral_values mu 1%R (partial_function_total f)) 0 /\
  is_extended_real_supremum (sign_matching_finite_dual_values mu 1%R (partial_function_total f)) 0.
Proof.
move=> mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf := @measurable_normed_total_constant R X R^o _ (scalar_absolute_value_norm R) mu hm 1%R.
have hc : is_countably_measure_measurable_function mu (0%R : real_norm_metric_space (scalar_absolute_value_norm R))
    (partial_function_total f).
  constructor; first exact hf.1.
  apply: (@null_set_countably_measurable R X mu hm); by [].
have hh := @linfinity_dual_supremum R X mu hm f hc.
by rewrite null_measure_essential_norm_zero in hh.
Qed.

(** Source for [dual_sign_replacement_regression]: Federer 2.4.16, p. 90,
    prints the correct sign(f) factor; using f itself does not preserve the
    test bound. *)
Example dual_sign_replacement_regression (R : realType) :
  (`|dual_test_sign_alignment (2:R) 1| <= 1)%R /\
  ~ (`|1 * Num.sg (1:R) * 2| <= 1)%R.
Proof.
split.
- have hh := @dual_test_sign_alignment_bound R 2%R 1%R; by rewrite normr1 in hh.
- have hh := @dual_test_missing_sign_counterexample R; by rewrite normr1 in hh.
Qed.

(** Regression examples for Federer (1969), 2.4.17, p. 90. The tests cover
    zero norms despite nonzero functions, the reciprocal zero convention,
    and the corrected absolute-value split. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic NonnegativeSum MeasureUP
  MeasurableNormedBasic MeasureExponentDomain MeasureExponentZero ReciprocalExponent MeasureReciprocalInterval
  MeasureEssentialNormAttainment MeasureExponentContinuity SignedExponentSplitCounterexample RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [null_measure_exponent_domain_regression]: zero-norm case of
    P and U in Federer 2.4.17, p. 90 A nonzero constant under the null
    measure belongs to P at every admissible exponent, whereas U is empty,
    including reciprocal exponent zero. *)
Example null_measure_exponent_domain_regression (R : realType) (X : choiceType) :
  let mu := fun _ : set X => (0 : \bar R) in
  let f := fun _ : X => (1%R : real_norm_metric_space (scalar_absolute_value_norm R)) in
  (forall p, 1 <= p -> measure_finite_norm_exponents mu (partial_function_total f) p) /\
  (forall u, ~ measure_positive_reciprocal_exponents mu (partial_function_total f) u).
Proof.
move=> mu f; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf := (@measurable_normed_total_constant R X R^o _ (scalar_absolute_value_norm R) mu hm 1%R).1.
have hz p (hp : 1 <= p) : measure_exponent_norm mu (partial_function_total f) p=0.
  apply: (@measure_exponent_norm_zero_iff R X mu hm f p hp hf).2; by [].
split.
- move=> p hp; split=> //; by rewrite hz // ltry.
- move=> u [hu0 [hu1 [hup huf]]].
  have hd := @reciprocal_lebesgue_exponent_domain R u hu0 hu1.
  rewrite MeasureReciprocalInterval.measure_reciprocal_exponent_normE (hz _ hd) ltxx in hup.
  by move: hup.
Qed.

(** Source for [reciprocal_zero_infinity_regression]: the explicit
    convention 1/0=infinity in Federer 2.4.17, p. 90 This must differ from
    ordinary field inversion, whose value at zero is zero. *)
Example reciprocal_zero_infinity_regression (R : realType) :
  reciprocal_lebesgue_exponent (0 : R)=+oo /\ ((0 : R)^-1=0)%R.
Proof. by rewrite /reciprocal_lebesgue_exponent eqxx invr0. Qed.

(** Source for [exponent_absolute_split_regression]: Regression supporting
    Federer 2.4.17, p. 90: a split on signed function values fails at f=-2
    when the exponent decreases from two to one. *)
Example exponent_absolute_split_regression (R : realType) :
  ((-2 : R) <= 1)%R /\ ~ (real_power `|(-2 : R)| 2 <= real_power `|(-2 : R)| 1)%R.
Proof. exact: signed_exponent_split_counterexample. Qed.

From Federer Require Import PartialFunctionUP MeasurableFunctionUP MeasurePartialExponentContinuity.
(** Source for [null_measure_partial_exponent_continuity_regression]:
    conull-domain boundary case of Federer 2.4.17, p. 90,
    with 2.3.2, p. 73. Under the null measure every
    partial function is measurable, even with empty domain, and
    the closure-continuity assertion must still apply. *)
Example null_measure_partial_exponent_continuity_regression (R : realType) (X : choiceType)
    (f : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  let mu := fun _ : set X => (0 : \bar R) in
  continuous (fun p : subspace (closure
      (measure_finite_norm_exponents mu f : set (ExtendedRealOrderTopology.extended_real_line R))) =>
    (measure_exponent_norm mu f p : ExtendedRealOrderTopology.extended_real_line R)).
Proof.
move=> mu; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
apply: (@measure_partial_exponent_norm_continuous_on_closure R X mu hm f).
constructor; first by [].
move=> U hU A; by rewrite /mu add0e.
Qed.

(** Federer (1969), 2.4.18, pp. 90–91: compositions and image measures. Here
    u is total, as in Federer; f retains its possibly proper domain. The
    local Federer erratum contains no correction to this item. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialFunctionBasic
  PartialFunctionPrecomposition PartialFunctionIntegralParts MeasureUpperIntegralPositivePart
  MeasureUP MeasurePushforward NonnegativeSum MeasurableFunctionUP PushforwardMeasurableFunctions
  MeasureIntegralUP MeasureIntegralUniqueness MeasureIntegralPartsDifference PushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [pushforward_null_partial_integrability_regression]:
    conull-domain boundary case of Federer 2.4.18(1)–(2), pp. 90–91 Every
    partial f, including an empty graph, is measurable for the null measure,
    and the two integrability domains agree. *)
Example pushforward_null_partial_integrability_regression (R : realType) (X Y : choiceType)
    (u : X -> Y) (f : partial_function Y (extended_real_line R)) :
  let mu := fun _ : set X => (0 : \bar R) in
  is_measure_measurable_function (measure_pushforward u mu) f /\
  (is_measure_integrable mu (partial_function_precompose u f) <->
    is_measure_integrable (measure_pushforward u mu) f).
Proof.
move=> mu; have hm : is_measure mu.
  constructor; first by move=> A.
  move=> A F hc hcov; exact: nonnegative_sum_nonnegative.
have hf : is_measure_measurable_function mu (partial_function_precompose u f).
  constructor; first by [].
  move=> U hU A; by rewrite /mu add0e.
split.
- exact: (@pushforward_function_measurable_from_composition R X Y (extended_real_line R) mu u f hf).
- exact: (@measure_pushforward_integrable_iff R X Y mu hm u f hf).
Qed.

(** Source for [pushforward_undefined_integral_regression]: the definedness
    convention implicit in Federer 2.4.18(1), p. 90, and explicit in its use
    of 2.4.4(6) on p. 91 If both target part integrals are infinite, neither
    side has an assigned signed integral; equality must not create one. *)
Example pushforward_undefined_integral_regression (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (u : X -> Y)
    (f : partial_function Y (extended_real_line R)) :
  is_measure_measurable_function mu (partial_function_precompose u f) ->
  is_measure_integral (measure_pushforward u mu) (partial_extended_function_positive_part f) +oo ->
  is_measure_integral (measure_pushforward u mu) (partial_extended_function_negative_part f) +oo ->
  ~ is_measure_integrable mu (partial_function_precompose u f) /\
  ~ is_measure_integrable (measure_pushforward u mu) f.
Proof.
move=> hf hp hn.
have hpush := @measure_pushforward_is_measure R X Y u mu hm.
have hnot : ~ is_measure_integrable (measure_pushforward u mu) f.
  move=> [a ha].
  have [P [N [hP [hN he]]]] := (@measure_integral_parts_iff R Y _ hpush f a).1 ha.
  have ep := measure_integral_unique hP hp; have en := measure_integral_unique hN hn.
  by rewrite ep en /extended_subtract /extended_add /= in he.
split=> // hX; apply: hnot.
exact: (@measure_pushforward_integrable_iff R X Y mu hm u f hf).1 hX.
Qed.

(** Regression examples for Federer (1969), 2.4.19, p. 91 They check a
    translated singleton domain, relative continuity without any control off
    C, positive-infinite scalar integral, and the impossible empty range. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric CompleteMetricUP RealMetricBackground MetricSubsetBackground
  ExtendedRealOrderTopology PartialFunctionUP PartialFunctionPostcomposition MeasureUP MeasureAlmostUP
  MeasureIntegralUP MeasureVectorIntegralUP ConvexFunctionUP MeasureLpRangeRepresentative MeasureJensen.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [jensen_singleton_relative_continuity_example]: regression
    for the relative-C hypothesis in Federer 2.4.19, p. 91 C may be a
    nonzero singleton and F is unrestricted off that singleton. *)
Example jensen_singleton_relative_continuity_example (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (c : real_norm_metric_space hN) (F : real_norm_metric_space hN -> real_line_metric R)
    (g : partial_function X (real_norm_metric_space hN)) (y : real_norm_metric_space hN) (a : \bar R) :
  mu setT=m%:E -> (0 < m)%R -> (0 <= F c)%R ->
  measure_almost_everywhere mu (partial_function_preimage g [set c]) ->
  is_measure_vector_integral mu g y ->
  is_measure_integral mu (partial_function_postcompose g (fun z => ((F z)%:E : extended_real_line R))) a ->
  ((m^-1)%R *: y)%R=c /\ (F c)%:E <= a * (m^-1)%R%:E.
Proof.
move=> hmass hm0 hpos hgC hy ha.
have hC : closed ([set c] : set (real_norm_metric_space hN)).
  apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
have hconv : is_real_convex_function_on [set c] F.
  split.
  - move=> x z hx hz t ht ht1; change (x=c) in hx; change (z=c) in hz.
    by rewrite hx hz -scalerDl subrK scale1r.
  - move=> x z hx hz t ht ht1; change (x=c) in hx; change (z=c) in hz.
    by rewrite hx hz -scalerDl subrK scale1r -mulrDl subrK mul1r.
have hcts : continuous (fun z : metric_subset [set c] => F (val z)).
  have he : (fun z : metric_subset [set c] => F (val z))=(fun _ : metric_subset [set c] => F c).
    apply: funext=> z; have hz : val z=c := set_valP z; by rewrite hz.
  rewrite he=> z; exact: (@cvg_cst (real_line_metric R) (F c) (metric_subset [set c]) (nbhs z) _).
have hp z : [set c] z -> (0 <= F z)%R by move=> ->.
have hh := @measure_jensen_integral_values R X V N hN hY mu hm m [set c] F g y a
  hmass hm0 hC hconv hcts hp hgC hy ha.
have he : ((m^-1)%R *: y)%R=c := hh.1.
split=> //; by rewrite -he; exact hh.2.
Qed.

(** Source for [jensen_infinite_integral_mean_example]: regression for the
    allowed infinite right-hand integral in Federer 2.4.19, p. 91 Mean
    membership remains a substantive assertion in this case. *)
Example jensen_infinite_integral_mean_example (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (hY : is_complete_metric_space [the metricType R of real_norm_metric_space hN])
    (mu : set X -> \bar R) (hm : is_measure mu) (m : R)
    (C : set (real_norm_metric_space hN)) (F : real_norm_metric_space hN -> real_line_metric R)
    (g : partial_function X (real_norm_metric_space hN)) (y : real_norm_metric_space hN) :
  mu setT=m%:E -> (0 < m)%R -> closed C -> is_real_convex_function_on C F ->
  continuous (fun z : metric_subset C => F (val z)) -> (forall z, C z -> (0 <= F z)%R) ->
  measure_almost_everywhere mu (partial_function_preimage g C) ->
  is_measure_vector_integral mu g y ->
  is_measure_integral mu (partial_function_postcompose g (fun z => ((F z)%:E : extended_real_line R))) +oo ->
  C ((m^-1)%R *: y)%R.
Proof.
move=> hmass hm0 hC hconv hF hpos hgC hy ha.
exact: (@measure_jensen_integral_values R X V N hN hY mu hm m C F g y +oo
  hmass hm0 hC hconv hF hpos hgC hy ha).1.
Qed.

(** Source for [jensen_empty_range_positive_mass_example]: regression for
    the positive-mass and conull-range hypotheses in Federer 2.4.19, p. 91
    They prevent applying Jensen to an empty convex target. *)
Example jensen_empty_range_positive_mass_example (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (g : partial_function X Y) :
  mu setT != 0 -> ~ measure_almost_everywhere mu (partial_function_preimage g set0).
Proof.
move=> hm hg; have [y hy] := @positive_measure_conull_range_nonempty R X Y mu g set0 hm hg.
exact hy.
Qed.

(** Boundary regressions for Federer (1969), 2.5.1, pp. 91–92 These check
    empty lattices, the distinction from vector spaces, and the sign
    restriction on constant truncation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import PartialFunctionBasic MeasureUP MeasureStepConstants MeasureStepIntegralIdentification
  MeasureIntegralUP MeasureIntegralUniqueness FunctionLatticeUP FunctionLatticeLaws ContinuousFunctionLattice
  SummableRealFunctionUP SummableRealFunctionLattice.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_function_lattice_example]: boundary of the
    closure-only definition in Federer 2.5.1, p. 91 The empty lattice is
    permitted, so unconditional zero membership would be incorrect. *)
Example empty_function_lattice_example (R : realType) (X : Type) :
  is_function_lattice (set0 : set (X -> R)) /\ ~ (set0 : set (X -> R)) (fun _ => 0%R).
Proof. split; [by constructor|by []]. Qed.

(** Source for [positive_lattice_not_negation_closed_example]: regression
    for L+ in Federer 2.5.1, p. 91 *)
Example positive_lattice_not_negation_closed_example (R : realType) :
  let L := positive_function_lattice (setT : set (unit -> R)) in
  is_function_lattice L /\ L (fun _ => 1%R) /\ ~ L (fun _ => (-1)%R).
Proof.
move=> L; split; first exact: positive_function_lattice_laws (all_functions_lattice R unit).
split.
- split=> // x; exact: ler01.
- move=> [_ hn]; have hh := hn tt; by move: hh; rewrite oppr_ge0 ler10.
Qed.

(** Source for [negative_ceiling_not_summable_example]: regression for the
    nonnegative-ceiling premise in Federer 2.5.1, p. 91 On an
    infinite-measure source, truncating zero by -1 gives a nonsummable
    constant. This is a boundary explanation, not a correction to Federer. *)
Example negative_ceiling_not_summable_example (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) : mu setT=+oo ->
  ~ summable_real_functions mu (fun _ : X => Order.min 0%R (-1)%R).
Proof.
move=> hmass.
have he : (fun _ : X => Order.min (0%R : R) (-1)%R)=(fun _ : X => (-1)%R).
  apply: funext=> x; by rewrite min_r // oppr_le0 ler01.
rewrite he; move=> [a ha].
have hs := @measure_step_constant_integral R X mu hm (-1)%R.
have hneg : ((-1)%R%:E : \bar R) < 0 by rewrite lte_fin oppr_lt0 ltr01.
rewrite hmass (lt0_muley hneg) in hs.
have hi := @measure_step_function_integral R X mu hm _ (-oo) (measure_step_constant hm (-1)%R) hs.
have hh := measure_integral_unique ha hi; discriminate hh.
Qed.

(** Boundary regressions for Federer (1969), 2.5.2, pp. 92–93 These check
    the empty-lattice split, a positive cone without negation closure, and a
    zero functional. They do not identify arbitrary representing measures as
    unique. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLaws ContinuousFunctionLattice MonotoneDaniellIntegralUP
  RealScalarOrderLimits DaniellCoverUP DaniellCoverBasic DaniellCoverSealed DaniellEmptyBoundary
  MonotoneDaniellRepresentation RealIntegralFunctionalUP MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_lattice_representation_example]: the empty case of
    Federer 2.5.2, p. 92 The theorem still represents the empty domain for
    an arbitrary ambient functional. *)
Example empty_lattice_representation_example (R : realType) (X : choiceType)
    (A : (X -> R) -> R) : exists mu, is_measure mu /\ is_real_integral_functional mu set0 A.
Proof.
apply: (@monotone_daniell_representation R X set0 A); first by constructor.
constructor.
- by move=> f g [].
- by move=> c f hc [].
- by move=> f g [].
- by move=> f g hf [].
Qed.

(** Source for [empty_lattice_cover_failure_example]: Supporting Federer
    2.5.2, p. 92.The envelope exists for an empty lattice but is not a
    measure. *)
Example empty_lattice_cover_failure_example (R : realType) (X : choiceType)
    (A : (X -> R) -> R) : exists mu,
  is_daniell_cover_envelope set0 A mu /\ ~ is_measure mu.
Proof.
exists (@DaniellCover.value R X set0 A).
have he := @DaniellCover.laws R X set0 A.
split=> //; exact: daniell_empty_envelope_not_measure he.
Qed.

(** Source for [positive_cone_daniell_representation_example]: a lattice
    need not be a vector space in Federer 2.5.1–2.5.2, pp. 91–92 Evaluation
    on the positive cone satisfies the four laws and is represented by the
    theorem. *)
Example positive_cone_daniell_representation_example (R : realType) :
  let L := positive_function_lattice (setT : set (unit -> R)) in
  ~ L (fun _ => (-1)%R) /\
  exists mu, is_measure mu /\ is_real_integral_functional mu L (fun f => f tt).
Proof.
move=> L; split.
- move=> [_ hp]; have hh := hp tt; by move: hh; rewrite oppr_ge0 ler10.
- apply: (@monotone_daniell_representation R [the choiceType of (unit : Type)] L (fun f => f tt)).
  + exact: positive_function_lattice_laws (all_functions_lattice R unit).
  + constructor.
    * by move=> f g hf hg.
    * by move=> c f hc hf.
    * move=> f g hf hg hfg; exact: hfg tt.
    * move=> f g hf hg hinc; exact: hinc tt.
Qed.

(** Source for [zero_daniell_functional_zero_mass_example]: zero-functional
    boundary of the suiting-sequence construction in Federer 2.5.2, p. 92
    The constant one sequence forces the representing envelope's total mass
    to vanish. *)
Example zero_daniell_functional_zero_mass_example (R : realType) (X : choiceType) :
  exists mu, is_measure mu /\ mu setT=0 /\
    is_real_integral_functional mu (setT : set (X -> R)) (fun _ => 0%R).
Proof.
pose L := (setT : set (X -> R)).
pose A := fun _ : X -> R => (0%R : R).
have hL : is_function_lattice L := all_functions_lattice R X.
have hA : is_monotone_daniell_integral L A.
  constructor.
  - by move=> f g hf hg; rewrite /A add0r.
  - by move=> c f hc hf; rewrite /A mulr0.
  - by move=> f g hf hg hfg; rewrite /A.
  - move=> f g hf hg hinc; split; first by move=> n m hnm.
    exact: real_constant_order_limit.
pose mu := @monotone_daniell_measure R X L A hL hA.
have hm : is_measure mu := monotone_daniell_measure_is_measure hL hA.
have hne : exists f, L f by exists (fun _ => 1%R).
have hc : is_daniell_cover_envelope L A mu := monotone_daniell_measure_envelope hL hA hne.
have hs : is_daniell_suiting_sequence L setT (fun _ : nat => fun _ : X => 1%R).
  split.
  - move=> n; split=> // x; exact: ler01.
  - split; first by move=> n m hnm x.
    move=> x hx r hr; exists 0%N; exact hr.
have hb := daniell_cover_lower hc hs (daniell_constant_sequence_cost A (fun _ : X => 1%R)).
have hz : mu setT=0 by apply/eqP; rewrite eq_le hb (measure_nonnegative hm).
exists mu; split=> //; split=> //; exact: monotone_daniell_measure_represents.
Qed.

(** Boundary regressions for Federer (1969), 2.5.3, pp. 94–95. These
    examples test the empty lattice, the discontinuous sequence limit, and a
    partial function with empty but conull domain for zero measure. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialExtendedArithmetic PartialAbsolutePartsGraph PartialExtendedOrderLoci
  FunctionLatticeUP ContinuousFunctionLattice FunctionLatticeRegularityUP DaniellEmptyBoundary
  SequencePrefixIndicators SequenceLimitFunctionalUP SequenceLimitFunctionalLaws SequenceLimitFunctionalSealed
  DaniellCoverUP DaniellCoverBasic DaniellPositiveL1Density RealIntegralFunctionalUP SummableRealFunctionUP
  ExtendedRealBoundsUP MeasureUP MeasureAlmostUP MeasureIntegralUP MeasureConullZeroIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_lattice_zero_measure_not_regular_example]: the
    empty-lattice boundary of Federer 2.5.3, p. 94 Even zero measure cannot
    satisfy the finite-hull definition when no lattice functions exist,
    although 2.5.2 has a vacuous representation. *)
Example empty_lattice_zero_measure_not_regular_example (R : realType) :
  ~ is_function_lattice_regular (set0 : set (unit -> R))
    (fun _ : set unit => (0 : \bar R)).
Proof.
exact: (@empty_function_lattice_not_regular R [the choiceType of (unit : Type)] _
  (@daniell_zero_measure R [the choiceType of (unit : Type)])).
Qed.

(** Source for [sequence_prefix_limit_jump_example]: explicit witness values
    in the final counterexample of Federer 2.5.3, p. 95 Every finite prefix
    has functional value zero, whereas the pointwise increasing limit has
    functional value one. *)
Example sequence_prefix_limit_jump_example (R : realType) k :
  @SequenceLimitFunctional.value R (@sequence_prefix_indicator R k)=0%R /\
  @SequenceLimitFunctional.value R (fun _ => 1%R)= 1%R.
Proof.
have hA := @SequenceLimitFunctional.laws R; split.
- exact: (@sequence_limit_functional_value R _ hA _ 0%R (@sequence_prefix_indicator_limit_zero R k)).
- exact: (@sequence_limit_functional_constant R _ hA 1%R).
Qed.

(** Source for [zero_measure_empty_domain_density_example]: partial-domain
    regression for the second further condition in Federer 2.5.3, p. 94,
    with the convention in 2.3.1, p. 72 The empty function is summable for
    zero measure, so density must not silently require a total target or a
    nonnull domain. *)
Example zero_measure_empty_domain_density_example (R : realType) :
  let X := [the choiceType of (unit : Type)] in
  let mu := fun _ : set X => (0 : \bar R) in
  let f := @partial_function_empty X (extended_real_line R) in
  partial_function_domain f=set0 /\
  exists (h : X -> R) (q : R), positive_function_lattice setT h /\
    is_measure_integral mu
      (partial_extended_function_absolute_value (partial_extended_function_subtract (real_total_integrand h) f)) q%:E /\
    (q < 1)%R.
Proof.
move=> X mu f; split; first exact: partial_function_empty_domain.
pose L := (setT : set (X -> R)).
pose A := fun _ : X -> R => (0%R : R).
have hm : is_measure mu := @daniell_zero_measure R X.
have hL : is_function_lattice L := all_functions_lattice R X.
have hA : is_real_integral_functional mu L A.
  move=> g hg; apply: (@measure_almost_zero_integral R X mu hm (real_total_integrand g)); by [].
have hc : is_daniell_cover_envelope L A mu.
  constructor.
  - move=> S g c hg hcost.
    apply: (extended_real_supremum_upper hcost); by exists 0%N.
  - move=> S b hb; apply: (hb (fun _ : nat => fun _ : X => 1%R) 0).
    + split.
      * move=> n; split=> // x; exact: ler01.
      * split; first by move=> n m hnm x.
        move=> x hx r hr; exists 0%N; exact hr.
    + exact: (@daniell_constant_sequence_cost R X A (fun _ => 1%R)).
have hf : is_measure_summable mu f.
  exists 0%R; apply: (@measure_almost_zero_integral R X mu hm f); by [].
have hp : measure_almost_everywhere mu (partial_extended_nonnegative_locus f) by [].
exact: (@daniell_nonnegative_summable_lattice_density R X L A hL mu hm hA hc f 1%R hf hp ltr01).
Qed.

(** Boundary regressions for Federer (1969), 2.5.5, pp. 96–97 These check
    the nonempty-lattice correction and the fact that the original Daniell
    integral need not be monotone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ContinuousFunctionLattice FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP DaniellIntegralUP DaniellIntegralNegation MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for
    [empty_daniell_lattice_has_no_regular_representation_example]: local
    boundary correction to Federer 2.5.5, p. 96. The empty lattice satisfies
    all four functional hypotheses but has no L+ regular measure. *)
Example empty_daniell_lattice_has_no_regular_representation_example (R : realType) :
  is_function_lattice (set0 : set (unit -> R)) /\
  is_daniell_integral (set0 : set (unit -> R)) (fun _ => 0) /\
  ~ exists mu : set unit -> \bar R, is_measure mu /\
    is_function_lattice_regular (positive_function_lattice (set0 : set (unit -> R))) mu.
Proof.
split; first by constructor.
split; first by constructor.
move=> [mu [hm hr]].
have he : positive_function_lattice (set0 : set (unit -> R))=set0.
  apply/seteqP; split; [by move=> f [[] _]|by move=> f []].
rewrite he in hr.
exact: (@empty_function_lattice_not_regular R [the choiceType of (unit : Type)] mu hm hr).
Qed.

(** Source for [negative_evaluation_daniell_not_monotone_example]:
    regression distinguishing the hypotheses of Federer 2.5.5, p. 96, from
    2.5.2, p. 92. Negative evaluation satisfies the Daniell laws but
    reverses the order between the constants zero and one. *)
Example negative_evaluation_daniell_not_monotone_example (R : realType) :
  let L := (setT : set (unit -> R)) in
  let A := fun f : unit -> R => - f tt in
  is_daniell_integral L A /\ ~ is_monotone_daniell_integral L A.
Proof.
move=> L A.
have hL : is_function_lattice L := all_functions_lattice R unit.
have hD : is_monotone_daniell_integral L (fun f => f tt).
  constructor.
  - by move=> f g hf hg.
  - by move=> c f hc hf.
  - by move=> f g hf hg hfg; exact: hfg.
  - by move=> f g hf hg hfg; exact: hfg tt.
split.
- exact: (@daniell_integral_negate R unit L (fun f => f tt) hL (monotone_daniell_is_daniell hD)).
- move=> hbad.
  have h01 : function_le (fun _ : unit => (0 : R)) (fun _ => 1) by move=> x; exact: ler01.
  have hh := @monotone_daniell_integral_monotone R unit L A hbad (fun _ => 0) (fun _ => 1) I I h01.
  by move: hh; rewrite /A oppr0 oppr_ge0 ler10.
Qed.

(** Regression examples for Federer (1969), 2.5.6, pp. 97–98. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ContinuousFunctionLattice DaniellIntegralUP
  DaniellVariationUP LatticeAdditiveFunctional LatticeExtendedVariation VectorFunctionLattice
  VectorVariationSupremum ExtendedRealBoundsUP ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_additive_variations_example]: zero-functional boundary
    regression for Federer 2.5.6, pp. 97–98 X may be empty. *)
Example zero_additive_variations_example (R : realType) (X : Type) (f : X -> R) :
  function_nonnegative f ->
  lattice_positive_variation setT (fun _ : X -> R => 0%R) f=0 /\
  lattice_negative_variation setT (fun _ : X -> R => 0%R) f=0.
Proof.
move=> hf.
have hL := all_functions_lattice R X.
have hA : is_lattice_additive_functional setT (fun _ : X -> R => 0%R).
  by move=> g h hg hh; rewrite add0r.
have hp : lattice_positive_variation setT (fun _ : X -> R => 0%R) f=0.
  apply/eqP; rewrite eq_le; apply/andP; split.
  - apply: extended_real_sup_least=> v [g [hg ->]]; exact: lexx.
  - exact: (@lattice_positive_variation_nonnegative R X setT _ hL hA f (conj I hf)).
split=> //; rewrite lattice_negative_variation_dual.
have he : (fun _ : X -> R => (-0)%R)=(fun _ => (0%R : R)).
  by apply: funext=> g; rewrite oppr0.
by rewrite he.
Qed.

(** Source for [infinite_variations_together_example]: regression that the
    finiteness assertion in Federer 2.5.6, pp. 97–98, retains its content
    when the interval supremum is unbounded No boundedness premise is added. *)
Example infinite_variations_together_example (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) f :
  is_function_lattice L -> is_lattice_additive_functional L A ->
  positive_function_lattice L f -> lattice_positive_variation L A f=+oo ->
  lattice_negative_variation L A f=+oo.
Proof.
move=> hL hA hf he.
have hn : ~~ (lattice_negative_variation L A f < +oo).
  apply/negP=> hq.
  have hp := (proj2 (@lattice_variations_finite_iff R X L A hL hA f hf)) hq.
  by rewrite he ltxx in hp.
move: hn; rewrite ltey negbK; exact/eqP.
Qed.

(** Source for [negative_evaluation_absolute_supremum_example]: regression
    for the outer absolute value in Federer 2.5.6, p. 98. Negative
    evaluation on one point has zero positive variation but unit total
    variation at f=1 *)
Example negative_evaluation_absolute_supremum_example (R : realType) :
  extended_real_sup (symmetric_functional_absolute_values
    (setT : set (unit -> R)) (fun g => (- g tt)%R) (fun _ => 1%R))= 1.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- apply: extended_real_sup_least=> v [g [[hg hgf] ->]].
  rewrite lee_fin normrN; exact: hgf tt.
- apply: extended_real_sup_upper; exists (fun _ => 1%R); split.
  + split=> // x; by rewrite normr1.
  + by rewrite normrN normr1.
Qed.

(** Regression examples for Federer (1969), 2.5.7, pp. 98–99. The erratum p.
    2, book p. 98 lines 10–11, requires total domains and the closed unit
    ball. The examples include zero-norm representation at both endpoints
    and at finite conjugate exponents. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP DaniellIntegralUP FunctionLatticeSeminormUP FunctionOperatorSeminorm
  TotalScalarLpUP TotalScalarLpLattice TotalScalarLpFiniteSeminorm FiniteLpLinearDaniell DyadicAverageScore
  MeasureAlmostUP CountablyMeasurableUP RealScalarOrderLimits LpConjugatePair ConjugateExponents
  LpFunctionalDensityUP LpLinearFunctionalRepresentation TotalScalarLpZeroCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_lp_functional_is_linear]: regression of the linearity
    hypothesis of Federer 2.5.7, p. 98 This includes the zero space. *)
Example zero_lp_functional_is_linear (R : realType) (X : choiceType)
    (mu : set X -> \bar R) p :
  is_linear_functional_on_functions (total_scalar_lp mu p) (fun _ => 0%R).
Proof. split; [by move=> f g hf hg; rewrite add0r|by move=> c f hf; rewrite mulr0]. Qed.

(** Source for [zero_lp_functional_operator_norm]: regression of
    the corrected supremum in Federer 2.5.7, p. 98,
    erratum p. 2, book p. 98 line 11. The ball contains
    zero even when the unit sphere is empty; M is zero. *)
Example zero_lp_functional_operator_norm (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p :
  1 <= p -> function_operator_seminorm (total_scalar_lp mu p) (fun _ => 0%R)
    (finite_total_scalar_lp_norm mu p)=0.
Proof.
move=> hp; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@function_operator_seminorm_least_bound R X (total_scalar_lp mu p)
    (fun _ => 0%R) (finite_total_scalar_lp_norm mu p) 0%R (lexx _))=> f hf.
  by rewrite normr0 mul0r.
- exact: (@function_operator_seminorm_nonnegative R X (total_scalar_lp mu p)
    (fun _ => 0%R) (finite_total_scalar_lp_norm mu p)
    (@total_scalar_lp_vector_lattice R X mu hm p hp)
    (@zero_lp_functional_is_linear R X mu p)
    (@finite_total_scalar_lp_norm_laws R X mu hm p)).
Qed.

(** Source for [zero_finite_lp_functional_is_daniell]: regression of the
    finite-p preliminary assertion in Federer 2.5.7, p. 98 This exercises
    the actual dominated-convergence route to increasing continuity,
    including M=0, without a finite-total-mass hypothesis. *)
Example zero_finite_lp_functional_is_daniell (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) :
  (1 <= p)%R -> is_daniell_integral (total_scalar_lp mu p%:E) (fun _ => 0%R).
Proof.
move=> hp; apply: (@finite_lp_bounded_linear_is_daniell R X mu hm p (fun _ => 0%R) hp).
- exact: zero_lp_functional_is_linear.
- by rewrite (@zero_lp_functional_operator_norm R X mu hm p%:E hp) ltry.
Qed.

(** Source for [zero_dyadic_average_score]: regression of the p=1
    maximization score in Federer 2.5.7, p. 99 Zero integral coordinates
    give zero score, including the zero bound M=0. *)
Example zero_dyadic_average_score (R : realType) :
  dyadic_average_score (fun _ : nat => (0%R : R))=0%R.
Proof.
have hz : forall n : nat, (0 <= (0%R : R) <= 0)%R by move=> n; rewrite lexx.
have hh := @dyadic_average_score_bounds R (fun _ => 0%R) 0%R (lexx _)
  hz.
apply/eqP; rewrite eq_le; by have [h0 h1] := andP hh; rewrite h0 h1.
Qed.

(** Source for [zero_lp_functional_density]: regression of the
    representation and uniqueness conclusion of Federer 2.5.7, pp. 98–99, at
    M=0 The endpoint countability hypothesis is retained. *)
Example zero_lp_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q :
  is_lp_conjugate_pair p q ->
  (q=+oo -> measure_countably_measurable mu setT) ->
  exists k : X -> R, is_lp_functional_density mu p q (fun _ => 0%R) k /\
    total_scalar_lp_norm mu q k=0 /\ measure_almost_everywhere mu [set x | k x=0%R].
Proof.
move=> hpq hX.
have hp := (lp_conjugate_pair_admissible hpq).1.
have hz := @zero_lp_functional_operator_norm R X mu hm p hp.
have hb : function_operator_seminorm (total_scalar_lp mu p) (fun _ => 0%R)
    (finite_total_scalar_lp_norm mu p) < +oo by rewrite hz ltry.
have [_ [k [hk [hN hu]]]] := @lp_linear_functional_representation R X mu hm p q (fun _ => 0%R)
  hpq (@zero_lp_functional_is_linear R X mu p) hb hX
  (fun _ f g _ _ _ => @real_constant_order_limit R 0%R).
exists k; split; first exact: hk.
have hN0 : total_scalar_lp_norm mu q k=0 by rewrite hN hz.
split=> //; exact: (@total_scalar_lp_zero_norm_almost_zero R X mu hm q k hk.1 hN0).
Qed.

(** Source for [zero_finite_conjugate_functional_density]: regression of
    case (i), Federer 2.5.7, p. 98 No countable-measurability hypothesis on
    X is needed. *)
Example zero_finite_conjugate_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p : R) :
  (1 < p)%R -> exists k : X -> R,
    is_lp_functional_density mu p%:E (finite_conjugate_exponent p)%:E (fun _ => 0%R) k /\
    total_scalar_lp_norm mu (finite_conjugate_exponent p)%:E k=0 /\
    measure_almost_everywhere mu [set x | k x=0%R].
Proof.
move=> hp; apply: (@zero_lp_functional_density R X mu hm p%:E (finite_conjugate_exponent p)%:E).
- by left; exists p.
- by [].
Qed.

(** Source for [zero_l1_functional_density]: regression of case (ii),
    Federer 2.5.7, p. 98 Countable measurability of X is an explicit
    hypothesis. *)
Example zero_l1_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  measure_countably_measurable mu setT -> exists k : X -> R,
    is_lp_functional_density mu 1 +oo (fun _ => 0%R) k /\
    total_scalar_lp_norm mu +oo k=0 /\ measure_almost_everywhere mu [set x | k x=0%R].
Proof.
move=> hX; apply: (@zero_lp_functional_density R X mu hm 1 +oo).
- by right; left.
- by move=> _.
Qed.

(** Source for [zero_linfinity_functional_density]: regression of case
    (iii), Federer 2.5.7, p. 98 The zero functional has the required
    increasing continuity; no finite-mass or countable-measurability
    assumption on X is imposed. *)
Example zero_linfinity_functional_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  exists k : X -> R, is_lp_functional_density mu +oo 1 (fun _ => 0%R) k /\
    total_scalar_lp_norm mu 1 k=0 /\ measure_almost_everywhere mu [set x | k x=0%R].
Proof.
apply: (@zero_lp_functional_density R X mu hm +oo 1).
- by right; right.
- by [].
Qed.

(** Regression examples for corrected Federer (1969), 2.5.8, p. 100; erratum
    p. 2, book p. 100 line 3. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP DaniellIntegralUP TotalScalarLpUP LpFunctionalDensityUP
  MeasureAlmostUP NullMeasureEvaluation RadonNikodymDaniell RealScalarOrderLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [evaluation_null_measure_daniell_counterexample]: Supporting
    Federer 2.5.8, p. 100. *)
Example evaluation_null_measure_daniell_counterexample (R : realType) :
  let X := [the choiceType of (unit : Type)] in
  let mu := fun _ : set X => (0 : \bar R) in
  is_daniell_integral (total_scalar_lp mu +oo) (fun f => f tt) /\
    ~ exists k : X -> R, is_lp_functional_density mu +oo 1 (fun f => f tt) k.
Proof.
move=> X mu; split.
- exact: point_evaluation_is_daniell.
- exact: null_measure_evaluation_not_representable.
Qed.

(** Source for [zero_daniell_radon_nikodym_example]: zero-functional
    regression for corrected Federer 2.5.8, p. 100 The measure may have
    infinite total mass and need not be countably measurable on X. *)
Example zero_daniell_radon_nikodym_example (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  exists k : X -> R, is_lp_functional_density mu +oo 1 (fun _ => 0%R) k /\
    forall l, is_lp_functional_density mu +oo 1 (fun _ => 0%R) l ->
      measure_almost_everywhere mu [set x | k x=l x].
Proof.
have hA : is_daniell_integral (total_scalar_lp mu +oo) (fun _ => 0%R).
  constructor.
  - by move=> f g hf hg; rewrite add0r.
  - by move=> c f hc hf; rewrite mulr0.
  - move=> f hf; exists 0%R=> k hk; exact: lexx.
  - move=> f g hf hg hfg; exact: real_constant_order_limit.
have [k [hk [_ hu]]] := @radon_nikodym_daniell_representation R X mu hm (fun _ => 0%R)
  hA (fun _ _ _ => erefl).
exists k; by split.
Qed.

(** Regression examples for Federer (1969), 2.5.9, p. 100, with the
    positive-cone and total-domain corrections in the erratum, p. 2, book p.
    100 lines 21–24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric MeasureUP MeasureAlmostUP MeasureAlmostBasic
  CountablyMeasurableUP FunctionLatticeUP FunctionLatticeLaws FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP MonotoneDaniellIntegralLaws DaniellIntegralUP
  RealIntegralFunctionalUP RealScalarOrderLimits MeasurableTotalBasic
  SummableRealFunctionUP MeasureConullZeroIntegral TotalScalarLpUP
  LatticeDominatedDifference RealLatticeDensityUP DominatedLatticeRepresentation
  ScalarLipschitzExtensionUP ScalarLipschitzExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [zero_dominated_lattice_representation_example]:
    zero-functional regression for Federer 2.5.9, p. 100.
    The original lattice need not be a vector space, and its
    representing measure need not have finite total mass. *)
Example zero_dominated_lattice_representation_example (R : realType) (X : choiceType)
    (L : set (X -> R)) (hL : is_function_lattice L) (F : (X -> R) -> R)
    (mu : set X -> \bar R) (hm : is_measure mu) :
  is_monotone_daniell_integral L F -> is_real_integral_functional mu L F ->
  is_function_lattice_regular L mu -> measure_countably_measurable mu setT ->
  exists k : X -> R, is_real_lattice_density mu L (fun _ => 0%R) k /\
    total_scalar_lp mu +oo k /\ total_scalar_lp_norm mu +oo k <= 1 /\
    measure_almost_everywhere mu [set x | k x=0%R].
Proof.
move=> hF hrep hr hX.
have hA : is_daniell_integral L (fun _ => 0%R).
  constructor.
  - by move=> f g hf hg; rewrite add0r.
  - by move=> c f hc hf; rewrite mulr0.
  - move=> f hf; exists 0%R=> g hg; exact: lexx.
  - move=> f g hf hg hfg; exact: real_constant_order_limit.
have hb f : L f -> (`|(0%R : R)| <= F (fun x => `|f x|))%R.
  move=> hf; rewrite normr0.
  have h := @lattice_absolute_difference_member R X L hL f (fun _ => 0%R) hf (function_lattice_zero hL hf).
  have he : (fun x => `|f x-0%R|%R)=(fun x => `|f x|%R) by apply: funext=> x; rewrite subr0.
  rewrite he in h.
  exact: (@monotone_daniell_integral_nonnegative R X L F hL hF _ h (fun x => normr_ge0 (f x))).
have [k [hk [hkm [hkn hu]]]] := @dominated_lattice_integral_representation R X L hL F (fun _ => 0%R) mu hm hF hrep hr hX hA hb.
exists k; split=> //; split=> //; split=> //.
apply: hu; split.
- exact: (@measurable_total_constant R X
    [the topologicalType of real_norm_metric_space (scalar_absolute_value_norm R)] mu hm 0%R).
- move=> f hf; apply: (@measure_almost_zero_integral R X mu hm).
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  by apply/real_total_integrand_graph; rewrite mulr0.
Qed.

(** Source for [zero_distance_scalar_extension_example]: regression
    for the continuous extension used in Federer 2.5.9, p. 100.
    A zero pseudometric must identify distinct points; no separatedness
    or quotient construction may be imposed on the L1 distance. *)
Example zero_distance_scalar_extension_example (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (A : T -> R)
    (hd : is_pseudometric_on_set W d) (hDW : forall x, D x -> W x)
    (hD : exists y, D y) (hA : is_scalar_lipschitz_on_set D d A)
    (x y : T) :
  W x -> D y -> d x y=0%R ->
  @scalar_lipschitz_extension R T W D d A hd hDW hD hA x=A y.
Proof.
move=> hx hy hxy.
have [he hl] := @scalar_lipschitz_extension_specification R T W D d A hd hDW hD hA.
have hh := hl x y hx (hDW y hy).
rewrite hxy (he y hy) normr_le0 subr_eq0 in hh.
exact: (elimT eqP hh).
Qed.

(** Regression examples for the disjoint-decomposition assertion in Federer
    (1969), 2.5.10, pp. 100–101 Counting measure is Federer 2.1.2, p. 54
    These are local tests, not the geometric example printed later in
    2.5.10. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic CountingMeasure NonnegativeSumSupport
  FunctionLatticeSeminormUP FunctionOperatorSeminorm TotalScalarLpUP TotalScalarLpFiniteSeminorm
  RealLatticeDensityUP FiniteMeasureDecompositionUP FiniteDecompositionRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_singleton_decomposition_example]: regression
    of the condition in Federer 2.5.10, pp. 100–101, for
    counting measure on an arbitrary set, including uncountable sets. *)
Example counting_singleton_decomposition_example (R : realType) (X : choiceType) :
  is_finite_measure_decomposition (@counting_measure R X) setT (fun x => [set x]).
Proof.
split.
- move=> x _; split; first exact: counting_measure_measurable.
  rewrite counting_measure_sum nonnegative_sum_singleton; first exact: ltry.
  by rewrite lee_fin ler01.
- split.
  + move=> x y _ _ hxy; apply/seteqP; split=> [z [hzx hzy]|z []].
    apply: hxy; by rewrite -hzx -hzy.
  + move=> T hT; exists T; split; first by move=> x hx.
    split.
    * apply: finite_set_countable; apply: contrapT=> hn.
      by rewrite (counting_measure_infinite R hn) ltxx in hT.
    * have he : (\bigcup_(x in T) [set x])=T.
        apply/seteqP; split=> [y [x hx heq]|y hy].
        - by move: heq=> /= ->.
        - by exists y.
      by rewrite he setDv (measure_empty (counting_measure_is_measure R X)).
Qed.

(** Source for [counting_bounded_lone_representation_example]: regression of
    Federer 2.5.10's representation assertion, pp. 100–101 No countability
    of the counting-measure source is imposed. *)
Example counting_bounded_lone_representation_example (R : realType) (X : choiceType)
    (A : (X -> R) -> R) :
  is_linear_functional_on_functions (total_scalar_lp (@counting_measure R X) 1) A ->
  function_operator_seminorm (total_scalar_lp (@counting_measure R X) 1) A
    (finite_total_scalar_lp_norm (@counting_measure R X) 1) < +oo ->
  exists k : X -> R, is_real_lattice_density (@counting_measure R X)
    (total_scalar_lp (@counting_measure R X) 1) A k.
Proof.
move=> hA hb.
have [k [hk hn]] := @lone_functional_representation_by_finite_decomposition R X X
  (@counting_measure R X) (counting_measure_is_measure R X) setT (fun x => [set x]) A
  (counting_singleton_decomposition_example R X) hA hb.
by exists k.
Qed.

(** Source for [null_measure_empty_decomposition_example]: boundary
    regression for Federer 2.5.10, pp. 100–101. The decomposition
    may be empty when every finite test is null; its union need
    not equal a nonempty ambient space. *)
Example null_measure_empty_decomposition_example (R : realType) (X : choiceType) :
  is_finite_measure_decomposition (fun _ : set X => (0 : \bar R))
    (@set0 unit) (fun _ => @set0 X).
Proof.
split; first by move=> j [].
split; first by move=> i j [].
move=> T hT; exists set0; split; first by move=> j [].
split; first exact: countable0.
by [].
Qed.

(** Boundary regressions supporting Federer (1969), 2.5.10, p. 101. These
    verify the support and empty-piece conventions used by the Radon
    argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureSupport RadonCompactSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [empty_compact_restriction_support_example]: empty-remainder
    regression for the support construction in Federer 2.5.10, p. 101 No
    Radon hypothesis is needed for this boundary identity. *)
Example empty_compact_restriction_support_example (R : realType) (T : topologicalType)
    (mu : set T -> \bar R) (hm : is_measure mu) :
  measure_support (measure_restrict mu set0)=set0.
Proof.
have he : measure_restrict mu set0=(fun _ : set T => (0 : \bar R)).
  apply: funext=> A; by rewrite /measure_restrict set0I (measure_empty hm).
by rewrite he measure_support_zero.
Qed.

(** Source for [null_measure_positive_compact_piece_example]: zero-measure
    regression for the eligibility predicate in Federer 2.5.10, p. 101 The
    only eligible compact piece for the zero measure is empty. *)
Example null_measure_positive_compact_piece_example (R : realType) (T : topologicalType)
    (K : set T) :
  is_positive_compact_piece (fun _ : set T => (0 : \bar R)) K -> K=set0.
Proof.
move=> [_ h]; apply: contrapT=> hn.
have hne : K `&` setT <> set0 by rewrite setIT.
have hp := h setT openT hne; by rewrite ltxx in hp.
Qed.

(** Regressions for the predecessor subtraction in Federer (1969), 2.5.10,
    p. 101. These test overlapping, repeated sets and the first index. it
    does not state this example. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import CardinalSuccessorUP OrderedFamilyDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ordered_constant_family_first_piece_example]:
    first-index regression for Federer 2.5.10, p. 101.
    With no predecessors, the first piece is the whole original set. *)
Example ordered_constant_family_first_piece_example (X : choiceType) (A : set X) :
  ordered_family_piece setT leq (fun _ : nat => A) 0%N=A.
Proof.
apply/seteqP; split=> [x [hx _]|x hx] //; split=> //.
move=> [j [_ [hj hne]] _]; apply: hne; by move: hj; rewrite leqn0=> /eqP.
Qed.

(** Source for [ordered_constant_family_later_piece_example]:
    repeated-set regression for Federer 2.5.10, p. 101.
    The first set has already removed every point from the second piece. *)
Example ordered_constant_family_later_piece_example (X : choiceType) (A : set X) :
  ordered_family_piece setT leq (fun _ : nat => A) 1%N=set0.
Proof.
apply/seteqP; split=> [x [hx hn]|x []]; apply: hn; exists 0%N=> //.
Qed.

(** Boundary regressions for Federer (1969), 2.6.1, pp. 114–115 The examples
    test the printed zero-times-infinity convention and absence of
    finite-total-measure restrictions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_zero_infinite_rectangle_example]: regression of the
    explicit multiplication convention in Federer 2.6.1, p. 115 A measurable
    zero-by-infinite rectangle has zero product measure. *)
Example product_zero_infinite_rectangle_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B -> alpha A=0 -> beta B=+oo ->
  product_measure ha hb (A `*` B)=0.
Proof.
move=> hA hB hzero hinf; apply/eqP.
rewrite eq_le (measure_nonnegative (product_measure_is_measure ha hb)) andbT.
have hh := product_measure_rectangle_bound ha hb hA hB; by rewrite hzero hinf mul0e in hh.
Qed.

(** Source for [product_null_first_factor_example]: zero-factor
    regression for Federer 2.6.1, pp. 114–115. If the
    first factor's whole space is null, every product subset is
    null even when the other factor has infinite total measure. *)
Example product_null_first_factor_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (S : set (X * Y)) :
  alpha setT=0 -> product_measure ha hb S=0.
Proof.
move=> hz; apply/eqP; rewrite eq_le (measure_nonnegative (product_measure_is_measure ha hb)) andbT.
have hc : S `<=` (@setT X) `*` (@setT Y) by move=> x hx; split.
have h1 := @measure_mono R (X * Y)%type (product_measure ha hb) (product_measure_is_measure ha hb) _ _ hc.
have h2 := @product_measure_rectangle_bound R X Y alpha beta ha hb setT setT
  (measure_measurable_whole ha) (measure_measurable_whole hb).
rewrite hz mul0e in h2; exact: le_trans h1 h2.
Qed.

(** Source for [product_infinite_zero_rectangle_example]: regression of the
    other multiplication order in Federer 2.6.1, p. 115 Infinite
    first-factor measure times zero second-factor measure still gives a null
    measurable rectangle. *)
Example product_infinite_zero_rectangle_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B -> alpha A=+oo -> beta B=0 ->
  product_measure ha hb (A `*` B)=0.
Proof.
move=> hA hB hinf hzero; apply/eqP.
rewrite eq_le (measure_nonnegative (product_measure_is_measure ha hb)) andbT.
have hh := product_measure_rectangle_bound ha hb hA hB; by rewrite hinf hzero mule0 in hh.
Qed.

(** Null-strip regression for Federer (1969), 2.6.2, pp. 115–117 Every
    subset of a null first-coordinate cylinder is null and product
    measurable, without measurability of that subset or any finite
    total-measure assumption on the second factor. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit MeasureAlmostBasic MeasureFiniteClosure ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_arbitrary_null_strip_subset_example]: boundary
    regression for the completed product measure in Federer 2.6.2, pp.
    115–117 The subset here is arbitrary, so no measurability hypothesis is
    smuggled into null-set completeness. *)
Example product_arbitrary_null_strip_subset_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (S : set (X * Y)) :
  measure_measurable alpha A -> alpha A=0 -> S `<=` A `*` setT ->
  product_measure ha hb S=0 /\ measure_measurable (product_measure ha hb) S.
Proof.
move=> hA hzero hS.
have hmu := product_measure_is_measure ha hb.
have hn : product_measure ha hb (A `*` setT)=0.
  apply/eqP; rewrite eq_le (measure_nonnegative hmu) andbT.
  have hh := @product_measure_rectangle_bound R X Y alpha beta ha hb A setT hA (measure_measurable_whole hb).
  by rewrite hzero mul0e in hh.
have hz := @measure_null_subset R (X * Y)%type (product_measure ha hb) hmu _ _ hS hn.
split=> //; exact: (@measure_null_measurable R (X * Y)%type (product_measure ha hb) hmu S hz).
Qed.

(** Boundary regressions supporting Federer (1969), 2.6.2(2), p. 115: the
    rectangle-value formula includes finite and infinite counting factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import CountingMeasure FiniteCountingFunctionExamples ProductMeasure ProductRectangleValue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_counting_singleton_rectangle_example]:
    finite-factor regression for Federer 2.6.2(2), p. 115;
    counting measure is defined in 2.1.2, p. 54. A
    rectangle formed from two singletons has product measure one. *)
Example product_counting_singleton_rectangle_example (R : realType)
    (X Y : choiceType) (x : X) (y : Y) :
  product_measure (counting_measure_is_measure R X) (counting_measure_is_measure R Y)
    ([set x] `*` [set y]) = 1.
Proof.
rewrite (product_measure_rectangle_value _ _ (counting_measure_measurable R _) (counting_measure_measurable R _)).
by rewrite !counting_singleton_value mule1.
Qed.

(** Source for [product_counting_infinite_rectangle_example]:
    infinite-factor regression for Federer 2.6.2(2), p. 115;
    the product of counting measure on the natural numbers and
    a counting singleton has infinite measure, with no finite-
    total-measure assumption. *)
Example product_counting_infinite_rectangle_example (R : realType)
    (Y : choiceType) (y : Y) :
  product_measure (counting_measure_is_measure R [the choiceType of (nat : Type)])
    (counting_measure_is_measure R Y) (setT `*` [set y]) = +oo.
Proof.
rewrite (product_measure_rectangle_value _ _ (counting_measure_measurable R _) (counting_measure_measurable R _)).
by rewrite counting_singleton_value mule1 (counting_measure_infinite R infinite_nat).
Qed.


(** Regression for Federer (1969), 2.6.2(3), pp. 115, 117: counting measure
    has no nonempty null exceptional sets. This tests the null-section
    theorem with arbitrary, possibly infinite, first-factor counting
    measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP CountingMeasure
  FiniteCountingFunctionExamples ProductMeasure ProductSections ProductNullSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_null_counting_sections_pointwise_example]:
    regression strengthening the almost-everywhere conclusion of
    Federer 2.6.2(3), p. 115, for counting measure from
    2.1.2, p. 54. Every section of a product-null set
    is null when the outer factor is counting measure. This
    special-case consequence is not separately printed in the book. *)
Example product_null_counting_sections_pointwise_example (R : realType)
    (X Y : choiceType) (beta : set Y -> \bar R) (hb : is_measure beta)
    (S : set (X * Y)) :
  product_measure (counting_measure_is_measure R X) hb S = 0 ->
  forall x, beta (product_vertical_section S x) = 0.
Proof.
move=> hz x; have h := @product_null_vertical_sections R X Y
  (@counting_measure R X) beta (counting_measure_is_measure R X) hb S hz.
apply: contrapT=> hn.
have hs : [set x] `<=` ~` [set z | beta (product_vertical_section S z) = 0].
  by move=> z ->.
have hm := @measure_mono R X (@counting_measure R X) (counting_measure_is_measure R X) _ _ hs.
rewrite counting_singleton_value (h : counting_measure (~` [set z | beta (product_vertical_section S z) = 0]) = 0) in hm.
by move: hm; rewrite lee_fin leNgt ltr01.
Qed.


(** Regressions for Federer (1969), 2.6.2(3), pp. 115–117: repeated
    rectangles must not be counted repeatedly, and countably measurable sets
    may have infinite product measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  CountablyMeasurableUP CountablyMeasurableSequences MeasureIntegralUP CountingMeasure FiniteCountingFunctionExamples
  ProductMeasure ProductRectangleMeasurability ProductRectangleValue ProductSections
  CountableRectangleUnionUP CountableRectangleFubini ProductSetFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [repeated_rectangle_union_integral_example]:
    overlap regression for the disjoint decomposition in Federer
    2.6.2, p. 116. Repeating a measurable rectangle
    at every natural index leaves the repeated integral unchanged. *)
Example repeated_rectangle_union_integral_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (A : set X) (B : set Y) :
  measure_measurable alpha A -> measure_measurable beta B ->
  is_measure_integral alpha
    (partial_function_total (fun x => beta (product_vertical_section (\bigcup_(_ : nat) (A `*` B)) x))) (alpha A*beta B).
Proof.
move=> hA hB; pose S := \bigcup_(_ : nat) (A `*` B).
have hs : is_countable_rectangle_union alpha beta S.
  exists (fun _ => A), (fun _ => B); split=> // n; by split.
have he : S = A `*` B.
  apply/seteqP; split=> [z [n _ hz]|z hz] //; by exists 0%N.
have hv : product_measure ha hb S = alpha A*beta B.
  rewrite he; exact (@product_measure_rectangle_value R X Y alpha beta ha hb A B hA hB).
have hi := @countable_rectangle_union_vertical_integral R X Y alpha beta ha hb S hs.
by rewrite hv in hi.
Qed.

(** Source for [countably_measurable_infinite_product_integral_example]:
    infinite-measure regression for Federer 2.6.2(3), p. 115.
    Counting measure on the naturals times a counting singleton
    is a countably measurable infinite-measure set, and its actual
    outer section integral is infinity. *)
Example countably_measurable_infinite_product_integral_example (R : realType)
    (Y : choiceType) (y : Y) :
  is_measure_integral (@counting_measure R [the choiceType of (nat : Type)])
    (partial_function_total (fun n : nat => @counting_measure R Y
      (product_vertical_section (setT `*` [set y]) n))) +oo.
Proof.
pose ha := counting_measure_is_measure R [the choiceType of (nat : Type)].
pose hb := counting_measure_is_measure R Y.
pose S := (@setT nat) `*` [set y].
have hS : measure_countably_measurable (product_measure ha hb) S.
  apply: (countably_measurable_sequence_iff (product_measure_is_measure ha hb) S).2.
  exists (fun n : nat => [set n] `*` [set y]); split.
  - apply/seteqP; split=> [[n z] [_ hz]|[n z] [m _ [hn hz]]].
    + exists n=> //; by split.
    + by split.
  - move=> n; split.
    + exact (@product_measure_rectangle_measurable R [the choiceType of (nat : Type)] Y _ _ ha hb _ _
        (counting_measure_measurable R _) (counting_measure_measurable R _)).
    + rewrite (product_measure_rectangle_value ha hb (counting_measure_measurable R _) (counting_measure_measurable R _))
        !counting_singleton_value mule1; exact: ltry.
have hi := (@product_set_fubini R [the choiceType of (nat : Type)] Y _ _ ha hb S hS).2.2.1.
have hv : product_measure ha hb S = +oo.
  rewrite (product_measure_rectangle_value ha hb (counting_measure_measurable R _) (counting_measure_measurable R _))
    counting_singleton_value mule1; exact (@counting_measure_infinite R [the choiceType of (nat : Type)] setT infinite_nat).
by rewrite hv in hi.
Qed.


(** Boundary regressions for Federer (1969), 2.6.2(4), pp. 115, 117:
    arbitrary infinite factors with zero integrand, proper conull domains,
    and a negative integrand. p. 239 leaves its deduction as an exercise. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction MeasureUP MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureConullZeroIntegral MeasureStepConstants MeasureStepIntegralIdentification MeasureIntegralGraphEquivalence
  ProductMeasure ProductRectangleValue ProductRectangleMeasurability PartialProductSections ParameterizedIntegral ProductSummableFubini.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_zero_function_fubini_example]: zero-support
    regression for Federer 2.6.2(4), p. 115. Both
    factors may have arbitrary infinite mass; both actual iterated
    integrals of the total zero function are zero. *)
Example product_zero_function_fubini_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  let f := partial_function_total (fun _ : X * Y => (0 : extended_real_line R)) in
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) 0 /\
  is_measure_integral beta (parameterized_integral alpha (partial_product_horizontal_section f)) 0.
Proof.
move=> f; apply: (@product_summable_fubini R X Y alpha beta ha hb f 0%R).
apply: (@measure_almost_zero_integral R (X * Y)%type (product_measure ha hb) (product_measure_is_measure ha hb)).
apply: (@measure_almost_everywhere_mono R (X * Y)%type (product_measure ha hb)
  (product_measure_is_measure ha hb) setT _ _ (measure_almost_everywhere_true (product_measure_is_measure ha hb)))=> p _; by [].
Qed.

(** Source for [product_partial_zero_fubini_example]: exact-domain
    regression for Federer 2.6.2(4), p. 115, using
    the conull-domain convention of 2.4.2, p. 81.
    The zero function is undefined off the chosen conull set D;
    both iterated integrals still exist and equal zero. *)
Example product_partial_zero_fubini_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (D : set (X * Y)) :
  measure_almost_everywhere (product_measure ha hb) D ->
  let f := partial_function_source_restrict D (partial_function_total (fun _ : X * Y => (0 : extended_real_line R))) in
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) 0 /\
  is_measure_integral beta (parameterized_integral alpha (partial_product_horizontal_section f)) 0.
Proof.
move=> hD f; apply: (@product_summable_fubini R X Y alpha beta ha hb f 0%R).
apply: (@measure_almost_zero_integral R (X * Y)%type (product_measure ha hb) (product_measure_is_measure ha hb)).
apply: (@measure_almost_everywhere_mono R (X * Y)%type (product_measure ha hb)
  (product_measure_is_measure ha hb) _ _ _ hD)=> p hp; by split.
Qed.

(** Source for [product_negative_constant_fubini_example]: signed
    regression for the part reduction in Federer 2.6.2(4),
    p. 117. With both factors of total mass one, the
    constant negative-one integrand has both iterated integrals -1. *)
Example product_negative_constant_fubini_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  alpha setT = 1 -> beta setT = 1 ->
  let f := partial_function_total (fun _ : X * Y => ((-1)%R)%:E : extended_real_line R) in
  is_measure_integral alpha (parameterized_integral beta (partial_product_vertical_section f)) (-1)%:E /\
  is_measure_integral beta (parameterized_integral alpha (partial_product_horizontal_section f)) (-1)%:E.
Proof.
move=> hA hB f; apply: (@product_summable_fubini R X Y alpha beta ha hb f (-1)%R).
pose nu := product_measure ha hb; have hnu := product_measure_is_measure ha hb.
have hwhole : nu setT = 1.
  have he : (@setT (X * Y)) = setT `*` setT by apply/seteqP; split=> p _; by [].
  rewrite /nu he (product_measure_rectangle_value ha hb (measure_measurable_whole ha) (measure_measurable_whole hb)) hA hB mule1; by [].
have hs := @measure_step_constant_integral R (X * Y)%type nu hnu (-1)%R.
rewrite hwhole mule1 in hs.
have hi := @measure_step_function_integral R (X * Y)%type nu hnu _ (-1)%:E
  (@measure_step_constant R (X * Y)%type nu hnu (-1)%R) hs.
apply: (@measure_integral_graph_equivalent R (X * Y)%type nu _ f (-1)%:E _ hi)=> p z.
split; first by move=> [r [<- <-]].
move=> <-; exists (-1)%R; by split.
Qed.

(** Boundary regressions for Federer (1969), 2.5.13, pp. 106–107: empty
    compact sets, the zero functional, and a negative point-evaluation
    functional. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import FunctionLatticeUP DaniellIntegralUP FunctionLatticeSeminormUP MeasureUP MeasureIntegralUP
  SummableRealFunctionUP FunctionLatticeRegularityUP CompactSupportFunctionUP CompactSupportFunctionLattice
  CompactCutoffUP CompactSupportRieszRepresentation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_compact_cutoff_example]: empty-set
    regression for the cutoff used in Federer 2.5.13,
    p. 106. The zero function supplies the laws directly. *)
Example empty_compact_cutoff_example (R : realType) (X : topologicalType) :
  is_compact_cutoff set0 (fun _ : X => (0 : R)).
Proof.
constructor; first exact: compactly_supported_zero_function.
- move=> x; by rewrite lexx ler01.
- by move=> x [].
Qed.

(** Source for [negative_evaluation_daniell_example]: signed
    functional regression for Federer 2.5.13, pp. 106–107.
    Negative point evaluation is order bounded and Daniell; no
    positivity of the given functional is required. *)
Example negative_evaluation_daniell_example (R : realType) (X : topologicalType) (x : X) :
  hausdorff_space X -> locally_compact (@setT X) ->
  is_daniell_integral (@compactly_supported_continuous_functions R X) (fun f => -f x).
Proof.
move=> hh hl; apply: compact_support_order_bounded_daniell hh hl _ _.
- split.
  + by move=> f g hf hg; rewrite opprD.
  + by move=> c f hf; rewrite mulrN.
- move=> u hu; exists 0=> k [hk [hk0 hku]]; by rewrite oppr_le0; exact: hk0.
Qed.

(** Source for [zero_compact_support_riesz_example]: zero-functional
    and unrestricted ambient-space regression for the representation
    in Federer 2.5.13, p. 106. Both representing measures
    exist with the actual finite integral-difference conclusion. *)
Example zero_compact_support_riesz_example (R : realType) (X : topologicalType) :
  hausdorff_space X -> locally_compact (@setT X) ->
  exists mu nu : set X -> \bar R,
    is_measure mu /\ is_measure nu /\
    is_function_lattice_regular (@compactly_supported_continuous_functions R X) mu /\
    is_function_lattice_regular (@compactly_supported_continuous_functions R X) nu /\
    forall f, compactly_supported_continuous_functions f -> exists a b : R,
      is_measure_integral mu (real_total_integrand f) a%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E /\ 0=a-b.
Proof.
move=> hh hl; apply: (@compact_support_riesz_representation R X (fun _ => 0) hh hl).
- split; [by move=> f g hf hg; rewrite add0r|by move=> c f hf; rewrite mulr0].
- move=> u hu; exists 0=> k hk; exact: lexx.
Qed.

(** Boundary regressions for the scalar parts of Federer (1969), 2.5.14, pp.
    107–108: empty finite covers, empty open test sets, and the zero
    functional's Radon representation. These examples do not claim the later
    modification of 2.5.12 is already formalised. *)
From mathcomp Require Import all_boot all_order all_algebra finmap classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactSupportFunctionLattice FiniteCompactPartitionUP
  CompactOpenContentUP CompactOpenContentBasic CompactSupportRadonRepresentation
  MonotoneDaniellIntegralUP ExtendedRealOrderLimit MeasureUP RadonMeasureUP RealIntegralFunctionalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_compact_partition_example]: the empty
    support and empty-cover case of the partition used in Federer
    2.5.14, p. 108. The sum condition is vacuous
    on the empty compact set, rather than falsely asserted globally. *)
Example empty_compact_partition_example (R : realType) (X : topologicalType)
    (J : choiceType) (V : J -> set X) :
  is_finite_compact_partition V fset0 set0 (fun _ _ => (0 : R)).
Proof.
constructor; try by move=> j; rewrite in_fset0.
by move=> x [].
Qed.

(** Source for [empty_open_content_example]: alpha(empty)=0 boundary case in
    Federer 2.5.14, p. 108 *)
Example empty_open_content_example (R : realType) (X : topologicalType)
    (A : (X -> R) -> R) (a : set X -> \bar R) :
  is_monotone_daniell_integral (@compactly_supported_continuous_functions R X) A ->
  is_compact_open_content A a -> a set0=0%E.
Proof. move=> hA ha; exact: compact_open_content_empty hA ha. Qed.

(** Source for [zero_compact_support_radon_example]: the zero functional has
    a Radon representing measure on every locally compact Hausdorff space in
    Federer 2.5.14, p. 107 No point of X, countable base, or positive total
    mass is assumed. *)
Example zero_compact_support_radon_example (R : realType) (X : topologicalType) :
  hausdorff_space X -> locally_compact (@setT X) ->
  exists nu : set X -> \bar R, is_measure nu /\ is_radon_measure nu /\
    is_real_integral_functional nu (@compactly_supported_continuous_functions R X) (fun _ => 0).
Proof.
move=> hh hl; apply: (@compact_support_radon_representation R X (fun _ => 0) hh hl).
constructor.
- by move=> f g hf hg; rewrite add0r.
- by move=> c f hc hf; rewrite mulr0.
- by move=> f g hf hg hfg.
- move=> f g hf hg hfg; split; first by move=> n m hnm.
  split=> c hc; exists 0%N=> n _; exact hc.
Qed.

(** Boundary regressions for Federer (1969), 2.5.11, p. 102, 2.5.15, pp.
    108–109, and 2.5.16, p. 109: the two-valued cardinal measures beta_j,
    the unit point mass behind the evaluation functional, and the variation
    of the identity curve. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CardinalMeasureUP CardinalMeasureLaws
  PointMassMeasure CurveVariationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cardinal_measure_singleton_example]: regression of the
    first clause of beta_1 in Federer 2.5.11, p. 102: a singleton is
    countable, so beta_1 vanishes on it. *)
Example cardinal_measure_singleton_example (R : realType) (K : choiceType) (u : K) :
  cardinal_measure R (@setT nat) [set u] = 0.
Proof. exact (cardinal_measure_small R (countable1 u)). Qed.

(** Source for [cardinal_measure_uncountable_example]: regression of the
    second clause of beta_1 in Federer 2.5.11, p. 102: an uncountable
    carrier has measure one. *)
Example cardinal_measure_uncountable_example (R : realType) (K : choiceType) :
  ~ countable (@setT K) -> cardinal_measure R (@setT nat) (@setT K) = 1.
Proof. move=> hK; exact (cardinal_measure_whole R hK). Qed.

(** Source for [point_mass_singleton_example]: regression of the value
    phi({xi})=1 in Federer 2.5.15, p. 108, for the unit point mass. *)
Example point_mass_singleton_example (R : realType) (X : Type) (x : X) :
  point_mass R x [set x] = 1.
Proof. exact (point_mass_in R (S := [set x]) erefl). Qed.

(** Source for [point_mass_empty_example]: regression of the value zero of
    the unit point mass on the empty set, Federer 2.5.15, p. 108. *)
Example point_mass_empty_example (R : realType) (X : Type) (x : X) :
  point_mass R x set0 = 0.
Proof. by rewrite point_mass_out. Qed.

(** Source for [identity_variation_lower_example]: regression of the
    distance bound for the variation in Federer 2.5.16, p. 109: the
    identity curve of the real line has variation at least one on [0,1]. *)
Example identity_variation_lower_example (R : realType) :
  1 <= curve_variation (fun x : R => (x : real_line_metric R)) 0 1.
Proof.
have := curve_variation_ge_distance (fun x : R => (x : real_line_metric R)) (@ler01 R).
by rewrite real_line_metric_distanceE /= sub0r normrN normr1.
Qed.

(** Source for [variation_self_example]: regression of V_a^a g=0 in
    Federer 2.5.16, p. 109, for the identity curve. *)
Example variation_self_example (R : realType) :
  curve_variation (fun x : R => (x : real_line_metric R)) 1 1 = 0.
Proof. exact: curve_variation_self. Qed.

(** Boundary regressions for Federer (1969), 2.5.17, pp. 110–111: a
    degenerate Riemann–Stieltjes sum and the vanishing of the interval bumps
    at an end point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import StieltjesSums IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_sum_degenerate_example]: regression of a sum
    over a sequence with a single degenerate cell, Federer 2.5.17,
    p. 110. *)
Example stieltjes_sum_degenerate_example (R : realType) (f g : R -> R) (a : R) :
  stieltjes_sum f g [:: a; a; a] = 0.
Proof. by rewrite /= subrr mulr0 addr0. Qed.

(** Source for [interval_bump_endpoint_example]: regression of the
    vanishing of the bumps at the left end point, Federer 2.5.17,
    p. 111. *)
Example interval_bump_endpoint_example (R : realType) (a b : R) (n : nat) :
  interval_bump a b n a = 0.
Proof. by apply: interval_bump_zero; rewrite ltxx. Qed.

(** Boundary regression for Federer (1969), 2.5.17, p. 111: the variation of
    the identity on [0, 1] equals one *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import RealMetricBackground StieltjesIntegral StieltjesMonotone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [identity_total_variation_example]: regression of
    V_0^1 g = g(1) - g(0) for the nondecreasing identity, Federer 2.5.17,
    p. 111. *)
Example identity_total_variation_example (R : realType) :
  total_variation (fun x : R => x) 0 1 = 1.
Proof. by rewrite (monotone_total_variation (g := fun x : R => x) (fun x y h => h) ler01) subr0. Qed.

(** Regression for Federer (1969), 2.5.18(1), p. 112. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground StieltjesIntegral StieltjesMonotone
  StieltjesIntegrationByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [parts_identity_example]: regression of
    int_0^1 x dx = 1/2 from Federer 2.5.18(1), p. 112. *)
Example parts_identity_example (R : realType) :
  stieltjes_integral (fun x : R => x) (fun x : R => x) 0 1 = 1 / 2.
Proof.
have hfin := monotone_locally_finite_variation (g := fun x : R => x) (fun x y h => h).
have hcont : continuous (fun x : R => x) by move=> x; exact: cvg_id.
have := stieltjes_integration_by_parts hfin hfin hcont hcont ler01.
by rewrite mulr1 mulr0 subr0 => h; lra.
Qed.

(** Boundary regressions for Federer 2.5.12, pp. 102–106. *)
From Federer Require Import VectorDaniellHypotheses VectorDaniellNormalisationUP
  VectorDaniellDualExtension PartialDualPairing.

(** Source for [dual_pairing_empty_domain_example]: regression
    of the partial-function convention in Federer 2.5.12,
    p. 103, using 2.3.2, p. 73. Pairing does not
    supply values outside the original domain. *)
Example dual_pairing_empty_domain_example (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (k : X -> weak_dual_space hN) :
  partial_function_domain (partial_dual_pairing k (@partial_function_empty X E)) = set0.
Proof.
apply/seteqP; split; last by move=> x [].
move=> x [z /partial_dual_pairing_graph [y [hy _]]]; exact: hy.
Qed.

(** Source for [dual_pairing_zero_vector_example]: the pairing
    in Federer 2.5.12, p. 103, vanishes at the zero
    vector, including a zero-dimensional target. *)
Example dual_pairing_zero_vector_example (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (k : X -> weak_dual_space hN) x :
  partial_function_graph
    (partial_dual_pairing k (partial_function_total (fun _ : X => (0 : E)))) x 0%:E.
Proof.
apply/partial_dual_pairing_graph; exists 0; split=> //.
by rewrite (@dual_space_zero R E N hN (val (k x)) (set_valP (k x))).
Qed.

(** Source for [zero_dimensional_variation_measure_example]:
    regression of the unit-norm conclusion in Federer 2.5.12,
    p. 103, when E is zero-dimensional. Its dual unit
    sphere is empty and the chosen dual norm is zero; thus
    the almost-everywhere norm-one assertion forces phi(X)=0,
    rather than requiring a nonzero vector in E. *)
Example zero_dimensional_variation_measure_example (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (Q : set (X -> E)) (T : (X -> E) -> R)
    (k : X -> weak_dual_space hN) :
  (forall y : E, y=0) ->
  is_normalised_vector_daniell_density phi Q T k -> phi setT = 0%E.
Proof.
move=> hzero hk.
have hnorm alpha : dual_norm N alpha=0.
  have hs : [set alpha y | y in [set y | N y = 1]] = set0.
    apply/seteqP; split; last by move=> z [].
    move=> z [y hy _].
    have hy' : N y = 1 := hy.
    have hh : (0 : R) = 1 by move: hy'; rewrite (hzero y) (real_seminorm_zero hN.1).
    by move: hh; move/eqP; rewrite eq_sym oner_eq0.
  by rewrite /dual_norm hs sup0.
have hi := normalised_vector_density_unit_norm hk.
have hempty : [set x | dual_norm N (val (k x)) = 1] = set0.
  apply/seteqP; split; last by move=> x [].
  move=> x hx; have hh : dual_norm N (val (k x)) = 1 := hx.
  move: hh; rewrite hnorm; move/eqP; by rewrite eq_sym oner_eq0.
by move: hi; rewrite /measure_almost_everywhere hempty setC0.
Qed.

(** Regression examples for Federer (1969), 2.6.7, p. 121: empty intervals
    and atoms at either endpoint. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureIntegralUP SummableRealFunctionUP
  LatticeL1ApproximationLaws CumulativeIntegrationByParts PointMassMeasure PointMassIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cumulative_empty_interval_example]: regression
    of the degenerate-interval extension of Federer 2.6.7,
    p. 121. Both printed half-open intervals are empty. *)
Example cumulative_empty_interval_example (R : realType)
    (mu : set R -> \bar R) (hm : is_measure mu) (a : R) (f : R -> R) :
  is_measure_integral mu (real_total_integrand (left_half_open_integrand a a f)) 0%:E /\
  is_measure_integral mu (real_total_integrand (right_half_open_integrand a a f)) 0%:E.
Proof.
have hL : left_half_open_integrand a a f=(fun _ : R => 0).
  by apply: funext=> x; rewrite /left_half_open_integrand ltNge andbN.
have hR : right_half_open_integrand a a f=(fun _ : R => 0).
  by apply: funext=> x; rewrite /right_half_open_integrand ltNge andNb.
rewrite hL hR; split; exact: real_total_zero_integral hm.
Qed.

(** Source for [cumulative_left_endpoint_atom_example]: in
    Federer 2.6.7, p. 121, a common unit atom at a=0
    contributes zero to the first integral over (0,1] and
    one to the second over [0,1). This checks the opposite
    strictness of both cumulative functions and both intervals. *)
Example cumulative_left_endpoint_atom_example (R : realType) :
  is_measure_integral (point_mass R (0 : R))
    (real_total_integrand (right_half_open_integrand 0 1 (fun r : R => if 0 < r then 1 else 0))) 0%:E /\
  is_measure_integral (point_mass R (0 : R))
    (real_total_integrand (left_half_open_integrand 0 1 (fun r : R => if 0 <= r then 1 else 0))) 1%:E.
Proof.
split.
- have hi := point_mass_real_integral (0 : R)
    (right_half_open_integrand 0 1 (fun r : R => if 0 < r then 1 else 0)).
  by rewrite /right_half_open_integrand ltxx in hi.
- have hi := point_mass_real_integral (0 : R)
    (left_half_open_integrand 0 1 (fun r : R => if 0 <= r then 1 else 0)).
  by rewrite /left_half_open_integrand lexx ltr01 in hi.
Qed.

(** Source for [cumulative_right_endpoint_atom_example]: in
    Federer 2.6.7, p. 121, a common unit atom at b=1
    contributes zero to both integrals on [0,1]. In the
    first term f(1)=0; in the second, 1 is excluded. *)
Example cumulative_right_endpoint_atom_example (R : realType) :
  is_measure_integral (point_mass R (1 : R))
    (real_total_integrand (right_half_open_integrand 0 1 (fun r : R => if 1 < r then 1 else 0))) 0%:E /\
  is_measure_integral (point_mass R (1 : R))
    (real_total_integrand (left_half_open_integrand 0 1 (fun r : R => if 1 <= r then 1 else 0))) 0%:E.
Proof.
split.
- have hi := point_mass_real_integral (1 : R)
    (right_half_open_integrand 0 1 (fun r : R => if 1 < r then 1 else 0)).
  by rewrite /right_half_open_integrand lexx ltr01 ltxx in hi.
- have hi := point_mass_real_integral (1 : R)
    (left_half_open_integrand 0 1 (fun r : R => if 1 <= r then 1 else 0)).
  by rewrite /left_half_open_integrand ler01 ltxx in hi.
Qed.

(** Regression examples for Federer (1969), 2.6.5, pp. 119–120. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward ProductMeasure PointMassMeasure PointMassRegularity
  InfiniteDiscreteMeasure ProductAssociativityObstruction ProductMeasureAssociativity
  LebesgueScalarMeasure LebesgueAssociativityCounterexample FiniteCoordinates GrassmannAbbreviations
  PolynomialFunctions EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBlockCoordinates EuclideanBlockMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_dimensional_polynomial_null_example]:
    regression of the explicit zero-dimensional extension of
    the polynomial-nullity assertion in Federer 2.6.5,
    p. 120. Nonzero at the sole vector means no zeros. *)
Example zero_dimensional_polynomial_null_example (R : realType)
    (P : PolynomialFunction (R_n R 0) R^o) :
  P 0 <> 0 -> euclidean_lebesgue_measure 0 [set x | P x = 0] = 0%:E.
Proof. move=> hp; apply: euclidean_polynomial_zero_set_null; by exists 0. Qed.

(** Source for [empty_euclidean_block_example]: regression
    of the empty-product convention extending Federer 2.6.5,
    p. 120. The product of two zero-dimensional unit
    masses is the image of the zero-dimensional measure. *)
Example empty_euclidean_block_example (R : realType) :
  measure_pushforward (@euclidean_block_split R 0 0) (@euclidean_lebesgue_measure R 0) =
    product_measure (euclidean_lebesgue_is_measure R 0) (euclidean_lebesgue_is_measure R 0).
Proof. exact: euclidean_block_measure. Qed.

(** Source for [infinite_middle_factor_association_example]: Supporting
    Federer 2.6.5, p. 119.Only the outer factors need countable
    measurability: the middle factor is infinite on every nonempty subset,
    even though its carrier is a singleton. *)
Example infinite_middle_factor_association_example (R : realType) :
  measure_pushforward (@product_associate unit unit unit)
    (product_measure (product_measure_is_measure (point_mass_is_measure R tt)
      (infinite_discrete_measure_is_measure R (Choice.clone unit _))) (point_mass_is_measure R tt)) =
  product_measure (point_mass_is_measure R tt)
    (product_measure_is_measure (infinite_discrete_measure_is_measure R (Choice.clone unit _))
      (point_mass_is_measure R tt)).
Proof.
apply: product_measure_associative_outer_countable; exact: point_mass_countably_measurable.
Qed.

(** Source for [lebesgue_association_zero_infinity_example]: Supporting
    Federer 2.6.5, p. 119.For the diagonal over [0,1] and an infinite unit
    factor, the two associations give zero and infinity. The actual sealed
    Lebesgue measure is used, with diagonal nullity proved by Fubini. *)
Example lebesgue_association_zero_infinity_example (R : realType) :
  product_measure (product_measure_is_measure (lebesgue_scalar_is_measure R) (lebesgue_scalar_is_measure R))
    (infinite_discrete_measure_is_measure R (Choice.clone unit _))
    (restricted_diagonal [set x : R | 0 <= x /\ x <= 1] `*` @setT unit) = 0%E /\
  product_measure (lebesgue_scalar_is_measure R)
    (product_measure_is_measure (lebesgue_scalar_is_measure R) (infinite_discrete_measure_is_measure R (Choice.clone unit _)))
    (@right_associated_diagonal R unit [set x : R | 0 <= x /\ x <= 1]) = +oo%E.
Proof.
have hD := @lebesgue_bounded_diagonal_null R (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) (@lebesgue_scalar_segment R) 0 1 ler01.
split; first exact: left_associated_null_diagonal hD.
apply: (@right_associated_diagonal_infinite R R (Choice.clone unit _)
  (@lebesgue_scalar_measure R) (@infinite_discrete_measure R unit)
  (lebesgue_scalar_is_measure R) (infinite_discrete_measure_is_measure R (Choice.clone unit _))
  (@infinite_discrete_measure_nonempty R unit) tt).
have he : [set x : R | 0 <= x /\ x <= 1] = `[0,1].
  apply/seteqP; split=> x; rewrite /= in_itv /=.
  - by move=> [h0 h1]; rewrite h0 h1.
  - by move=> /andP.
by rewrite he lebesgue_scalar_segment ?ler01 // subr0 lte_fin ltr01.
Qed.

From Federer Require Import CountablyMeasurableUP CountablyMeasurableSequences.
(** Source for [infinite_singleton_not_countably_measurable_example]:
    Supporting Federer 2.6.5, p. 119.An infinite unit factor cannot admit a
    countable cover by finite-measure sets. *)
Example infinite_singleton_not_countably_measurable_example (R : realType) :
  ~ measure_countably_measurable (@infinite_discrete_measure R unit) setT.
Proof.
move=> h.
have [F [hF hFm]] := (proj1 (countably_measurable_sequence_iff
  (infinite_discrete_measure_is_measure R (Choice.clone unit _)) setT)) h.
have hcover : (\bigcup_n F n) tt by rewrite -hF.
have [n _ hn] := hcover.
have hi : infinite_discrete_measure R (F n) = +oo%E.
  apply: infinite_discrete_measure_nonempty; by exists tt.
by move: (hFm n).2; rewrite hi ltxx.
Qed.

From Federer Require Import RationalLebesgueIntegrals RationalIteratedIntegrals
  RationalFubiniKernel RationalRectangleIntegral RationalFubiniCounterexample.
(** Source for [rational_zero_axis_integral_example]: regression
    of the zero convention on the coordinate axes in Federer
    2.6.3(2), p. 117. The entire y=0 section has integral zero. *)
Example rational_zero_axis_integral_example (R : realType) :
  is_measure_integral (@lebesgue_scalar_measure R)
    (real_total_integrand (fun x => rational_fubini_kernel x (0 : R))) 0%E.
Proof. exact: rational_section_integral_zero. Qed.

(** Source for [rational_unit_segment_integral_example]: regression
    of the first primitive evaluation in Federer 2.6.3(2),
    p. 117, at a=y=1. The integral is zero although the
    kernel changes sign on the interval. *)
Example rational_unit_segment_integral_example (R : realType) :
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,1]
    (real_total_integrand (fun x => rational_fubini_kernel x (1 : R))) 0%E.
Proof.
have hi := @rational_first_lebesgue_integral R 1 1 ltr01 ltr01.
by rewrite /rational_first_primitive expr1n mulr1 subrr mul0r in hi.
Qed.

(** Source for [rational_square_primitive_integral_example]: regression
    of the scale-independent rectangle value in Federer
    2.6.3(2), p. 118, at m=1 and every a>0.
    This actual one-dimensional integral gives the nonzero
    value used in the contradiction, without assuming product integrability. *)
Example rational_square_primitive_integral_example (R : realType) (a : R) :
  0 < a -> is_measure_subset_integral (@lebesgue_scalar_measure R) `[0,a]
    (real_total_integrand (fun y => rational_first_primitive y a))
    ((1 : R)/(1+1)^+2)%:E.
Proof.
move=> ha; have hi := @rational_second_scaled_lebesgue_integral R a 1 ha ltr01.
by rewrite mul1r in hi.
Qed.

Local Close Scope ereal_scope.
Local Open Scope ring_scope.

From Federer Require Import TensorProduct SummableRealSpace SummableRealIntegralMap SummableTensorMap
  SummableTensorIntegral SummableTensorSeminormDensity DaniellProduct CompactProductSections
  TotalScalarLpUP CompactSupportFunctionUP DaniellIntegralUP DaniellIntegralAlgebra CompactSupportFunctionLattice.
(** Source for [summable_tensor_empty_factor_example]: empty-factor
    regression for the monomorphism in Federer 2.6.4,
    p. 118. The total-function space on an empty domain
    is zero, and hence so is its tensor product with any other factor. *)
Example summable_tensor_empty_factor_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  (forall x : X, False) -> forall t : tensor_space (summable_real_space ha) (summable_real_space hb), t=0.
Proof.
move=> hX t; apply: (@summable_tensor_map_injective R X Y alpha beta ha hb t 0).
apply: summable_real_value_injective; apply: funext=> p; case: p=> x y; case: (hX x).
Qed.

(** Source for [summable_null_function_tensor_not_quotiented_example]:
    regression of the total-domain convention in Federer 2.6.4,
    p. 119, erratum p. 2 lines 3, 4, 6. A
    zero-seminorm, zero-integral function with nonzero point value is retained by
    the tensor embedding, even though the product integral is zero. *)
Example summable_null_function_tensor_not_quotiented_example (R : realType) (X Y : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (f : summable_real_space ha) (g : summable_real_space hb) (x : X) (y : Y) :
  total_scalar_lp_norm alpha 1 (summable_real_value f)=0%E ->
  summable_real_value f x = 1 -> summable_real_value g y = 1 -> summable_real_integral_map f=0 ->
  summable_real_value (summable_tensor_map ha hb (tensor_inj f g)) (x,y) = 1 /\
  summable_real_integral_map (summable_tensor_map ha hb (tensor_inj f g))=0.
Proof.
move=> _ hf hg hi; rewrite summable_tensor_map_generator; split.
- by rewrite summable_product_pairE /= hf hg mulr1.
- by rewrite summable_product_integral_value hi mul0r.
Qed.

(** Source for [daniell_product_zero_left_example]: zero-functional
    regression for the last diagram of Federer 2.6.4,
    p. 119. The other Daniell functional may be signed. *)
Example daniell_product_zero_left_example (R : realType) (X Y : topologicalType)
    (A : (X -> R) -> R) (B : (Y -> R) -> R)
    (hX : hausdorff_space X) (hlX : locally_compact (@setT X))
    (hY : hausdorff_space Y) (hlY : locally_compact (@setT Y))
    (hA : is_daniell_integral (@compactly_supported_continuous_functions R X) A)
    (hB : is_daniell_integral (@compactly_supported_continuous_functions R Y) B)
    (h : (X*Y) -> R) :
  (forall f, compactly_supported_continuous_functions f -> A f=0) ->
  compactly_supported_continuous_functions h ->
  @daniell_product R X Y A B hX hlX hY hlY hA hB h=0.
Proof.
move=> hAz hh; rewrite (@daniell_product_iterated_value R X Y A B hX hlX hY hlY hA hB h hh).
have hz : (fun y => A (fun x => h (x,y)))=(fun _ => (0 : R)).
  apply: funext=> y; exact: hAz _ (@compact_product_first_section R X Y h y hX hh).
rewrite hz; exact (@daniell_integral_zero R Y _ B hB _ (@compactly_supported_zero_function R Y)).
Qed.

(** Federer 2.6.6, pp. 120–121: regression examples for empty coordinates
    and a non-surjective compact inverse system. Source context are recorded
    in CompactProductFiniteControl.v. *)
From mathcomp Require Import bool_topology.
From Federer Require Import InfiniteDaniellProduct InfiniteDaniellProductUP FiniteCoordinateProduct
  FiniteCoordinateProductUP ConsistentCylinderFunctionalUP ProductCylinderLattice
  CompactInverseSystemUP CompactInverseLimitUP InverseDaniellFamilyUP InverseDaniellIntegral
  DaniellSpaceWeakTopology.

(** Source for [infinite_product_empty_coordinates_regression]:
    the empty-coordinate boundary of Federer 2.6.6, p. 120.
    A constant cylinder has its literal value as its integral. *)
Example infinite_product_empty_coordinates_regression (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
    (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
    (hA1 : forall i, A i (fun _=>1) = 1) (x0 : prod_topology Y) (f : prod_topology Y -> R) :
  continuous_coordinate_functions fset0 f ->
  @infinite_daniell_product R I Y A hh hc hA hA1 f=f x0.
Proof.
move=> hf; have hb := @infinite_daniell_product_specification R I Y A hh hc hA hA1.
rewrite (hb.2.2 fset0 f hf).
exact: (@finite_coordinate_product_empty R I Y A _
  (@finite_coordinate_product_specification R I Y A hh hc hA hA1) f hf x0).
Qed.

(** Source for [two_stage_bonding]: regression construction for
    the inverse-limit paragraph of Federer 2.6.6, pp. 120–121.
    The map from stage true to stage false is constant false;
    the two identity maps remain identities. *)
Definition two_stage_bonding (i j : bool) (x : bool) := if i then x else if j then false else x.

(** Source for [two_stage_projection]: regression projections
    for the non-surjective system supporting Federer 2.6.6,
    pp. 120–121. The limit is its upper stage. *)
Definition two_stage_projection (i : bool) (x : bool) := if i then x else false.

(** Source for [two_stage_inverse_system]: the finite compact
    Hausdorff inverse-system laws for the regression example
    supporting Federer 2.6.6, pp. 120–121. *)
Lemma two_stage_inverse_system :
  @is_compact_inverse_system [the choiceType of (bool : Type)] (fun i j=>i ==> j)
    (fun _=>[the topologicalType of (bool : Type)]) two_stage_bonding.
Proof.
constructor.
- constructor.
  + by exists false.
  + by case.
  + by case=> [] [] [].
  + move=> i j; by exists true; case: i; case: j.
- move=> i; exact: bool_compact.
- move=> i; exact: discrete_hausdorff.
- move=> i j hij x U hU; rewrite nbhs_principalE; apply/principal_filterP.
  exact (@topology_structure.nbhs_singleton [the topologicalType of (bool : Type)] _ _ hU).
- by case=> x.
- by move=> [] [] [] // _ _ x.
Qed.

(** Source for [two_stage_inverse_limit]: the actual limit
    satisfies realization and point-separation laws, a regression
    for Federer 2.6.6, pp. 120–121. *)
Lemma two_stage_inverse_limit :
  @is_compact_inverse_limit [the choiceType of (bool : Type)] (fun i j=>i ==> j)
    (fun _=>[the topologicalType of (bool : Type)]) two_stage_bonding
    [the topologicalType of (bool : Type)] two_stage_projection.
Proof.
constructor.
- exact: bool_compact.
- exact: discrete_hausdorff.
- move=> i x U hU; rewrite nbhs_principalE; apply/principal_filterP.
  exact (@topology_structure.nbhs_singleton [the topologicalType of (bool : Type)] _ _ hU).
- by move=> x [] [] //.
- move=> u hu; exists (u true).
  move=> i; case: i=> //.
  exact: (hu false true erefl).
- by move=> x y h; exact: h true.
Qed.

(** Source for [two_stage_bonding_not_surjective_regression]:
    this inverse-system regression for Federer 2.6.6,
    pp. 120–121, genuinely has a non-surjective bonding map. *)
Example two_stage_bonding_not_surjective_regression :
  ~ exists x, two_stage_bonding false true x=true.
Proof. by move=> [x]. Qed.

(** Source for [two_stage_daniell_family]: evaluation at false
    gives a consistent normalized monotone family on the regression
    inverse system, supporting Federer 2.6.6, pp. 120–121. *)
Lemma two_stage_daniell_family (R : realType) :
  @is_consistent_inverse_daniell_family R [the choiceType of (bool : Type)] (fun i j=>i ==> j)
    (fun _=>[the topologicalType of (bool : Type)]) two_stage_bonding (fun _ f=>f false).
Proof.
constructor.
- move=> i; exact: point_evaluation_monotone_daniell.
- by [].
- by move=> [] [] // _ f hf.
Qed.

(** Source for [non_surjective_inverse_integral_regression]:
    the sealed inverse-limit integral evaluates at false in this
    non-surjective system, supporting the generality of Federer
    2.6.6, pp. 120–121. *)
Example non_surjective_inverse_integral_regression (R : realType) (f : bool -> R) :
  compactly_supported_continuous_functions f ->
  @inverse_limit_daniell_integral R [the choiceType of (bool : Type)] (fun i j=>i ==> j)
    (fun _=>[the topologicalType of (bool : Type)]) two_stage_bonding [the topologicalType of (bool : Type)]
    two_stage_projection (fun _ f=>f false) two_stage_inverse_system two_stage_inverse_limit
    (two_stage_daniell_family R) f=f false.
Proof.
move=> hf.
have hb := @inverse_limit_daniell_integral_specification R [the choiceType of (bool : Type)] (fun i j=>i ==> j)
    (fun _=>[the topologicalType of (bool : Type)]) two_stage_bonding [the topologicalType of (bool : Type)]
    two_stage_projection (fun _ f=>f false) two_stage_inverse_system two_stage_inverse_limit
    (two_stage_daniell_family R).
exact: hb.2.2 true f hf.
Qed.

(** Boundary regressions for the Radon vector representation, Federer
    2.5.14, p. 108. Source context and the distinction between local and
    global nullity are documented in RadonVectorRepresentation.v and
    LocallyNullMeasureUP.v. *)
From Federer Require Import RadonVectorRepresentation RadonVectorUniqueness
  LocallyNullMeasureUP LocallyAlmostMeasureLaws RadonDualLocalModification
  TrivialVectorVariation CompactSupportVectorContinuity OrderBoundedVectorFunctionalUP
  CompactSupportFunctionUP RadonMeasureUP VectorDaniellNormalisationUP
  RealNormUP VectorDaniellHypotheses VectorDaniellRepresentationUP FunctionLatticeUP
  RealIntegralFunctionalUP MeasureUP MeasureIntegralUP SummableRealFunctionUP MeasureAlmostUP.

(** Source for [radon_locally_equal_compact_space_example]:
    local uniqueness in Federer 2.5.14, p. 108, becomes
    ordinary almost uniqueness on a compact space, since the
    Radon measure of the whole space is finite. *)
Example radon_locally_equal_compact_space_example (R : realType) (X : topologicalType)
    (phi : set X -> \bar R) (hr : is_radon_measure phi) (P : set X) :
  compact (@setT X) -> measure_locally_almost_everywhere phi P ->
  measure_almost_everywhere phi P.
Proof.
move=> hX hP; have h := hP setT (radon_compact_finite hr hX).
by rewrite setTI in h.
Qed.

(** Source for [radon_zero_dimensional_variation_example]:
    zero-dimensional boundary of Federer 2.5.14, p. 108.
    The Radon variation measure vanishes everywhere, so the
    almost unit-norm assertion never requires a unit functional
    on the zero space. No lattice unit series is assumed. *)
Example radon_zero_dimensional_variation_example (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hQ : is_vector_function_space Q)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (hT : is_order_bounded_vector_functional N (@compactly_supported_continuous_functions R X) Q T)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (hrep : is_real_integral_functional phi (positive_function_lattice (@compactly_supported_continuous_functions R X))
      (variation_integral N Q T)) :
  (forall y : E, y=0) -> forall A, phi A=0%E.
Proof.
move=> hE.
have hV := @compact_support_vector_variation_functional R X E N hN Q T
  (radon_hausdorff hr) (radon_locally_compact hr) hQ hM hT.
apply: (@radon_positive_compact_zero_measure R X phi hphi hr (variation_integral N Q T) hrep).
exact (@trivial_vector_variation_zero R X E N hN
  (@compactly_supported_continuous_functions R X) Q T hQ hV hE).
Qed.

(** Source for [radon_local_modification_integral_example]:
    changing a density on a locally null set preserves every
    compact-norm-support test in Federer 2.5.14, p. 108.
    The modified representative need not have a uniform bound. *)
Example radon_local_modification_integral_example (R : realType) (X : topologicalType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi) (hr : is_radon_measure phi)
    (Q : set (X -> E)) (T : (X -> E) -> R)
    (hM : is_vector_lattice_module hN (@compactly_supported_continuous_functions R X) Q)
    (k l : X -> weak_dual_space hN) (w : X -> E) :
  is_vector_daniell_density phi Q T k ->
  measure_locally_almost_everywhere phi [set x | k x=l x] -> Q w ->
  is_measure_integral phi (real_total_integrand (fun x => val (l x) (w x))) (T w)%:E.
Proof.
move=> hk he hw.
have hl := @radon_dual_locally_equal_representation R X E N hN phi hphi hr Q T hM k l he hk.
exact (@vector_daniell_density_integral R X E N hN phi Q T l hl w hw).
Qed.

(** Boundary regressions for Federer 2.5.20, p. 114. Editions and the
    absence of a matching. *)
From Federer Require Import CompactFunctionSpace CompactFunctionSpaceUP
  CompactPushforwardSupport RegularizedScalarRatio.

(** Source for [compact_function_space_empty_domain_example]:
    empty-space boundary of E=K(Y) in Federer 2.5.20,
    p. 114. Evaluation injectivity implies that every vector
    is zero when Y is empty; no chosen point of Y is needed. *)
Example compact_function_space_empty_domain_example (R : realType)
    (Y : topologicalType) (hY : forall y : Y, False)
    (v : compact_function_space R Y) : v=0.
Proof.
apply: (@compact_function_evaluation_injective R Y (compact_function_space R Y)
  (@compact_function_evaluate R Y) (@compact_function_space_specification R Y) v 0).
by apply: funext=> y; exact: False_ind _ (hY y).
Qed.

(** Source for [disintegration_zero_weight_ratio_example]:
    zero-weight boundary of the variation approximation used
    for the final measure identity in Federer 2.5.20,
    p. 114. The regularized quotient is defined even
    where the positive test function vanishes. *)
Example disintegration_zero_weight_ratio_example (R : realType) (e : R) :
  0<e -> `|0/(0+e)|=0 /\ `|0*(0/(0+e))-0|=0.
Proof. by move=> _; rewrite !mul0r subrr !normr0. Qed.

(** Source for [constant_graph_fibre_example]: the graph
    construction in the second paragraph of Federer 2.5.20,
    p. 114, for a constant map. Its image has an
    empty fibre away from that constant. *)
Example constant_graph_fibre_example (X Y : topologicalType) (a x : X) (y : Y) :
  x<>a -> ~ (daniell_graph_map (fun _ : Y => a) @` setT) (x,y).
Proof.
move=> hne him; apply: hne.
by symmetry; exact: (@daniell_graph_map_image_fibre X Y (fun _ : Y => a) x y him).
Qed.

(** Boundary regressions for the actual geometric example in Federer 2.5.10,
    p. 101. Hausdorff length and the projected counting measure have
    separate sealed specifications; the Source context are recorded in
    PlaneLineMeasures.v. *)
From Federer Require Import MeasureBasic HausdorffLength PlaneLineMeasures
  PlaneProjectionMeasure EuclideanInnerProduct InnerMetric LebesgueScalarMeasure.

(** Source for [hausdorff_length_empty_example]: empty-cover
    boundary of Federer 2.10.1, pp. 169–170, supporting
    the actual Hausdorff measure used in 2.5.10, p. 101. *)
Example hausdorff_length_empty_example (R : realType) (X : metricType R) :
  @hausdorff_length R X set0 = 0%E.
Proof. exact: measure_empty (@hausdorff_length_is_measure R X). Qed.

(** Source for [plane_degenerate_segment_example]: degenerate
    line-segment boundary of 2.10.7, p. 175, used by the
    geometric example in Federer 2.5.10, p. 101. *)
Example plane_degenerate_segment_example (R : realType) (s a : R) :
  hausdorff_length (plane_vertical s @` `[a,a])=0%E.
Proof.
by rewrite plane_vertical_hausdorff lebesgue_scalar_segment // subrr.
Qed.

(** Source for [plane_unit_segments_distinguish_measures_example]:
    regression for the horizontal/vertical distinction in Federer
    2.5.10, p. 101. Both segments have unit H^1 measure,
    while their projected-counting measures are one and zero. *)
Example plane_unit_segments_distinguish_measures_example (R : realType) (s t : R) :
  hausdorff_length (plane_horizontal t @` `[0%R,1%R]) = 1%E /\
  hausdorff_length (plane_vertical s @` `[0%R,1%R]) = 1%E /\
  plane_projection_measure (plane_horizontal t @` `[0%R,1%R]) = 1%E /\
  plane_projection_measure (plane_vertical s @` `[0%R,1%R])=0%E.
Proof.
rewrite plane_horizontal_hausdorff plane_vertical_hausdorff
  plane_horizontal_projection_measure plane_vertical_segment_projection_null
  lebesgue_scalar_segment ?ler01 // subr0.
by repeat split.
Qed.

From Federer Require Import VariationIntegralMeasure UniformFunctionNormUP BoundedContinuousSpaceUP BoundedContinuousBanachSpace.

(** Boundary regressions for Federer (1969), 2.5.6, p. 98, and 2.5.16, p.
    110: a vanishing negative variation measure, and the norm nu(f) = sup im
    |f| of a constant function on a nonempty metric space. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import VariationIntegralMeasure UniformFunctionNormUP BoundedContinuousSpaceUP
  BoundedContinuousBanachSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [variation_measure_zero_negative_example]: regression of
    the variation measure psi+ + psi- of Federer 2.5.6, p. 98, when
    psi- is the zero measure, as for a monotone Daniell integral: the
    variation measure is psi+ itself. *)
Example variation_measure_zero_negative_example (R : realType) (X : choiceType)
    (mu : set X -> \bar R) :
  variation_measure mu (fun _ => 0%E) = mu.
Proof. by apply: funext=> S; rewrite /variation_measure adde0. Qed.

(** Source for [bounded_continuous_constant_norm_example]: regression of
    nu(f) = sup im |f| in Federer 2.5.16, p. 110: on a nonempty metric
    space the constant function c has norm |c|; for c = 0 this checks
    the zero norm. *)
Example bounded_continuous_constant_norm_example (R : realType) (Y : metricType R) (y0 : Y)
    (v : bounded_continuous_space Y) (c : R) :
  bounded_continuous_evaluate v = (fun _ => c) -> bounded_continuous_space_norm v = `|c|.
Proof.
move=> hv.
have hn := bounded_continuous_norm_supremum (bounded_continuous_space_specification Y) v.
rewrite hv in hn.
apply: (uniform_function_norm_unique hn); constructor.
- exact: normr_ge0.
- by move=> y.
- by move=> d _ hd; exact: hd y0.
Qed.

From Federer Require Import CardinalSuccessorExistence ExtendedLatticeDensity.

(** Source for [cantor_power_nat_example]: regression for Cantor's
    theorem (Kelley, Appendix, Theorem 161, p. 276), used for the sets
    Y_j of Federer 2.5.11, p. 102: the subsets of nat do not inject
    into nat. *)
Example cantor_power_nat_example : ~ (@setT (set nat) #<= @setT nat)%card.
Proof. exact: cantor_power_not_le. Qed.

(** Source for [cantor_power_empty_example]: empty boundary case of
    the same theorem, supporting Federer 2.5.11, p. 102: the power
    set of the empty set has one member, the empty set none. *)
Example cantor_power_empty_example : ~ (@setT (set void) #<= @setT void)%card.
Proof. exact: cantor_power_not_le. Qed.

(** Source for [aleph_one_uncountable_example]: regression for the
    set Y_1 of Federer 2.5.11, p. 102: a set with cardinal number
    aleph_1 exists and is uncountable. *)
Example aleph_one_uncountable_example : exists J1 : choiceType, ~ countable (@setT J1).
Proof. by have [J1 h1] := aleph_one_exists; exists J1; exact: h1.2.1. Qed.

(** Source for [zero_times_infinity_fine_example]: boundary case of
    the reduction of extended real densities in Federer 2.5.10,
    p. 100: with the convention 0 . infinity = 0 of 2.1.1, p. 51,
    0 . infinity equals 0 . fine(infinity). *)
Example zero_times_infinity_fine_example (R : realType) :
  (((0 : R) * fine (+oo : \bar R))%R)%:E = ((0 : R)%:E * +oo)%E.
Proof. by apply: extended_product_finite_fine; rewrite mul0e. Qed.

From Federer Require Import UncountableProductNotRadon DiscreteSliceSpace DiscreteSliceRadon LocalUniquenessExample.

(** Source for [slice_count_zero_regression]: Federer 2.5.14, p. 108,
    counterexample to almost uniqueness; boundary case of the counting
    functional on K(D) for the zero function, whose set of nonzero values
    is empty. Regression example. *)
Lemma slice_count_zero_regression (R : realType) (D : choiceType) :
  @slice_count R D (fun _ => 0%R) = 0%R.
Proof.
transitivity (0 * @slice_count R D (fun _ => 0%R))%R; last by rewrite mul0r.
rewrite -slice_count_scale; congr slice_count.
by apply: funext=> d; rewrite mul0r.
Qed.

(** Source for [slice_count_empty_indicator_regression]: Federer 2.5.14,
    p. 108; the indicator of the empty list of indices has counting
    value zero, the case m = 0 of the lower estimate for open supersets
    of Z = D x {0}. Regression example. *)
Lemma slice_count_empty_indicator_regression (R : realType) (D : choiceType) :
  @slice_count R D (fun d => (d \in [::])%:R) = 0%R.
Proof. by rewrite slice_count_indicator. Qed.

(** Source for [power_set_zero_slice_regression]: Federer 2.5.14,
    p. 108, "only locally so", with D the power set of the natural
    numbers, which is uncountable (natural_power_set_uncountable): some
    Radon measure representing lambda makes Z = D x {0} locally null of
    infinite measure. Regression example for the hypotheses of
    zero_slice_infinite. *)
Lemma power_set_zero_slice_regression (R : realType) :
  exists phi : set _ -> \bar R, is_measure phi /\ measure_locally_null phi (@zero_slice R (set nat)) /\
    phi (@zero_slice R (set nat)) = +oo%E.
Proof.
have [phi [hm [hr hA]]] := compact_support_radon_representation
  (@slice_space_hausdorff R (set nat)) (@slice_space_locally_compact R (set nat))
  (@slice_lambda_monotone_daniell R (set nat)).
exists phi; split=> //; split.
- exact: zero_slice_locally_null hm hr hA.
- exact: zero_slice_infinite hm hr hA natural_power_set_uncountable.
Qed.

(** Source for [uncountable_product_not_radon_regression]: Federer
    2.5.15, pp. 108-109, with J the power set of the natural numbers:
    the K(X) regular measure associated with evaluation at xi is not a
    Radon measure. Regression example for 2.5.14, p. 107, "Thus phi may
    fail to be a Radon measure". *)
Lemma uncountable_product_not_radon_regression (R : realType) :
  exists phi : set (product_space R (set nat)) -> \bar R, is_measure phi /\ ~ is_radon_measure phi /\
    ~ measure_measurable phi [set @base_point R (set nat)].
Proof.
have [phi [hm hA hr [hc hn] hnr]] :=
  @regular_measure_may_fail_radon R (set nat) natural_power_set_uncountable.
by exists phi.
Qed.

From mathcomp Require Import cardinality topology normedtype. From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength MeasureUP MeasureBasic MeasureAlmostBasic StieltjesMonotone StieltjesImageMeasures StieltjesInducedPairLaws.
Import numFieldTopology.Exports.
Section StieltjesInducedPairExamples.
Local Open Scope classical_set_scope.
(** Source for [constant_induced_pair_zero_example]: Federer 2.5.17,
    p. 111, boundary case g(x) = c of the measures induced by g: the
    Daniell integral vanishes, "hence psi^- = 0", and equality in (2)
    for the continuous function g gives psi^+{x : a < x < b} =
    V_a^b g = 0, so psi^+ = 0 as well. Regression example for
    [induced_measure_pair_laws] and [induced_measure_pair_monotone]. *)
Example constant_induced_pair_zero_example (R : realType) (c : R) (psip psim : set R -> \bar R) :
  is_induced_measure_pair (fun _ : R => c) psip psim ->
  psip = (fun _ => 0%E) /\ psim = (fun _ => 0%E).
Proof.
move=> hpair.
have hmono : forall x y : R, (x <= y)%R -> ((fun _ : R => c) x <= (fun _ : R => c) y)%R.
  by move=> x y _; exact: lexx.
have hk := monotone_locally_finite_variation hmono.
have [hzero _] := induced_measure_pair_monotone hk hmono hpair.
have [hm [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ hcont]]]]]]]]]]]]] := induced_measure_pair_laws hk hpair.
have hc : continuous (fun _ : R => c) by move=> x; exact: cvg_cst.
have hopen : forall a b : R, psip `]a, b[ = 0%E.
  move=> a b; case: (leP a b)=> hab.
  - have h := hcont hc a b hab.
    by rewrite hzero /= adde0 (monotone_total_variation hmono hab) subrr in h.
  - have -> : `]a, b[ = set0 :> set R.
      apply/seteqP; split=> x //; rewrite /= in_itv /= => /andP[h1 h2].
      by have := lt_trans h1 h2; rewrite ltNge (ltW hab).
    exact: measure_empty hm.
have hT : psip setT = 0%E.
  have -> : setT = \bigcup_(n in [set: nat]) `](- n%:R : R), n%:R[.
    apply/seteqP; split=> y // _.
    have /andP[_ hy] := truncn_itv (normr_ge0 y).
    exists (Num.truncn `|y|).+1=> //; move: hy; rewrite /= in_itv /= ltr_norml.
    by [].
  by apply: (measure_null_countable_union hm (countableP _))=> n _; exact: hopen.
split=> //.
by apply/funext=> S; exact (measure_null_subset hm (subsetT S) hT).
Qed.
End StieltjesInducedPairExamples.

From Federer Require Import FiniteCoordinateSplit FiniteCoordinateAdjoinProduct FiniteCoordinateRestriction FiniteCoordinateProductIdentification.

Section FiniteProductIdentificationExamples.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [finite_product_separated_value_empty_example]: empty
    index-set boundary of the product formula for the finite products
    of Federer 2.6.6, p. 120: mu_0 of the empty product is 1. *)
Example finite_product_separated_value_empty_example (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
    (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
    (hA1 : forall i, A i (fun _=>1) = 1) (f : forall j, Y j -> R) :
  @finite_coordinate_product R I Y A hh hc hA hA1 fset0 (fun x=>\prod_(j <- fset0) f j (x j)) = 1.
Proof.
rewrite (@finite_product_separated_value R I Y A hh hc hA hA1 fset0 f) ?big_seq_fset0 //.
Qed.

(** Source for [finite_product_marginal_restriction_same_example]:
    the boundary a = b of "mu_b(f o p^b_a) = mu_a(f) mu_{b-a}(1) =
    mu_a(f)", Federer 2.6.6, p. 120, where b - a is empty and
    p^a_a is the identity. *)
Example finite_product_marginal_restriction_same_example (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
    (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
    (hA1 : forall i, A i (fun _=>1) = 1) (F : {fset I}) (f : finite_coordinate_space Y F -> R) :
  compactly_supported_continuous_functions f ->
  finite_coordinate_marginal (@finite_coordinate_product R I Y A hh hc hA hA1) F
    (f \o finite_coordinate_restriction (fun j (hj : j \in F)=>hj))=
    finite_coordinate_marginal (@finite_coordinate_product R I Y A hh hc hA hA1) F f.
Proof.
move=> hf.
have [h1 h2] := @finite_product_marginal_restriction R I Y A hh hc hA hA1 F F (fun j hj=>hj) f hf.
by rewrite h1 h2.
Qed.

(** Source for [finite_product_adjoin_first_factor_example]: the first
    step a = 0 of the method of 2.6.4, p. 119, in Federer 2.6.6,
    p. 120: mu_{{i}} corresponds under psi to the product of the
    empty product mu_0 and mu_i. *)
Example finite_product_adjoin_first_factor_example (R : realType) (I : choiceType)
    (Y : I -> topologicalType) (A : forall i, (Y i -> R) -> R)
    (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
    (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
    (hA1 : forall i, A i (fun _=>1) = 1) (i : I) :
  is_daniell_product (finite_coordinate_marginal (@finite_coordinate_product R I Y A hh hc hA hA1) fset0) (A i)
    (@finite_coordinate_adjoined_functional R I Y (@finite_coordinate_product R I Y A hh hc hA hA1) fset0 i).
Proof. by apply: finite_product_adjoin_daniell_product; rewrite in_fset0. Qed.
End FiniteProductIdentificationExamples.

From Federer Require Import StieltjesImageSurjectivity.

(** Source for [bounded_increasing_not_onto_example]: regression for the
    counterexample to the unrestricted form of Federer 2.5.18(2), p. 112:
    the continuous increasing map g(x) = x/(1 + |x|) does not attain the
    value 1, so im g is not R. *)
Example bounded_increasing_not_onto_example (R : realType) :
  ~ exists x : R, bounded_increasing x = 1.
Proof.
move=> [x hx]; have := bounded_increasing_bound x.
by rewrite hx normr1 ltxx.
Qed.

From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP HomogeneousSpaceLaws CosetSpaceUP CosetSpace CovariantIntegralUP DaniellSpaceWeakTopology CompactSupportFunctionUP.

(** Regression examples for Federer (1969), 2.7.1, pp. 121–122. Source
    context and proof conventions: HomogeneousSpaceUP.v, CosetSpaceUP.v and
    CovariantIntegralUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import HomeomorphismUP TopologicalGroupUP TopologicalGroupLaws
  HomogeneousSpaceUP HomogeneousSpaceLaws CosetSpaceUP CosetSpace CovariantIntegralUP
  DaniellSpaceWeakTopology CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section InvariantMeasureFoundationExamples.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).

(** Source for [point_space_homogeneous_example]: regression for the
    definition of a homogeneous space in Federer 2.7.1, p. 121: every
    group acts on a one-point space, and the isotropy subgroup of its
    point is G. *)
Example point_space_homogeneous_example :
  is_homogeneous_space mul (fun (_ : G) (x : discrete_topology unit) => x) /\
  isotropy_subgroup (fun (_ : G) (x : discrete_topology unit) => x) tt = setT.
Proof.
split; last by apply/seteqP.
constructor.
- by move=> p; exact: cvg_snd.
- by [].
- by move=> x U _; exact: discrete_open.
- by move=> x; apply/seteqP; split=> // y _; exists e=> //; case: x; case: y.
Qed.

(** Source for [constant_action_not_unital_example]: regression for
    the derivation of A_e = 1_X in Federer 2.7.1, p. 121. The constant
    map A(g,x) = true on the discrete space {true, false} is
    continuous, compatible with the multiplication and has open orbit
    maps, but A(e,false) differs from false; the condition im A^x = X
    fails, so this A does not make the space homogeneous. *)
Example constant_action_not_unital_example :
  let A := fun (_ : G) (_ : discrete_topology bool) => true in
  [/\ continuous (fun p : G * discrete_topology bool => A p.1 p.2),
    forall g h x, A (mul g h) x = A g (A h x),
    forall x, is_open_map (orbit_map A x),
    A e false <> false &
    ~ is_homogeneous_space mul A].
Proof.
move=> A; split=> //.
- by move=> p; exact: cvg_cst.
- by move=> x U _; exact: discrete_open.
- move=> hA; have : (orbit_map A false @` setT) false by rewrite (homogeneous_orbit_onto hA false).
  by case.
Qed.

(** Source for [zero_integral_covariant_example]: regression for the
    hypothesis mu <> 0 in Federer 2.7.1, p. 122: the zero integral is
    chi covariant for every function chi, for instance chi = 0, which is
    not a homomorphism into R ~ {0}. *)
Example zero_integral_covariant_example (R : realType) (X : topologicalType) (A : G -> X -> X) :
  is_covariant_integral A (fun _ => (0 : R)) (fun _ : X -> R => 0) /\ (fun _ : G => (0 : R)) e <> 1.
Proof.
split; last by move/eqP; rewrite eq_sym oner_eq0.
constructor.
- exact (@daniell_integrals_zero R X (@compactly_supported_continuous_functions R X)).
- by move=> u g _; rewrite mulr0.
Qed.

(** Source for [whole_group_coset_space_point_example]: regression for
    the space G/S of Federer 2.7.1, p. 122, with S = G: the space G/G
    has exactly one point. *)
Example whole_group_coset_space_point_example :
  is_group_laws mul inv e -> forall g h, coset_projection mul setT g = coset_projection mul setT h.
Proof.
move=> hG g h.
have hS : is_subgroup mul inv e setT by [].
exact/(coset_projection_eq (coset_space_specification hG hS)).
Qed.

(** Source for [trivial_subgroup_coset_projection_injective_example]:
    regression for the space G/S of Federer 2.7.1, p. 122, with
    S = {e}: the projection of G onto G/{e} is injective. *)
Example trivial_subgroup_coset_projection_injective_example :
  is_group_laws mul inv e -> injective (coset_projection mul [set e]).
Proof.
move=> hG.
have hS : is_subgroup mul inv e [set e].
  constructor=> //=; [by move=> g h -> ->; exact: (group_mul1g hG)|by move=> g ->; exact: (group_inv1 hG)].
move=> g h /(coset_projection_eq (coset_space_specification hG hS)) /= hgh.
by rewrite -(group_mulKVg hG g h) hgh (group_mulg1 hG).
Qed.

End InvariantMeasureFoundationExamples.

From Federer Require Import HaarIntegralUP.

(** Regression examples for Federer (1969), 2.7.2, pp. 122-123. Source
    context and proof conventions: HaarIntegralUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground DaniellIntegralNegation TopologicalGroupUP
  HomogeneousSpaceUP CompactSupportFunctionUP DaniellSpaceWeakTopology CovariantIntegralUP
  HaarIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarIntegralExamples.
Variable R : realType.
Local Notation U := (discrete_topology unit).
Local Notation umul := (fun _ _ : U => (tt : U)).
Local Notation uinv := (fun x : U => x).

(** Source for [zero_integral_not_left_haar_example]: regression for
    "a nonzero monotone left invariant integral ... is called a left
    Haar integral", Federer 2.7.2, p. 122: the zero functional is a left
    invariant integral but not a left Haar integral. *)
Example zero_integral_not_left_haar_example (G : topologicalType) (mul : G -> G -> G) :
  is_left_invariant_integral mul (fun _ : G -> R => 0) /\
  ~ is_left_haar_integral mul (fun _ : G -> R => 0).
Proof.
split; last by case=> _ _ [u _]; apply.
constructor.
- exact (@daniell_integrals_zero R G (@compactly_supported_continuous_functions R G)).
- by move=> u g _; rewrite mulr0.
Qed.

(** Source for [trivial_group_haar_example]: regression for the
    definitions of left and right Haar integrals in Federer 2.7.2,
    p. 122: on the one-point group, evaluation at its point is both a
    left and a right Haar integral. *)
Example trivial_group_haar_example :
  [/\ is_topological_group umul uinv (tt : U),
    is_left_haar_integral umul (@point_evaluation R U tt) &
    is_right_haar_integral umul uinv (@point_evaluation R U tt)].
Proof.
have hcst (T : topologicalType) (c : R) : continuous ((fun _ : T => c) : T -> real_line_metric R).
  by move=> x; exact: cvg_cst.
have hK : @compactly_supported_continuous_functions R U (fun _ => 1).
  split; first exact: hcst.
  have -> : real_function_support (fun _ : U => (1 : R)) = [set (tt : U)].
    apply/seteqP; split=> x; first by case: x.
    move=> _; rewrite /real_function_support.
    by apply: (@subset_closure U [set y : U | (1 : R) <> 0]); apply/eqP; exact: oner_neq0.
  exact: compact_set1.
have hm := @point_evaluation_monotone_daniell R U (@compactly_supported_continuous_functions R U) tt.
have hd := monotone_daniell_is_daniell hm.
have hn : exists2 u, @compactly_supported_continuous_functions R U u & point_evaluation tt u <> 0.
  by exists (fun _ => 1)=> //; apply/eqP; exact: oner_neq0.
split.
- constructor; [by constructor=> // g; case: g|by move=> p; exact: cvg_cst|by move=> x; exact: cvg_id].
- by constructor=> //; constructor=> // u g _; rewrite mul1r.
- by constructor=> //; constructor=> // u g _; rewrite mul1r.
Qed.

End HaarIntegralExamples.

From Federer Require Import UniformActionUP UniformActionLaws.
(** Regression examples for Federer (1969), 2.7.3, p. 123. *)
Section UniformActionExamples.
Variable G : topologicalType.
Variable mul : G -> G -> G.

(** Source for [empty_space_orbit_family_not_basis_example]: regression
    for "when this condition holds one may take as B the family of the
    sets U_{g in G} A_g(V) x A_g(V) corresponding to all nonempty open
    subsets V of X", Federer 2.7.3, p. 123. On the empty space, every
    group acts as a homogeneous space and the condition holds
    vacuously, but the family is empty and is not the basis of any
    uniformity, since a uniformity contains X x X. The hypothesis that
    X is nonempty in uniform_action_orbit_basis cannot be omitted. *)
Example empty_space_orbit_family_not_basis_example :
  let A := fun (_ : G) (x : discrete_topology void) => x in
  [/\ is_homogeneous_space mul A, uniform_action_condition A,
    orbit_entourage_family A = set0 &
    ~ exists E, is_uniformity E /\ is_uniformity_basis E (orbit_entourage_family A)].
Proof.
move=> A; split.
- constructor; first by move=> [g x]; exfalso; case: x.
  + by [].
  + by move=> x; exfalso; case: x.
  + by move=> x; exfalso; case: x.
- by move=> x; exfalso; case: x.
- by apply/seteqP; split=> // p [V [_ [x _]] _]; exfalso; case: x.
- case=> E [hE [_ hb]].
  have hT : E setT := @filterT _ _ (uniformity_filter hE).
  by have [beta [V [_ [x _]] _] _] := hb _ hT; exfalso; case: x.
Qed.

(** Source for [identity_action_orbit_family_not_basis_example]:
    regression for the same assertion of Federer 2.7.3, p. 123, and the
    condition im A^x = X of 2.7.1, p. 121. The trivial action on the
    discrete space {true, false} satisfies the condition of 2.7.3 with
    W = {x}, but it is not transitive, and the family of the sets
    U_{g in G} A_g(V) x A_g(V) is not the basis of any uniformity: the
    member for V = {true} does not contain (false, false). *)
Example identity_action_orbit_family_not_basis_example :
  let A := fun (_ : G) (x : discrete_topology bool) => x in
  [/\ uniform_action_condition A, ~ is_homogeneous_space mul A &
    ~ exists E, is_uniformity E /\ is_uniformity_basis E (orbit_entourage_family A)].
Proof.
move=> A; split.
- move=> x V hV; exists ([set x]).
    by apply: open_nbhs_nbhs; split; [exact: discrete_open|].
  by move=> g _ y [z -> <-]; exact: nbhs_singleton hV.
- move=> hA; have : (orbit_map A true @` setT) false by rewrite (homogeneous_orbit_onto hA true).
  by case.
- case=> E [hE [hBE _]].
  have hb : orbit_entourage_family A (orbit_entourage A [set true]).
    by exists ([set true])=> //; split; [exact: discrete_open|exists true].
  have := uniformity_diagonal hE (hBE _ hb) (erefl : diagonal (false, false)).
  by case=> g _ [[z hz hzf] _]; move: hzf; rewrite hz.
Qed.

End UniformActionExamples.

From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP CompactSupportFunctionLattice TopologicalGroupUP HomogeneousSpaceUP HomogeneousSpaceLaws UniformActionUP HaarRatioUP HaarRatioLaws InvariantIntegralExistence HaarIntegralExistence.
(** Regression examples for Federer (1969), 2.7.4-2.7.5, pp. 123-125. Source
    context and proof conventions: HaarRatioLaws.v and
    InvariantIntegralExistence.v. *)
Section InvariantIntegralExamples.
Variable R : realType.
Local Open Scope ring_scope.

(** Source for [haar_ratio_self_example]: regression for the Haar
    ratio of Federer 2.7.4, p. 123: (v:v) = 1 for 0 <> v in K(X)+. The
    family consisting of the pair (e,1) belongs to C(v,v), since
    A_e = 1_X (2.7.1, p. 121), and 1/(v:v) <= (v:v)/(v:v) <= (v:v)
    (p. 124) gives (v:v) >= 1. Only the specification of Haar ratios is
    used. *)
Example haar_ratio_self_example (G X : topologicalType) (mul : G -> G -> G) (inv : G -> G)
    (e : G) (A : G -> X -> X) (rho : (X -> R) -> (X -> R) -> R) (v : X -> R) :
  is_group_laws mul inv e -> is_homogeneous_space mul A -> is_haar_ratio_function A rho ->
  positive_function_lattice (@compactly_supported_continuous_functions R X) v ->
  (exists b, v b <> 0) -> rho v v = 1.
Proof.
move=> hG hA hrho hv hb.
have hpos := haar_ratio_positive hrho hv hv hb hb.
have /andP [_ h] := haar_ratio_quotient_bounds hA hrho hv hv hv hb hb hb.
rewrite divff ?gt_eqF // in h.
apply/eqP; rewrite eq_le h andbT.
have hcov : haar_family_cover A v v [:: (e, 1)].
  split; first by move=> p; rewrite inE=> /eqP ->; exact: ler01.
  by move=> x; rewrite big_seq1 /= mul1r (homogeneous_unit_action hG hA).
by have := haar_ratio_lower (hrho _ _ hv hv hb) hcov; rewrite /haar_family_total big_seq1.
Qed.

(** Source for [invariant_integral_empty_space_example]: regression
    for "Theorem. If G acts uniformly on X, then there exists a nonzero
    monotone invariant integral on K(X)", Federer 2.7.4, p. 123. On the
    empty space X every map A is a transitive action making X a
    homogeneous space (2.7.1, p. 121), X is locally compact Hausdorff,
    and G acts uniformly, with the family of all subsets of X x X as
    uniformity and as invariant basis; but K(X) consists of the zero
    function only, on which every Daniell integral vanishes. The
    hypothesis that X is nonempty in
    uniform_action_invariant_integral_exists cannot be omitted. *)
Example invariant_integral_empty_space_example (G : topologicalType) (mul : G -> G -> G)
    (A : G -> discrete_topology void -> discrete_topology void)
    (mu : (discrete_topology void -> R) -> R) :
  [/\ is_homogeneous_space mul A, acts_uniformly A, hausdorff_space (discrete_topology void),
    locally_compact [set: discrete_topology void] &
    ~ is_nonzero_monotone_invariant_integral A mu].
Proof.
split.
- constructor; first by move=> [g x]; case: x.
  + by move=> g h x; case: x.
  + by move=> x; case: x.
  + by move=> x; case: x.
- exists [set: set (discrete_topology void * discrete_topology void)],
    [set: set (discrete_topology void * discrete_topology void)]; split.
  + constructor; first by constructor.
    * by move=> D _ [x y]; case: x.
    * by [].
    * by move=> D _; exists D=> // -[x y]; case: x.
  + by move=> x; case: x.
  + by split=> // D _; exists D.
  + by move=> beta g x; case: x.
- by move=> x; case: x.
- by move=> x; case: x.
case=> _ hm [u hu hmu]; apply: hmu.
have h0 : @compactly_supported_continuous_functions R (discrete_topology void) (fun _ => 0).
  exact: compactly_supported_zero_function.
have := monotone_daniell_integral_add hm h0 h0.
have -> : (fun x : discrete_topology void => (0 : R) + 0) = fun _ => 0 by apply: funext=> -[].
have -> : u = fun _ => 0 by apply: funext=> -[].
by move=> h; apply: (@addrI _ (mu (fun _ => 0))); rewrite addr0 -h.
Qed.

End InvariantIntegralExamples.

From Federer Require Import RealMetricBackground DaniellIntegralNegation TopologicalGroupUP CompactSupportFunctionUP DaniellSpaceWeakTopology CovariantIntegralUP HaarIntegralUP HaarIntegralDensity HaarIntegralUniqueness.

(** Regression examples for Federer (1969), 2.7.6-2.7.7, pp. 125-126. Source
    context and proof conventions: HaarIntegralDensity.v and
    HaarIntegralUniqueness.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground DaniellIntegralNegation TopologicalGroupUP
  CompactSupportFunctionUP DaniellSpaceWeakTopology CovariantIntegralUP HaarIntegralUP
  HaarIntegralDensity HaarIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HaarDensityExamples.
Variable R : realType.
Local Notation U := (discrete_topology unit).
Local Notation umul := (fun _ _ : U => (tt : U)).
Local Notation uinv := (fun x : U => x).
Local Notation KU := (@compactly_supported_continuous_functions R U).

(** Source for [one_point_constant_compact]: the constant function 1
    on the one-point space belongs to K(G), Federer 2.5.13, p. 106.
    Supporting lemma for the regression examples of 2.7.6-2.7.7,
    pp. 125-126. *)
Lemma one_point_constant_compact : KU (fun _ => 1).
Proof.
split; first by move=> x; exact: cvg_cst.
have -> : real_function_support (fun _ : U => (1 : R)) = [set (tt : U)].
  apply/seteqP; split=> x; first by case: x.
  move=> _; rewrite /real_function_support.
  by apply: (@subset_closure U [set y : U | (1 : R) <> 0]); apply/eqP; exact: oner_neq0.
exact: compact_set1.
Qed.

(** Source for [one_point_group_lch_haar_example]: regression for the
    hypotheses of Federer 2.7.6-2.7.7, pp. 125-126: the one-point group
    is a locally compact Hausdorff topological group, and evaluation at
    its point is both a left and a right Haar integral (2.7.2,
    p. 122). *)
Example one_point_group_lch_haar_example :
  [/\ is_locally_compact_hausdorff_group umul uinv (tt : U),
    is_left_haar_integral umul (@point_evaluation R U tt) &
    is_right_haar_integral umul uinv (@point_evaluation R U tt)].
Proof.
have hm := @point_evaluation_monotone_daniell R U KU tt.
have hd := monotone_daniell_is_daniell hm.
have hn : exists2 u, KU u & point_evaluation tt u <> 0.
  by exists (fun _ => 1); [exact: one_point_constant_compact|apply/eqP; exact: oner_neq0].
have hT : [set: U] = [set (tt : U)] by apply/seteqP; split=> // -[].
split.
- constructor.
  + constructor; first by constructor=> // g; case: g.
      by move=> p; exact: cvg_cst.
    by move=> x; exact: cvg_id.
  + by move=> [] [] _.
  + move=> [] _; exists [set: U]; first by rewrite withinET; exact: filterT.
    by split; [rewrite hT; exact: compact_set1|exact: closedT].
- by constructor=> //; constructor=> // u g _; rewrite mul1r.
- by constructor=> //; constructor=> // u g _; rewrite mul1r.
Qed.

(** Source for [one_point_group_haar_density_example]: regression for
    "k is uniquely characterized by (2)", Federer 2.7.6, p. 125: on the
    one-point group, with lambda = mu the evaluation at its point, every
    continuous k with mu(k u) = lambda(u) whenever u in K(G) is the
    constant 1. *)
Example one_point_group_haar_density_example (k : U -> R) :
  continuous (k : U -> real_line_metric R) ->
  (forall u, KU u -> point_evaluation tt (fun y => k y * u y) = point_evaluation tt u) ->
  k = fun _ => 1.
Proof.
move=> hkc hk.
have [hGc _ hr] := one_point_group_lch_haar_example.
have hc1 : continuous ((fun _ : U => (1 : R)) : U -> real_line_metric R).
  by move=> x; exact: cvg_cst.
have h1 : forall u, KU u -> point_evaluation tt (fun y => 1 * u y) = point_evaluation tt u.
  by move=> u _; rewrite /point_evaluation mul1r.
exact (haar_integral_density_unique hGc hr hkc hc1 hk h1).
Qed.

(** Source for [one_point_group_haar_multiple_example]: regression for
    Federer 2.7.7, p. 125, "Any two left ... Haar integrals of G are
    constant positive multiples of each other": on the one-point group
    every left Haar integral is a positive multiple of evaluation at its
    point. *)
Example one_point_group_haar_multiple_example (lambda : (U -> R) -> R) :
  is_left_haar_integral umul lambda ->
  exists2 c : R, 0 < c & forall u, KU u -> lambda u = c * u tt.
Proof.
move=> hl; have [hGc hl0 _] := one_point_group_lch_haar_example.
exact (left_haar_integral_unique hGc hl hl0).
Qed.

(** Source for [zero_integral_not_haar_multiple_example]: regression
    for the word "Haar" in Federer 2.7.7, p. 125: the zero functional
    is a left invariant integral of the one-point group, but it is no
    positive multiple of the left Haar integral given by evaluation at
    its point; the condition "nonzero" of 2.7.2, p. 122, cannot be
    omitted. *)
Example zero_integral_not_haar_multiple_example :
  is_left_invariant_integral umul (fun _ : U -> R => 0) /\
  ~ exists2 c : R, 0 < c & forall u, KU u -> 0 = c * point_evaluation tt u.
Proof.
split.
  constructor; first exact (@daniell_integrals_zero R U KU).
  by move=> u g _; rewrite mulr0.
case=> c hc hu.
have := hu _ one_point_constant_compact; rewrite /point_evaluation mulr1=> h0.
by move: hc; rewrite -h0 ltxx.
Qed.

End HaarDensityExamples.

From Federer Require Import RealMetricBackground TopologicalGroupUP CompactSupportFunctionUP DaniellIntegralUP CovariantIntegralUP HaarIntegralUP InvariantIntegralPositivity ModularFunctionUP ModularFunction CovariantHaarCharacterisation.

(** Regression examples for Federer (1969), 2.7.8-2.7.9, pp. 126-127. Source
    context and proof conventions: ModularFunction.v and
    CovariantHaarCharacterisation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealMetricBackground TopologicalGroupUP CompactSupportFunctionUP
  DaniellIntegralUP CovariantIntegralUP HaarIntegralUP InvariantIntegralPositivity
  ModularFunctionUP ModularFunction CovariantHaarCharacterisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ModularFunctionExamples.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.
Local Notation K := (@compactly_supported_continuous_functions R G).

(** Source for [modular_character_right_invariant]: regression for
    Federer 2.7.9(3), p. 127, with chi = Delta_G: a Daniell integral nu
    on K(G) is left Delta_G covariant if and only if it is right
    invariant, because Delta_G Delta_G^{-1} = 1. For a right Haar
    integral nu this recovers 2.7.8(2), p. 126. *)
Example modular_character_right_invariant (Delta : G -> R) (nu : (G -> R) -> R) :
  is_modular_function mul inv Delta -> is_daniell_integral K nu ->
  is_left_covariant_integral mul Delta nu <-> is_right_invariant_integral mul inv nu.
Proof.
move=> hD hnu.
have [hM _] := modular_function_homomorphism hGc hD.
have hD0 g : Delta g != 0 by rewrite gt_eqF // (modular_function_positive hD).
have h := left_covariant_modular_characterisation hGc hnu hM hD0 (modular_function_continuous hD) hD.
rewrite (_ : (fun g => Delta g * (Delta g)^-1) = fun _ => 1) in h; last first.
  by apply: funext=> g; exact: (mulfV (hD0 g)).
exact: h.
Qed.

Hypothesis hcomm : forall g h, mul g h = mul h g.

(** Source for [commutative_modular_function_one]: regression for
    "Delta_G is uniquely characterized by each of these properties",
    Federer 2.7.8, p. 126, in the commutative case: there x g^{-1} =
    g^{-1} x, so every left Haar integral is right invariant, and the
    modular function is the constant 1. *)
Example commutative_modular_function_one (Delta : G -> R) :
  is_modular_function mul inv Delta -> Delta = fun _ => 1.
Proof.
move=> hD; apply: esym; apply: (modular_function_unique_left_haar hGc hD)=> lambda hl.
split; first exact: covariant_integral_daniell (nonzero_invariant_integral_invariant hl).
move=> u g hu; rewrite mul1r.
have -> : u \o right_multiplication_action mul inv g = u \o left_multiplication_action mul (inv g).
  by apply: funext=> x; rewrite /= /right_multiplication_action /left_multiplication_action hcomm.
exact: (invariant_integral_translate hl (inv g) hu).
Qed.

(** Source for [commutative_left_haar_inversion_invariant]: regression
    for Federer 2.7.8(3), p. 126, in the commutative case: with
    Delta_G = 1, lambda(u o p) = lambda(u) whenever lambda is a left
    Haar integral and u in K(G), p the inversion of G. *)
Example commutative_left_haar_inversion_invariant (lambda : (G -> R) -> R) (u : G -> R) :
  is_left_haar_integral mul lambda -> K u -> lambda (u \o inv) = lambda u.
Proof.
move=> hl hu; have [D hD] := modular_function_exists R hGc.
have h := modular_function_left_inversion hD hl hu.
rewrite (commutative_modular_function_one hD) in h.
rewrite -h; congr lambda; apply: funext=> x.
by rewrite /= mulr1.
Qed.

End ModularFunctionExamples.

From Federer Require Import TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP CompactSupportFunctionUP CompactSupportFunctionLattice HaarIntegralUP IsotropyGroupTopology CosetIntegralUP CosetIntegralLaws.
(** Regression examples for Federer (1969), 2.7.10, pp. 127–128. Source
    context and proof conventions: IsotropyGroupTopology.v,
    CosetIntegralUP.v and CosetIntegralLaws.v. *)
Section CosetIntegralExamples.
Variable R : realType.
Local Open Scope ring_scope.

(** Source for [left_multiplication_isotropy_example]: regression for
    the isotropy group G^x of Federer 2.7.1, p. 121, in the case
    2.7.2(1), p. 122, A(g,x) = gx, where 2.7.10, p. 127, applies with
    X = G: the isotropy group is G^x = {e}, since gx = x implies
    g = (gx)x^{-1} = e. *)
Example left_multiplication_isotropy_example (G : topologicalType) (mul : G -> G -> G)
    (inv : G -> G) (e : G) (x : G) :
  is_group_laws mul inv e -> isotropy_subgroup (left_multiplication_action mul) x = [set e].
Proof.
move=> hG; apply/seteqP; split=> g; rewrite /isotropy_subgroup /left_multiplication_action /=.
- by move=> h; rewrite -(group_mulgK hG x g) h (group_mulgV hG).
- by move=> ->; exact: group_mul1g hG x.
Qed.

(** Source for [coset_integral_trivial_isotropy_example]: regression
    for "(1) mu^x(u)(g x) = mu_s[u(g s)] whenever u in K(G), g in G",
    Federer 2.7.10, p. 127, in the boundary case where mu is the
    evaluation at the identity of G^x, as for the trivial isotropy group
    of left_multiplication_isotropy_example: then mu^x(u)(g x) = u(g). *)
Example coset_integral_trivial_isotropy_example (G X : topologicalType) (mul : G -> G -> G)
    (inv : G -> G) (e : G) (A : G -> X -> X) (x : X)
    (mulS : isotropy_subgroup A x -> isotropy_subgroup A x -> isotropy_subgroup A x)
    (invS : isotropy_subgroup A x -> isotropy_subgroup A x) (eS : isotropy_subgroup A x)
    (mu : (isotropy_subgroup A x -> R) -> R) (M : (G -> R) -> X -> R) (u : G -> R) (g : G) :
  is_group_laws mul inv e -> is_subgroup_restriction mul inv e (isotropy_subgroup A x) mulS invS eS ->
  (forall f, mu f = f eS) -> is_coset_integral mul A x mu M ->
  @compactly_supported_continuous_functions R G u -> M u (A g x) = u g.
Proof.
move=> hG hR hmu hM hu.
by rewrite (coset_integral_value hM g hu) hmu (subgroup_restriction_unit hR) (group_mulg1 hG).
Qed.

(** Source for [coset_integral_zero_example]: regression for "linear
    epimorphism", Federer 2.7.10, p. 127, at the zero function of K(G):
    mu^x(0) = 0, from the linearity with the scalar 0. *)
Example coset_integral_zero_example (G X : topologicalType) (mul : G -> G -> G)
    (inv : G -> G) (e : G) (A : G -> X -> X) (x : X)
    (mulS : isotropy_subgroup A x -> isotropy_subgroup A x -> isotropy_subgroup A x)
    (mu : (isotropy_subgroup A x -> R) -> R) (M : (G -> R) -> X -> R) :
  is_locally_compact_hausdorff_group mul inv e -> is_homogeneous_space mul A ->
  hausdorff_space X -> is_left_haar_integral mulS mu -> is_coset_integral mul A x mu M ->
  M (fun _ => 0) = (fun _ => 0).
Proof.
move=> hG hA hX hmu hM.
have h := coset_integral_scale hG hA hX hmu hM 0 (@compactly_supported_zero_function R G).
have e1 : (fun _ : G => 0 * (0 : R)) = (fun _ => 0) by apply: funext=> g; rewrite mul0r.
by move: h; rewrite e1=> ->; apply: funext=> y; rewrite mul0r.
Qed.

End CosetIntegralExamples.

From Federer Require Import RealMetricBackground TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP CompactSupportFunctionUP CovariantIntegralUP HaarIntegralUP GroupMultiplicationHomogeneous ModularFunctionUP ModularFunction IsotropyGroupTopology CosetSpaceUP CosetSpaceHomogeneous WeilCondition UnimodularGroupUP UnimodularGroups CosetSpaceInvariantIntegrals.
From mathcomp Require Import functions topology.
(** Regression examples for Federer (1969), 2.7.11–2.7.12, pp. 128–129.
    Source context and proof conventions: WeilCondition.v,
    UnimodularGroups.v and CosetSpaceInvariantIntegrals.v. *)
Section WeilConditionExamples.
Variable R : realType.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [left_multiplication_weil_example]: regression for
    Federer 2.7.11(1), p. 128, in the boundary case X = G with the
    action 2.7.2(1), p. 122, where G^x = {e}: Weil's condition reduces
    to chi(e) Delta_{G^x}(e) = Delta_G(e), which holds, so that every
    continuous homomorphism chi of G into R ~ {0} admits a nonzero left
    chi covariant integral on K(G), in accordance with 2.7.9(1),
    p. 126. *)
Example left_multiplication_weil_example (G : topologicalType) (mul : G -> G -> G) (inv : G -> G)
    (e : G) (chi : G -> R) (x : G) :
  is_locally_compact_hausdorff_group mul inv e ->
  (forall g h, chi (mul g h) = chi g * chi h) -> (forall g, chi g != 0) ->
  continuous (chi : G -> real_line_metric R) ->
  exists nu : (G -> R) -> R, is_left_covariant_integral mul chi nu /\
    exists2 v, @compactly_supported_continuous_functions R G v & nu v <> 0.
Proof.
move=> hG hchiM hchi0 hchic.
have hT := lch_group_topological hG; have hgl := topological_group_laws hT.
have hA := left_multiplication_homogeneous hT.
have hH := lch_group_hausdorff hG; have hl := lch_group_locally_compact hG.
have [mulS [invS [eS [hR hSG]]]] := isotropy_group_exists x hG hA hH.
have [DG hDG] := modular_function_exists R hG.
have [DS hDS] := modular_function_exists R hSG.
apply/(covariant_integral_exists_iff_weil hG hA hH hl hR hDG hDS hchiM hchi0 hchic)=> t.
have ht : set_val t = e.
  have h : mul (set_val t) x = x := set_valP t.
  by rewrite -(group_mulgK hgl x (set_val t)) h (group_mulgV hgl).
have -> : t = eS by apply: val_inj; rewrite -!set_valE ht (subgroup_restriction_unit hR).
have [_ hDS1] := modular_function_homomorphism hSG hDS.
have [_ hDG1] := modular_function_homomorphism hG hDG.
have hchi1 : chi e = 1.
  have h := hchiM e e; rewrite (group_mul1g hgl) -{1}[chi e]mulr1 in h.
  exact: esym (mulfI (hchi0 e) h).
by rewrite hDS1 (subgroup_restriction_unit hR) hDG1 hchi1 mulr1.
Qed.

(** Source for [trivial_subgroup_coset_invariant_integral_example]:
    regression for "For each closed subgroup S of G, ... G/S admits a
    nonzero invariant integral if and only if Delta_S = Delta_G | S",
    Federer 2.7.12, p. 129, in the boundary case S = {e}: both modular
    functions take the value 1 at e, so that G/{e} admits a nonzero
    invariant integral, as G itself does by 2.7.5, p. 125. *)
Example trivial_subgroup_coset_invariant_integral_example (G Q : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G) (pi : G -> Q) (A : G -> Q -> Q) :
  is_locally_compact_hausdorff_group mul inv e -> is_left_coset_space mul inv [set e] pi ->
  is_coset_action mul pi A ->
  exists nu : (Q -> R) -> R, is_invariant_integral A nu /\
    exists2 v, @compactly_supported_continuous_functions R Q v & nu v <> 0.
Proof.
move=> hG hQ hAc.
have hgl := topological_group_laws (lch_group_topological hG).
have hS : is_subgroup mul inv e [set e].
  split=> //=; first by move=> g h -> ->; exact: group_mul1g hgl e.
  by move=> g ->; exact: group_inv1 hgl.
have hSc : closed [set e] := compact_closed (lch_group_hausdorff hG) (@compact_set1 G e).
have [mulS [invS [eS hR]]] := subgroup_restriction_exists hS.
have hSG := subgroup_restriction_locally_compact_hausdorff hR hG hSc.
have [DG hDG] := modular_function_exists R hG.
have [DS hDS] := modular_function_exists R hSG.
apply/(coset_space_invariant_integral_iff hG hS hSc hQ hAc hR hDG hDS)=> t.
have ht : set_val t = e := set_valP t.
have -> : t = eS by apply: val_inj; rewrite -!set_valE ht (subgroup_restriction_unit hR).
have [_ hDS1] := modular_function_homomorphism hSG hDS.
have [_ hDG1] := modular_function_homomorphism hG hDG.
by rewrite hDS1 (subgroup_restriction_unit hR) hDG1.
Qed.

(** Source for [compact_group_modular_unit_example]: regression for
    "every compact group is unimodular" and its equivalence with
    "the modular function Delta_G is constant with value 1", Federer
    2.7.12, p. 129: the modular function of a compact group is 1. *)
Example compact_group_modular_unit_example (G : topologicalType) (mul : G -> G -> G)
    (inv : G -> G) (e : G) (D : G -> R) :
  is_locally_compact_hausdorff_group mul inv e -> compact [set: G] ->
  is_modular_function mul inv D -> forall g, D g = 1.
Proof.
move=> hG hc hD.
exact: ((unimodular_iff_modular_unit hG hD).1 (compact_group_unimodular hG hc)).
Qed.

End WeilConditionExamples.

From Federer Require Import MeasureAlmostBasic LatticeL1ApproximationLaws HomogeneousSpaceUP SummableIncreasingLimits CosetLoneIntegralUP CosetLoneIntegralLaws.
(** Regression examples for Federer (1969), 2.7.13, pp. 130–131. Source
    context and proof conventions: CosetLoneIntegralUP.v and
    CosetLoneIntegralLaws.v. *)
Section CosetLoneIntegralExamples.
Variable R : realType.
Variables G X : topologicalType.
Variables (mul : G -> G -> G) (A : G -> X -> X) (x : X).
Variables (alpha : set G -> \bar R) (beta : set (isotropy_subgroup A x) -> \bar R)
  (gamma : set X -> \bar R).
Hypotheses (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma).
Local Open Scope ring_scope.

(** Source for [coset_fibre_integral_zero_example]: regression for
    "beta^x(u)(g x) = integral u(g s) d beta s whenever g in G",
    Federer 2.7.13, p. 130, in the boundary case u = 0: the fibre
    formula with value 0 holds at every point of X, for every measure
    beta, also when the cosets are beta null. *)
Example coset_fibre_integral_zero_example (y : X) :
  coset_fibre_integral mul A x beta (fun _ => 0) y 0.
Proof. by move=> g _; have h := real_total_zero_integral hb; exact: h. Qed.

(** Source for [coset_lone_integral_null_modification_example]:
    regression for the reading "for gamma almost all points g x" of
    "beta^x(u)(g x) = integral u(g s) d beta s whenever g in G",
    Federer 2.7.13, p. 130: changing each beta^x(u) on a gamma null
    set preserves both laws, so beta^x(u) is a member of L_1(gamma)
    determined only up to gamma almost equality, and the fibre formula
    cannot be required at every point. *)
Example coset_lone_integral_null_modification_example (B B' : (G -> R) -> X -> R) :
  is_coset_lone_integral mul A x alpha beta gamma B ->
  (forall u, measure_almost_everywhere gamma [set y | B u y = B' u y]) ->
  is_coset_lone_integral mul A x alpha beta gamma B'.
Proof.
move=> hB hBB'; split.
- move=> u a hu; have h := coset_lone_integral_identity hB hu.
  have h' := summable_total_almost_equal_integral hc h (hBB' u); exact: h'.
- move=> u hu.
  apply: (measure_almost_everywhere_mono hc _ (measure_almost_everywhere_and hc
    (coset_lone_integral_fibre hB hu) (hBB' u)))=> y /= [h he].
  by rewrite -he.
Qed.

(** Source for [coset_lone_integral_zero_example]: regression for the
    linearity of beta^x, Federer 2.7.13, p. 130, at the zero function:
    beta^x(0) = 0 gamma almost everywhere. *)
Example coset_lone_integral_zero_example (B : (G -> R) -> X -> R) :
  is_homogeneous_space mul A -> is_coset_lone_integral mul A x alpha beta gamma B ->
  measure_almost_everywhere gamma [set y | B (fun _ => 0) y = 0].
Proof.
move=> hA hB.
have h0 : summable_real_functions alpha (fun _ : G => 0).
  by exists 0; have h := real_total_zero_integral ha; exact: h.
apply: (measure_almost_everywhere_mono hc _ (coset_lone_integral_fibre hB h0))=> y /= h.
exact (coset_fibre_integral_unique hA h (@coset_fibre_integral_zero_example y)).
Qed.

End CosetLoneIntegralExamples.

From Federer Require Import TopologicalGroupUP HomogeneousSpaceUP CovariantIntegralUP HaarIntegralUP RadonMeasureUP CovariantMeasureRadon HomogeneousCovariantMeasureRadon CovariantMeasureRadonCounterexample.

(** Regression examples for Federer (1969), 2.7.14–2.7.15, pp. 131–133.
    Source context and proof conventions: CovariantMeasureRadon.v,
    HomogeneousCovariantMeasureRadon.v and
    CovariantMeasureRadonCounterexample.v. *)
Section CovariantMeasureRadonExamples.
Variable R : realType.
Local Open Scope ring_scope.

(** Source for [covariant_radon_hypothesis_needed_example]: regression
    for the alternative hypothesis added to "Every left (right) chi
    covariant measure over G is a Radon measure", Federer 2.7.14,
    p. 131: on the uncountable discrete group of subsets of N the K(G)
    regular measure associated with the zero integral is a left
    invariant measure, satisfies neither alternative, and is not a
    Radon measure. *)
Example covariant_radon_hypothesis_needed_example :
  exists phi : set subset_group -> \bar R,
    [/\ is_left_invariant_measure subset_difference phi,
      ~ ((exists C, compact C /\ phi C <> 0%E) \/ is_sigma_compact_space subset_group) &
      ~ is_radon_measure phi].
Proof.
have [phi [hphi h0 hnr]] := @zero_left_invariant_measure_not_radon R.
exists phi; split=> //; case=> [[C [hC hCz]]|hs]; first exact: hCz (h0 C hC).
exact: subset_group_not_sigma_compact hs.
Qed.

(** Source for [compact_group_covariant_measure_radon_example]:
    regression for Federer 2.7.14, p. 131, for a compact group, where
    the added hypothesis holds trivially: every left chi covariant
    measure over a compact group is a Radon measure. *)
Example compact_group_covariant_measure_radon_example (G : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G) (chi : G -> R) (phi : set G -> \bar R) :
  is_locally_compact_hausdorff_group mul inv e -> compact [set: G] ->
  is_left_covariant_measure mul chi phi -> is_radon_measure phi.
Proof.
move=> hG hc hphi; apply: (left_covariant_measure_radon hG hphi); right.
by exists (fun _ => [set: G]); split=> // x _; exists 0%N.
Qed.

(** Source for [empty_space_covariant_measure_radon_example]:
    regression for Federer 2.7.15, p. 133, in the boundary case of an
    empty homogeneous space X: every chi covariant measure over X is a
    Radon measure, since X is the union of the empty sequence of compact
    sets. *)
Example empty_space_covariant_measure_radon_example (G X : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G) (A : G -> X -> X) (chi : G -> R)
    (gamma : set X -> \bar R) :
  is_locally_compact_hausdorff_group mul inv e -> is_homogeneous_space mul A ->
  hausdorff_space X -> locally_compact [set: X] -> (forall x : X, False) ->
  is_covariant_measure A chi gamma -> is_radon_measure gamma.
Proof.
move=> hG hA hX hlX hE hg; apply: (homogeneous_covariant_measure_radon hG hA hX hlX hg); right.
by exists (fun _ => set0); split=> [n|x _]; [exact: compact0|exfalso; exact: hE x].
Qed.

End CovariantMeasureRadonExamples.

From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerNormedTopology OrthonormalFamilies EuclideanLebesgueBoxes EuclideanLebesgueHaar EuclideanBallVolume EuclideanRectangularBox EuclideanSimplexVolume .

Section EuclideanHaarExamples.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lebesgue_zero_dimension_cube_example]: regression for
    the normalisation "L^n{x : 0 < x_i < 1 for i = 1, ..., n} = 1" of
    Federer 2.7.16, p. 134, at n = 0: the condition is vacuous, the
    cube is the whole one-point space R^0, and L^0 is the unit mass of
    2.6.5. *)
Example lebesgue_zero_dimension_cube_example (R : realType) :
  @euclidean_lebesgue_measure R 0 [set x | forall i, 0 < x i < 1] = 1%:E.
Proof. exact: euclidean_unit_cube. Qed.

(** Source for [lebesgue_zero_dimension_haar_example]: regression for
    "L^n is the ... Haar measure over R^n", Federer 2.7.16, p. 134, at
    n = 0: the unit mass is a left Haar measure of the trivial group
    R^0. *)
Example lebesgue_zero_dimension_haar_example (R : realType) :
  is_left_haar_measure (fun x y : inner_metric_space (@euclidean_inner_productP R 0) => x + y)
    (@euclidean_lebesgue_measure R 0).
Proof. exact: euclidean_lebesgue_left_haar. Qed.

(** Source for [unit_ball_volume_small_dimensions_example]: regression
    for Federer 2.7.16, p. 135, "Moreover alpha(1) = 2 ... We also define
    alpha(0) = 1": with L^0 the unit mass both values follow from the
    definition alpha(n) = L^n{x : |x| < 1}. *)
Example unit_ball_volume_small_dimensions_example (R : realType) :
  euclidean_unit_ball_volume R 0 = 1 /\ euclidean_unit_ball_volume R 1 = 2.
Proof. by split; [exact: euclidean_unit_ball_volume0|exact: euclidean_unit_ball_volume1]. Qed.

(** Source for [degenerate_rectangular_box_example]: regression for
    "The L^n measure of a rectangular box ... where c_i >= 0 ... equals
    the product c_1 ... c_n", Federer 2.7.16, p. 136: in positive
    dimension a box with all edges c_i = 0 is L^n null. *)
Example degenerate_rectangular_box_example (R : realType) n
    (a : inner_metric_space (@euclidean_inner_productP R n.+1)) (e : 'I_n.+1 -> R_n R n.+1) :
  orthonormal_family (@euclidean_inner_product R n.+1) e ->
  @euclidean_lebesgue_measure R n.+1
    [set x | forall i, 0 <= euclidean_inner_product (x - a) (e i) <= 0] = 0%:E.
Proof.
move=> he; rewrite (@euclidean_rectangular_box R n.+1 a (fun _ => 0) e) //.
by rewrite prodr_const card_ord expr0n.
Qed.

(** Source for [zero_dimension_rectangular_box_example]: regression for
    the same assertion of Federer 2.7.16, p. 136, at n = 0: the empty
    product of edge lengths is 1 and the box is the whole space R^0. *)
Example zero_dimension_rectangular_box_example (R : realType)
    (a : inner_metric_space (@euclidean_inner_productP R 0)) (e : 'I_0 -> R_n R 0) :
  orthonormal_family (@euclidean_inner_product R 0) e ->
  @euclidean_lebesgue_measure R 0
    [set x | forall i, 0 <= euclidean_inner_product (x - a) (e i) <= 0] = 1%:E.
Proof.
by move=> he; rewrite (@euclidean_rectangular_box R 0 a (fun _ => 0) e) // big_ord0.
Qed.

(** Source for [plane_standard_simplex_example]: regression for "using
    2.6.2, 2.9.20 one inductively computes ... = 1/n!", Federer 2.7.16,
    p. 136, at n = 2: the triangle {x : x_1, x_2 >= 0, x_1 + x_2 <= 1}
    has L^2 measure 1/2. *)
Example plane_standard_simplex_example (R : realType) :
  @euclidean_lebesgue_measure R 2 (@euclidean_standard_simplex R 2) = (2^-1)%:E.
Proof. by rewrite euclidean_standard_simplex_measure. Qed.

End EuclideanHaarExamples.

From Federer Require Import TopologicalGroupUP TopologicalGroupLaws MeasureUP MeasureBasic HaarIntegralUP InvariantMeasureTranslates CompactGroupNonmeasurable VitaliNonmeasurableSet.
(** Regression examples for Federer (1969), 2.7.17, p. 141. Source
    editions and proof conventions: CompactGroupNonmeasurable.v and
    VitaliNonmeasurableSet.v. *)
From mathcomp Require Import topology.
Section CompactGroupNonmeasurableExamples.
Local Open Scope ring_scope.

(** Source for [trivial_subgroup_transversal_measurable_example]:
    regression for the hypothesis "S is a countably infinite subgroup"
    of Federer 2.7.17, p. 141: the trivial subgroup {e} is finite, G
    has exactly one point in common with each left coset g{e} = {g},
    and G is measurable with respect to every measure over G. *)
Example trivial_subgroup_transversal_measurable_example (R : realType) (G : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G) :
  is_group_laws mul inv e ->
  [/\ is_subgroup mul inv e [set e], finite_set [set e],
    (forall g, exists! t, [set: G] t /\ left_coset mul g [set e] t) &
    forall phi : set G -> \bar R, is_measure phi -> measure_measurable phi [set: G]].
Proof.
move=> hG; split.
- constructor=> //.
  + by move=> g h -> ->; exact: (group_mul1g hG).
  + by move=> g ->; exact: (group_inv1 hG).
- exact: finite_set1.
- move=> g; exists g; split; first by split=> //; exists e=> //; exact: (group_mulg1 hG).
  by move=> t [_ [s -> <-]]; rewrite (group_mulg1 hG).
- by move=> phi hm C; rewrite setIT setDT (measure_empty hm) adde0.
Qed.

(** Source for [real_quotient_subgroups_example]: regression for
    Federer 2.7.17, p. 141, and its remark "Vitali (with G = R/Z,
    S = Q/Z)": for a left Haar measure phi of R/Z, a set meeting each
    coset of the countably infinite subgroup Q/Z in exactly one point is
    phi nonmeasurable, whereas R/Z itself meets each coset of the finite
    subgroup {0} in exactly one point and is phi measurable. *)
Example real_quotient_subgroups_example (R : realType) (Q : topologicalType) (pi : R -> Q)
    (qadd : Q -> Q -> Q) (qopp : Q -> Q) :
  is_real_integer_quotient_group pi qadd qopp ->
  exists phi : set Q -> \bar R, [/\ is_left_haar_measure qadd phi,
    exists T : set Q, (forall g, exists! t, T t /\ left_coset qadd g (pi @` @real_rationals R) t) /\
      ~ measure_measurable phi T,
    (forall g, exists! t, [set: Q] t /\ left_coset qadd g [set pi 0] t) &
    measure_measurable phi [set: Q]].
Proof.
move=> hQ; have [[phi hphi] [T [hT1 hT]]] := real_quotient_vitali_nonmeasurable hQ.
have [_ _ h1 h2] := trivial_subgroup_transversal_measurable_example R (real_quotient_group_laws hQ).
have [mu [_ hm _ _]] := hphi.
exists phi; split=> //; last exact: (h2 phi hm).
by exists T; split=> //; apply: hT; left.
Qed.

End CompactGroupNonmeasurableExamples.

From Federer Require Import RealMetricBackground FunctionLatticeRegularityUP MonotoneDaniellIntegralUP CompactSupportFunctionUP MeasureUP DaniellEmptyBoundary MeasureConullZeroIntegral RealIntegralFunctionalUP TotalScalarLpFiniteSeminorm RegularLatticeLoneDensity TopologicalGroupUP HomogeneousSpaceUP CovariantIntegralUP CovariantTranslationContinuity.

(** Regression examples for Federer (1969), 2.7.18, p. 141. Source context
    and proof conventions: CovariantMeasureImage.v and
    CovariantTranslationContinuity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology normedtype.
From Federer Require Import RealMetricBackground FunctionLatticeRegularityUP
  MonotoneDaniellIntegralUP CompactSupportFunctionUP MeasureUP DaniellEmptyBoundary
  MeasureConullZeroIntegral RealIntegralFunctionalUP TotalScalarLpFiniteSeminorm
  RegularLatticeLoneDensity TopologicalGroupUP HomogeneousSpaceUP CovariantIntegralUP
  CovariantTranslationContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CovariantTranslationExamples.
Variable R : realType.
Local Notation U := (discrete_topology unit).
Local Notation umul := (fun _ _ : U => (tt : U)).
Local Notation uinv := (fun x : U => x).
Local Notation uact := (fun (_ : U) (x : U) => x).

(** Source for [zero_measure_translation_example]: regression for
    Federer 2.7.18, p. 141, in the case mu = 0 excluded from the
    continuity of chi in 2.7.1, p. 122. On the one-point group acting
    on itself, the zero measure is the K(X) regular measure associated
    with the zero integral, which is chi covariant for chi = 0; this
    chi is not a homomorphism into R ~ {0}, so that the printed step
    "chi(g) -> chi(h)" has no content, but the conclusion of 2.7.18
    holds and covariant_translation_continuity applies. *)
Example zero_measure_translation_example :
  let chi := fun _ : U => (0 : R) in
  let gamma := fun _ : set U => (0 : \bar R) in
  [/\ is_covariant_measure uact chi gamma, chi tt <> 1 &
    ((fun g : U => finite_total_scalar_lp_norm gamma 1 (fun x => (fun _ : U => (1 : R)) (uact g x) -
      (fun _ : U => (1 : R)) (uact tt x))) @ (tt : U) --> (0 : R))].
Proof.
move=> chi gamma.
have hcst (T : topologicalType) (c : R) : continuous ((fun _ : T => c) : T -> real_line_metric R).
  by move=> x; exact: cvg_cst.
have hsupp : real_function_support (fun _ : U => (1 : R)) = [set (tt : U)].
  apply/seteqP; split=> x; first by case: x.
  move=> _; rewrite /real_function_support.
  by apply: (@subset_closure U [set y : U | (1 : R) <> 0]); apply/eqP; exact: oner_neq0.
have hK : @compactly_supported_continuous_functions R U (fun _ => 1).
  by split; [exact: hcst|rewrite hsupp; exact: compact_set1].
have hm : is_measure gamma := @daniell_zero_measure R U.
have hi : is_real_integral_functional gamma (@compactly_supported_continuous_functions R U)
    (fun _ => 0).
  by move=> f _; exact: (measure_almost_zero_integral hm).
have hmono : is_monotone_daniell_integral (@compactly_supported_continuous_functions R U)
    (fun _ => 0).
  constructor.
  - by move=> f g _ _; rewrite addr0.
  - by move=> c f _ _; rewrite mulr0.
  - by move=> f g _ _ _.
  - move=> f g _ _ _; split; first by move=> n m _.
    by split=> [a ha|b hb]; exists 0%N.
have hr : is_function_lattice_regular (@compactly_supported_continuous_functions R U) gamma.
  move=> S; split=> _; last exact: ltry.
  exists setT; split; first exact: subsetT.
  split; last by split; [|exact: ltry].
  exists (fun _ => setT); split.
    move=> n; exists (fun _ => [set x : U | 2^-1 < (fun _ : U => (1 : R)) x]); split.
      move=> m; exists (fun _ => 1), 2^-1; split; first by split=> // x; exact: ler01.
      by split; [rewrite invr_gt0 ltr0n|].
    split; first by move=> m k _.
    apply/seteqP; split=> x // _; exists 0%N=> //=.
    by rewrite invf_lt1 ?ltr0n // ltr1n.
  split; first by move=> n m _.
  split; first exact: ltry.
  by apply/seteqP; split=> // x _ n _.
have hcov : is_covariant_measure uact chi gamma.
  exists (fun _ => 0); split; [exact: hmono|by move=> u g _; rewrite mul0r|exact: hm|exact: hi|].
  exact: hr.
split=> //; first by move/eqP; rewrite eq_sym oner_eq0.
have hT : is_topological_group umul uinv (tt : U).
  constructor; [by constructor=> // g; case: g|by move=> p; exact: cvg_cst|by move=> x; exact: cvg_id].
have hA : is_homogeneous_space umul uact.
  constructor.
  - by move=> p; exact: cvg_snd.
  - by [].
  - by move=> x V _; exact: discrete_open.
  - by move=> x; apply/seteqP; split=> // y _; exists tt=> //; case: x; case: y.
have hlc : locally_compact [set: U].
  move=> x _; exists setT; first exact: filterT.
  by split; [rewrite (_ : setT = [set (tt : U)]); [exact: compact_set1|apply/seteqP; split=> -[]]|].
have hv := represented_lattice_in_total_lone hm hi hK.
have [_ _ hlim] := covariant_translation_continuity hT hA hlc discrete_hausdorff hlc (tt : U) hcov hv.
exact: hlim.
Qed.

End CovariantTranslationExamples.

From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerMetric InnerNormedTopology LinearBasis Hom HomInner AffineMaps TopologicalGroupUP IsotropyGroupTopology HomogeneousSpaceUP CovariantIntegralUP HomSpaceTopology LinearGroupTopology LinearGroupSealed GeneralLinearPunctured SpecialLinearTopology OrthogonalGroupTopology AffineGroupTopology PuncturedLebesgueCovariance .
From mathcomp Require Import topology.

Section TopologicalLinearGroupExamples.
Local Open Scope ring_scope.

(** Source for [linear_group_zero_dimension_example]: regression for
    "the automorphisms form a dense open subset of Hom(V, V), called the
    linear group of V", Federer 2.7.16, p. 134, at dim V = 0: every
    member of Hom(R^0, R^0) is univalent, so the linear group is the
    whole one-point space. *)
Example linear_group_zero_dimension_example (R : realType)
    (f : inner_metric_space (hom_inner_productP (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R 0) (@coordinate_basisP R 0))) :
  linear_group (@euclidean_inner_productP R 0) (@coordinate_basisP R 0) f.
Proof. by move=> x y _; rewrite (coordinate_zero x) (coordinate_zero y). Qed.

(** Source for [orthogonal_group_unit_example]: regression for "the
    orthogonal group O(n) is a compact subset of Hom(R^n, R^n)", Federer
    2.7.16, p. 139: the identity 1_V of the linear group belongs to
    O(V) for every V. *)
Example orthogonal_group_unit_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) :
  orthogonal_group hB hb (linear_group_unit hB hb).
Proof. exact: (subgroup_unit (orthogonal_group_subgroup hB hb)). Qed.

(** Source for [punctured_line_covariant_example]: regression for
    "a transitive action results through replacement of R^n by
    R^n ~ {0}, which really does not matter because L^n{0} = 0", Federer
    2.7.16, p. 135, at n = 1: L^1 restricted to R ~ {0} is |det|^{-1}
    covariant for GL(1, R). *)
Example punctured_line_covariant_example (R : realType) :
  is_covariant_measure (@punctured_linear_action R 1) (fun g => `|general_linear_det g|^-1)
    (@punctured_lebesgue R 0).
Proof. exact: punctured_lebesgue_covariant. Qed.

(** Source for [special_linear_plane_homogeneous_example]: regression
    for "In case n >= 2 the special linear group SL(n, R) ... acts
    transitively on R^n ~ {0}", Federer 2.7.16, p. 135, at the smallest
    dimension n = 2: R^2 ~ {0} is a homogeneous space of SL(2, R). *)
Example special_linear_plane_homogeneous_example (R : realType) :
  exists mulS invS eS,
    is_subgroup_restriction (linear_group_mul (@euclidean_inner_productP R 2) (@coordinate_basisP R 2))
      (linear_group_inv (@euclidean_inner_productP R 2) (@coordinate_basisP R 2))
      (linear_group_unit (@euclidean_inner_productP R 2) (@coordinate_basisP R 2))
      (@special_linear R 2) mulS invS eS /\
    is_homogeneous_space mulS (@special_linear_punctured_action R 2).
Proof.
have [mulS [invS [eS hS]]] := @special_linear_restriction_exists R 2.
exists mulS, invS, eS; split=> //.
exact: (@special_linear_punctured_homogeneous R 0 mulS invS eS hS).
Qed.

(** Source for [isometry_translation_example]: regression for
    "G = A(V, V) cap {g : L(g) in O(n)} = im tau o O(n)", Federer 2.7.16,
    p. 140, example (7), for the translations: (1_V, z) belongs to the
    isometry group and corresponds to tau_z. *)
Example isometry_translation_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) (z : V) :
  isometry_group hB hb (linear_group_unit hB hb, z) /\
  affine_group_map hB hb (linear_group_unit hB hb, z) = affine_translation z.
Proof.
split; first exact: orthogonal_group_unit_example.
apply: funext=> v; rewrite /affine_group_map /affine_translation /=.
by rewrite (linear_group_unitE (linear_group_operations hB hb)).
Qed.

End TopologicalLinearGroupExamples.

From Federer Require Import MeasureUP MeasureBasic CovariantIntegralUP FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection OrthogonalMaps OrthonormalFamilies HomInner OrthogonalInjectionSpaces CompactGroupHomogeneousMeasures EuclideanOrthogonalInvariantMeasures .
From mathcomp Require Import topology.

Section OrthogonalInvariantMeasureExamples.

(** Source for [euclidean_orthogonal_injections_empty_example]:
    regression for "theta_{n,m} over O(n, m)", Federer 2.7.16, p. 139,
    with the convention n >= m of 1.7.2, p. 28: for n < m the set
    O(n, m) of orthogonal injections of R^m into R^n is empty, since the
    images of the standard basis would be m orthonormal vectors of
    R^n. *)
Example euclidean_orthogonal_injections_empty_example (R : realType) (n m : nat) :
  (n < m)%N -> forall f, ~ euclidean_orthogonal_injections R n m f.
Proof.
move=> hnm f hf.
have he : orthonormal_family (@euclidean_inner_product R m) (@coordinate_basis R m).
  move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE.
  by rewrite eq_sym.
have ho := orthogonal_map_orthonormal hf he.
have := orthonormal_dimension_bound (@euclidean_inner_productP R n) (@coordinate_basisP R n) ho.
by rewrite leqNgt hnm.
Qed.

(** Source for [euclidean_theta_nm_dimension_example]: regression for
    the hypothesis m <= n of euclidean_theta_nm_exists_unique, "theta_{n,m}
    over O(n, m)", Federer 2.7.16, p. 139: for n < m no measure over
    O(n, m) has total measure 1, because O(n, m) is empty. *)
Example euclidean_theta_nm_dimension_example (R : realType) (n m : nat)
    (phi : set (set_type (euclidean_orthogonal_injections R n m)) -> \bar R) :
  (n < m)%N -> is_measure phi -> phi [set: set_type (euclidean_orthogonal_injections R n m)] <> 1%E.
Proof.
move=> hnm hm; have -> : [set: set_type (euclidean_orthogonal_injections R n m)] = set0.
  apply/seteqP; split=> // f _.
  exact: (euclidean_orthogonal_injections_empty_example hnm (set_valP f)).
by rewrite (measure_empty hm)=> /eqP; rewrite eq_sym (@eqe R) oner_eq0.
Qed.

(** Source for [normalised_invariant_measure_point_example]: regression
    for the point x_0 in normalised_invariant_measure_exists, "the
    measure (A^x)_# theta_n over X is invariant with
    [(A^x)_# theta_n] X = 1", Federer 2.7.16, p. 139: a space carrying
    an invariant measure of total measure 1 is nonempty. *)
Example normalised_invariant_measure_point_example (R : realType) (G : Type) (X : topologicalType)
    (A : G -> X -> X) (phi : set X -> \bar R) :
  is_normalised_invariant_measure A phi -> exists x : X, True.
Proof.
move=> [[nu [_ _ hm _ _]] h1]; apply: contrapT=> hn; move: h1.
have -> : [set: X] = set0 by apply/seteqP; split=> // y _; apply: hn; exists y.
by rewrite (measure_empty hm)=> /eqP; rewrite eq_sym (@eqe R) oner_eq0.
Qed.

End OrthogonalInvariantMeasureExamples.

From Federer Require Import InnerProductUP InnerMetric LinearBasis Annihilator Hom HomInner CovariantIntegralUP HaarIntegralUP UnimodularGroupUP ExteriorDeterminant EuclideanLinearMaps EuclideanInnerProduct FiniteCoordinates HomSpaceTopology LinearGroupTopology LinearGroupSealed HomCompositionDeterminant HomHaarCovariance HomMonomorphisms LinearGroupUnimodular .
From mathcomp Require Import topology.

Section HomHaarExamples.
Local Open Scope ring_scope.

(** Source for [hom_left_composition_det_zero_example]: regression for
    the determinant (det g)^m of f |-> g o f behind "phi is |det|^{-m}
    covariant", Federer 2.7.16, p. 136, at m = dim U = 0: the
    determinant is 1. *)
Example hom_left_composition_det_zero_example (R : realType) (U V : lmodType R)
    (c : 'I_0 -> U) (hc : is_basis c) n (b : 'I_n -> V) (hb : is_basis b) (g : Hom V V) :
  det (euclidean_two_nonzero R) (hom_rank_one_baseP hc hb) (hom_left_composition U g) = 1.
Proof. by rewrite (hom_left_composition_det (euclidean_two_nonzero R) hc hb g) expr0. Qed.

(** Source for [hom_haar_zero_source_invariant_example]: regression for
    "If phi is a Haar measure of the additive group of X, then phi is
    |det|^{-m} covariant with respect to the action of G", Federer
    2.7.16, p. 136, at m = dim U = 0: the Haar integrals of X are
    invariant under G. *)
Example hom_haar_zero_source_invariant_example (R : realType) (U V : lmodType R)
    (C : U -> U -> R) (hC : is_inner_product C) (c : 'I_0 -> U) (hc : is_basis c)
    (B : V -> V -> R) (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b)
    (mu : (inner_metric_space (hom_inner_productP hC hB hc) -> R) -> R) :
  is_left_haar_integral (fun f g : inner_metric_space (hom_inner_productP hC hB hc) => f + g) mu ->
  is_invariant_integral (hom_linear_group_action hC hc hB hb) mu.
Proof.
move=> hmu; have h := hom_haar_integral_covariant hC hc hB hb hmu.
have he : (fun g => `|linear_group_det hB hb g| ^- 0) = (fun _ => 1).
  by apply: funext=> g; rewrite expr0 invr1.
by rewrite he in h.
Qed.

(** Source for [hom_monomorphisms_zero_source_example]: regression for
    "the monomorphisms form an open subset of X whose complement has phi
    measure 0", Federer 2.7.16, p. 136, at m = dim U = 0: every member of
    Hom(U, V) is univalent, so the complement is empty. *)
Example hom_monomorphisms_zero_source_example (R : realType) (U V : lmodType R)
    (C : U -> U -> R) (hC : is_inner_product C) (c : 'I_0 -> U) (hc : is_basis c)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : inner_metric_space (hom_inner_productP hC hB hc)) :
  hom_monomorphisms hC hc hB f.
Proof.
move=> x y _.
by rewrite (basis_vector_expansion hc x) (basis_vector_expansion hc y) !big_ord0.
Qed.

(** Source for [linear_group_line_unimodular_example]: regression for
    "We conclude that Delta_G = 1, G is unimodular", Federer 2.7.16,
    p. 137, at the smallest nontrivial dimension n = 1, where
    GL(1, R) is commutative. *)
Example linear_group_line_unimodular_example (R : realType) :
  is_unimodular R (linear_group_mul (@euclidean_inner_productP R 1) (@coordinate_basisP R 1))
    (linear_group_inv (@euclidean_inner_productP R 1) (@coordinate_basisP R 1)).
Proof. exact: euclidean_linear_group_unimodular. Qed.

End HomHaarExamples.

From Federer Require Import MeasureUP MeasureBasic CovariantIntegralUP FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct CoordinateProjection OrthogonalMaps OrthonormalFamilies InnerProductUP HomInner AdjointUP OrthogonalInjectionSpaces CompactGroupHomogeneousMeasures EuclideanOrthogonalInvariantMeasures DaniellSpaceCompactSpace RealPower ExteriorGrading ExteriorMaps FiniteExteriorPowers ExteriorNorm AssociatedSubspace SimpleElementary ExteriorNormNaturality ExtendedPositivePower OrthogonalProjectionConstants ProjectionConstantNorms .
From mathcomp Require Import topology.

Section ProjectionConstantExamples.

(** Source for [projection_constant_degree_zero_example]: regression
    for "a positive number beta_t(n, m) such that (int |(Lambda_m p)
    xi|^t dtheta*_{n,m} p)^{1/t} = beta_t(n, m) . |xi|", Federer 2.7.16,
    p. 139, at the boundary m = 0 admitted by projection_constant_exists:
    Lambda_0 p is the identity of the scalars and the only simple
    0-vector is 1, so beta_t(n, 0) = 1. *)
Example projection_constant_degree_zero_example (R : realType) (h2 : ((1 + 1 : R) != 0)%R) (t : R) n :
  (0 < t)%R -> is_projection_constant h2 t n 0 1.
Proof.
move=> ht; split; first exact: ltr01.
move=> mulS invS eS hS phi hphi xi hs.
have [nu [hnu hrep hm hnu1]] := normalised_invariant_measure_integral hphi.
have hunit (V : lmodType R) (B : V -> V -> R) (hB : is_inner_product B) (y : exterior_power V 0) :
    simple y -> exterior_norm h2 hB y = 1%R.
  by move=> [s ->]; rewrite tuple_product; apply: orthonormal_product_unit_norm; move=> [].
have hF : (fun p => real_power (projection_norm h2 xi p) t) = (fun _ => 1%R).
  apply: funext=> p; rewrite /projection_norm hunit ?real_power_one_base //.
  exact: exterior_power_map_simple.
rewrite hF; exists (nu (fun _ => 1%R))%:E.
  exact: hrep _ (compact_space_constant_one R (projection_space_compact hS)).
by rewrite hnu1 /= real_power_one_base hunit ?mulr1.
Qed.

(** Source for [projection_constant_vacuous_example]: regression for
    the hypothesis m <= n of projection_constant_unique, "Whenever n >= m
    are positive integers", Federer 2.7.16, p. 139: for n < m the space
    O*(n, m) is empty, no measure over it has total measure 1, and every
    positive number satisfies is_projection_constant. *)
Example projection_constant_vacuous_example (R : realType) (h2 : ((1 + 1 : R) != 0)%R) (t b : R) n m :
  (n < m)%N -> (0 < b)%R -> is_projection_constant h2 t n m b.
Proof.
move=> hnm hb; split=> // mulS invS eS hS phi [[nu [_ _ hm _ _]] h1] xi hs; exfalso.
have hemp : [set: set_type (euclidean_orthogonal_projections R n m)] = set0.
  apply/seteqP; split=> // p _.
  have [h [hh _]] := orthogonal_projection_map_projection p.
  have he : orthonormal_family (@euclidean_inner_product R m) (@coordinate_basis R m).
    move=> i j; rewrite euclidean_inner_basis /coordinate_basis ffunE.
    by rewrite eq_sym.
  have ho := orthogonal_map_orthonormal hh he.
  have := orthonormal_dimension_bound (@euclidean_inner_productP R n) (@coordinate_basisP R n) ho.
  by rewrite leqNgt hnm.
by move: h1; rewrite hemp (measure_empty hm)=> /eqP; rewrite eq_sym (@eqe R) oner_eq0.
Qed.

(** Source for [projection_constant_infinity_example]: regression for
    "We also define beta_oo(n, m) = 1", Federer 2.7.16, p. 140: the
    extended constant at t = oo is exactly 1. *)
Example projection_constant_infinity_example (R : realType) (h2 : ((1 + 1 : R) != 0)%R) n m (b : R) :
  is_extended_projection_constant h2 +oo n m b <-> b = 1%R.
Proof. by []. Qed.

End ProjectionConstantExamples.

From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis Hom HomInner GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct OrthogonalMaps HomSpaceTopology LinearGroupTopology OrthogonalGroupTopology OrthogonalGroupHaarMeasure OrthogonalInjectionSpaces AffineGroupTopology IsometryGroupStructure AffineSubspaceSpace OrthogonalProjectionFibres AffineSubspaceParametrisation .
From mathcomp Require Import topology.

Section AffineSubspaceExamples.

(** Source for [affine_linear_subspace_distance_example]: regression for
    "delta(W) = distance(W, 0)", Federer 2.7.16, p. 140: a vector
    subspace W, as the point tau_0 W of the space of m dimensional affine
    subspaces, has distance 0 from the origin. *)
Example affine_linear_subspace_distance_example (R : realType) (U V : lmodType R)
    (C : U -> U -> R) (B : V -> V -> R) (hC : is_inner_product C) (hB : is_inner_product B)
    (m : nat) (c : 'I_m -> U) (hc : is_basis c) (W : G V m) :
  affine_origin_distance hC hB hc (affine_subspace_of 0%R W) = 0%R.
Proof.
apply/eqP; rewrite eq_le; apply/andP; split.
- have h := @affine_origin_distance_least R U V C B hC hB m c hc (affine_subspace_of 0%R W) 0%R
    (affine_coset_base (0%R : V) W).
  by rewrite inner_norm0 in h.
- exact: inner_norm_nonnegative.
Qed.

(** Source for [isometry_translation_origin_example]: regression for
    "G = im tau o O(n)", Federer 2.7.16, p. 140: tau_z o s maps 0 to z. *)
Example isometry_translation_origin_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) (n : nat) (b : 'I_n -> V) (hb : is_basis b)
    (s : orthogonal_group hB hb) (z : inner_metric_space hB) :
  isometry_map (isometry_of s z) 0%R = z.
Proof. by rewrite isometry_map_zero isometry_of_translation. Qed.

(** Source for [projection_fibre_origin_example]: regression for
    "p^{-1}{y} = tau_{p*(y)} ker p", Federer 2.7.16, p. 140: the fibre of
    p over 0 contains the origin, so that it is ker p. *)
Example projection_fibre_origin_example (R : realType) (n m : nat) (hmn : (m <= n)%N)
    (p : set_type (orthogonal_projections (@euclidean_inner_productP R (n - m))
      (@euclidean_inner_productP R n) (@coordinate_basisP R n))) :
  affine_points (projection_fibre hmn p 0%R) 0%R.
Proof.
apply/projection_fibreE.
exact: (linear0 (hom_as_linear (orthogonal_projection_map p))).
Qed.

(** Source for [affine_parametrisation_zero_example]: regression for
    "(delta o xi)(s, y) = |y|", Federer 2.7.16, p. 140: the subspaces
    xi(s, 0) = s[ker p] pass through the origin. *)
Example affine_parametrisation_zero_example (R : realType) (n m : nat) (hmn : (m <= n)%N)
    (p : set_type (orthogonal_projections (@euclidean_inner_productP R (n - m))
      (@euclidean_inner_productP R n) (@coordinate_basisP R n)))
    (s : orthogonal_group (@euclidean_inner_productP R n) (@coordinate_basisP R n)) :
  affine_origin_distance (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    (@coordinate_basisP R m) (affine_parametrisation hmn p (s, 0%R)) = 0%R.
Proof. by rewrite affine_parametrisation_distance inner_norm0. Qed.

End AffineSubspaceExamples.

From Federer Require Import InnerProductUP InnerMetric LinearBasis FiniteDualDimension Annihilator ModuleQuotient SubspaceCarrier GrassmannSubspaces Hom HomInner ExteriorDeterminant EuclideanLinearMaps EuclideanInnerProduct FiniteCoordinates HaarIntegralUP ModularFunctionUP UnimodularGroupUP IsotropyGroupTopology HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance SubspaceStabiliser StabiliserHomSpace StabiliserHomDecomposition StabiliserHaarCovariance StabiliserModularFunction .
From mathcomp Require Import topology.

Section SubspaceStabiliserExamples.
Local Open Scope ring_scope.

(** Source for [stabiliser_zero_dimensional_det_example]: regression for
    "det(g|W)" in Federer 2.7.16, p. 137, at the boundary dim W = 0
    excluded there by 0 < m: every endomorphism of a zero dimensional
    space has determinant 1 (1.3.4, p. 16, wedge_0 is the identity). *)
Example stabiliser_zero_dimensional_det_example (R : realType) (U : lmodType R)
    (c : 'I_0 -> U) (hc : is_basis c) (f : {linear U -> U}) :
  det (euclidean_two_nonzero R) hc f = 1.
Proof.
rewrite (det_scalar_map (euclidean_two_nonzero R) hc (c := 1)) ?expr0 // => v.
by rewrite (basis_vector_expansion hc v) !big_ord0 linear0 scaler0.
Qed.

(** Source for [stabiliser_zero_dimensional_modular_example]:
    regression for "Delta_G(g) = |det(g|W)|^{-n} . |det g|^m", Federer
    2.7.16, p. 138, at the boundary m = 0 excluded by 0 < m: the formula
    gives Delta_G = 1, the value for the linear group of (2). *)
Example stabiliser_zero_dimensional_modular_example (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b)
    (W : ModuleQuotient.subspace V) (hW : grassmann_pred 0 W) mulS invS eS :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb W) mulS invS eS ->
  forall Delta : _ -> R, is_modular_function mulS invS Delta -> forall g, Delta g = 1.
Proof.
move=> hS Delta hD g; rewrite (subspace_stabiliser_modular hW hS hD) expr0 mulr1.
have [w hw] := hW.
rewrite (stabiliser_restriction_detE hW hw) stabiliser_zero_dimensional_det_example.
by rewrite normr1 expr1n invr1.
Qed.

(** Source for [stabiliser_scalar_modular_example]: regression for the
    exponents of "Delta_G(g) = |det(g|W)|^{-n} . |det g|^m", Federer
    2.7.16, p. 138: the scalar map 2 1_V belongs to G, has
    det(2 1_V|W) = 2^m and det(2 1_V) = 2^n, and Delta_G(2 1_V) =
    2^{-mn} 2^{nm} = 1, as for every central member. *)
Example stabiliser_scalar_modular_example (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b)
    (W : ModuleQuotient.subspace V) m (hW : grassmann_pred m W) mulS invS eS :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb W) mulS invS eS ->
  forall Delta : _ -> R, is_modular_function mulS invS Delta ->
  exists t, stabiliser_det t = (1 + 1) ^+ n /\ Delta t = 1.
Proof.
move=> hS Delta hD.
have h2 : (1 + 1 : R) != 0 := euclidean_two_nonzero R.
have [t [ht1 ht2]] := stabiliser_scaling_exists hB hb hW h2 h2.
have [w hw] := hW.
have hmn := subspace_dimension_le hb hw.
have hdet : stabiliser_det t = (1 + 1) ^+ n by rewrite ht2 -exprD subnKC.
exists t; split=> //.
rewrite (subspace_stabiliser_modular hW hS hD) ht1 hdet.
have hp : `|(1 + 1 : R)| = 1 + 1 by rewrite ger0_norm // addr_ge0 ?ler01.
rewrite !normrX hp -!exprM mulnC mulVf // expf_neq0 //.
Qed.

(** Source for [stabiliser_decomposition_identity_example]: regression
    for "xi(f) = (f|W, f|Z) whenever f in X", Federer 2.7.16, p. 137, at
    f = 1_V: the second component of xi(1_V) is the inclusion of Z into
    V. *)
Example stabiliser_decomposition_identity_example (R : realType) (V : lmodType R)
    (W : ModuleQuotient.subspace V) m q (e : 'I_(m + q) -> V) (heb : is_basis e)
    (hid : preserving_pred W (hom_identity V)) (z : subspace_space (adapted_complement heb)) :
  (subspace_decomposition heb (@subspace_lift R (Hom V V) (subspace_preserving_maps W) _ hid)).2 z =
    subspace_val z.
Proof. by []. Qed.

End SubspaceStabiliserExamples.

From Federer Require Import RealNormUP NormMetric InnerProductUP InnerMetric LinearBasis Hom HomInner FiniteCoordinates EuclideanInnerProduct HomSpaceTopology LinearGroupTopology TopologicalGroupUP AffineMapSpaceUP AffineMapSpaceSealed AffineMapSpaceTopology FiniteNormEquivalence HomSpaceNormTopology .
From mathcomp Require Import topology.

Section AffineMapSpaceExamples.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [affine_maps_line_dimension_example]: regression for
    "If dim V < oo, then dim A(V, V) < oo", Federer 2.7.16, p. 134, at
    dim V = 1: A(R, R) has a base of 1 . 1 + 1 = 2 members, the maps
    v |-> c v and the constants. *)
Example affine_maps_line_dimension_example (R : realType) :
  exists u : 'I_2 -> affine_maps (coordinate_space R 1) (coordinate_space R 1), is_basis u.
Proof. exact: (affine_maps_finite_dimensional (@coordinate_basisP R 1) (@coordinate_basisP R 1)). Qed.

(** Source for [affine_group_zero_dimension_example]: regression for
    "the affine group of V, the open dense subset of univalent maps in
    A(V, V)", Federer 2.7.16, p. 134, at dim V = 0: every map of the
    one-point space R^0 is univalent, so the affine group is the whole
    of A(R^0, R^0), for any norm. *)
Example affine_group_zero_dimension_example (R : realType)
    (N : affine_maps (coordinate_space R 0) (coordinate_space R 0) -> R) (hN : is_real_norm N) :
  @affine_space_group R (coordinate_space R 0) _ affine_map_eval N hN = setT.
Proof.
apply/seteqP; split=> // f _ x y _.
by rewrite (coordinate_zero x) (coordinate_zero y).
Qed.

(** Source for [affine_translation_group_example]: regression for
    "im tau = {f : L(f) = 1_V}" and "the affine group of V ... equals
    L^{-1}(linear group of V)", Federer 2.7.16, p. 134: every translation
    tau_z = M^{-1}(1_V, z) belongs to the affine group, for any norm. *)
Example affine_translation_group_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) (n : nat) (b : 'I_n -> V) (hb : is_basis b)
    (N : affine_maps V V -> R) (hN : is_real_norm N) (z : V) :
  @affine_space_group R V _ affine_map_eval N hN
    (affine_space_iso_inv affine_mapsP (hom_identity V, z)).
Proof.
rewrite (affine_space_groupE hB hb affine_mapsP hN) /= affine_space_hom_onto.
exact: linear_group_identity.
Qed.

(** Source for [affine_translation_composition_example]: regression for
    "tau ... transforms vector addition into composition of maps",
    Federer 2.7.16, pp. 133–134, through M(f o g) = (L(f) o L(g),
    f(0) + L(f)(g(0))): M(tau_z o tau_w) = (1_V, z + w) for every
    composition operation of A(V, V). *)
Example affine_translation_composition_example (R : realType) (V : lmodType R)
    (comp : affine_maps V V -> affine_maps V V -> affine_maps V V)
    (hc : is_affine_composition affine_map_eval comp) (z w : V) :
  affine_space_iso affine_mapsP
    (comp (affine_space_iso_inv affine_mapsP (hom_identity V, z))
      (affine_space_iso_inv affine_mapsP (hom_identity V, w))) = (hom_identity V, z + w).
Proof.
rewrite (affine_space_iso_comp affine_mapsP hc) !affine_space_hom_onto !affine_space_iso_inv_zero.
congr pair.
by apply: (@hom_ext R V V)=> v; rewrite hom_compE.
Qed.

(** Source for [affine_group_lch_example]: regression for "It should be
    clear from the preceding remarks that the topological assumptions of
    our general theory are satisfied", Federer 2.7.16, p. 134, for the
    affine group of V inside the sealed space A(V, V), normed by
    |L(f)| + |f(0)|: it carries the structure of a locally compact
    Hausdorff topological group. *)
Example affine_group_lch_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) (n : nat) (b : 'I_n -> V) (hb : is_basis b) :
  exists mul inv e, @is_locally_compact_hausdorff_group
    (set_type (@affine_space_group R V (affine_maps V V) affine_map_eval _
      (affine_space_reference_normP hB hb affine_mapsP))) mul inv e.
Proof.
have [mulS [invS [eS hS]]] := affine_group_structure_exists hB hb affine_mapsP
  (affine_space_reference_normP hB hb affine_mapsP).
by exists mulS, invS, eS; exact: (affine_space_group_lch hB hb affine_mapsP hS).
Qed.

(** Source for [hom_zero_dimension_norm_example]: regression for "all
    norms ... induce the same ... topology. In particular we can ...
    norm Hom(V, V) as in 1.7.6", Federer 2.7.16, p. 134, at dim V = 0:
    the operator norm of Hom(R^0, R^0) induces the topology of 1.7.9, in
    which every set containing the only point 0 is a neighbourhood. *)
Example hom_zero_dimension_norm_example (R : realType)
    (S : set (Hom (coordinate_space R 0) (coordinate_space R 0))) :
  S 0 -> nbhs ((0 : Hom (coordinate_space R 0) (coordinate_space R 0)) :
    real_norm_metric_space (hom_operator_norm_real_norm (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R 0) (@coordinate_basisP R 0))) S.
Proof.
move=> h0; pose M := real_norm_metric_space (hom_operator_norm_real_norm
  (@euclidean_inner_productP R 0) (@euclidean_inner_productP R 0) (@coordinate_basisP R 0)).
apply/(metricType_numDomainType.nbhs_mdistP (0 : M) S); exists 1=> [|f _]; first exact: ltr01.
by have -> : f = 0 by apply: hom_ext=> x; rewrite (coordinate_zero x) hom_zeroE (coordinate_zero (f 0)).
Qed.

(** Source for [finite_norms_scalar_example]: regression for "all norms
    ... induce the same ... topology", Federer 2.7.16, p. 134, for the
    one-dimensional space R^1: the comparison constants of any two
    norms are positive. *)
Example finite_norms_scalar_example (R : realType) (N1 N2 : coordinate_space R 1 -> R) :
  is_real_norm N1 -> is_real_norm N2 ->
  exists c C : R, [/\ 0 < c, 0 < C & forall x, c * N1 x <= N2 x /\ N2 x <= C * N1 x].
Proof. exact: (finite_norms_equivalent (@coordinate_basisP R 1)). Qed.

End AffineMapSpaceExamples.

From Federer Require Import InnerProductUP InnerMetric LinearBasis Annihilator Hom HomInner ExteriorDeterminant EuclideanLinearMaps EuclideanInnerProduct FiniteCoordinates FiniteExteriorPowers InnerExterior OrthonormalFamilies ModularFunctionUP HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance StabiliserHomSpace AffineGroupTopology SpecialLinearCommutators AffineGroupModular SimpleVectorFrames .
From mathcomp Require Import topology.

Section Example27164bExamples.
Local Open Scope ring_scope.

(** Source for [commutator_subgroup_zero_dimensional_example]:
    regression for "{g : det g = 1} is the commutator subgroup of
    GL(n, R)", Federer 2.7.16, p. 138, at the boundary n = 0: every
    member of GL(0, R) lies in the commutator subgroup, its determinant
    being 1 (1.3.4, p. 16). *)
Example commutator_subgroup_zero_dimensional_example (R : realType)
    (g : set_type (linear_group (@euclidean_inner_productP R 0) (@coordinate_basisP R 0))) :
  commutator_subgroup (@euclidean_inner_productP R 0) (@coordinate_basisP R 0) g.
Proof.
apply/special_linear_commutator.
rewrite /linear_group_det /hom_det.
rewrite (det_scalar_map (euclidean_two_nonzero R) (@coordinate_basisP R 0) (c := 1)) ?expr0 // => v.
by rewrite (basis_vector_expansion (@coordinate_basisP R 0) v) !big_ord0 linear0 scaler0.
Qed.

(** Source for [word_diagonal_scale_zero_example]: regression for the
    scaling of products used for 2.7.16, p. 138, at the boundary m = 0:
    the empty product of scalars is 1 (1.3.4, p. 16). *)
Example word_diagonal_scale_zero_example (K : fieldType) (V : lmodType K) (u : 'I_0 -> V) (d : 'I_0 -> K) :
  e_lambda (fun i => d i *: u i) (ord_tuple 0) = e_lambda u (ord_tuple 0).
Proof. by rewrite word_diagonal_scale big_ord0 scale1r. Qed.

(** Source for [orthonormal_word_zero_example]: regression for "a
    product of an orthonormal family has norm 1", used for 2.7.16,
    p. 138, at the boundary m = 0: the empty product has inner square 1
    (1.7.5, p. 32). *)
Example orthonormal_word_zero_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) (u : 'I_0 -> V) :
  exterior_inner_form (euclidean_two_nonzero R) hB (e_lambda u (ord_tuple 0)) (e_lambda u (ord_tuple 0)) = 1.
Proof. by apply: orthonormal_word_inner=> -[]. Qed.

(** Source for [affine_modular_translation_example]: regression for
    "Delta_G(g) = |det L(g)|^{-1}", Federer 2.7.16, p. 138, at the
    translations, L(g) = 1_V: Delta_G(tau_z) = 1, as "Delta_G|ker L = 1"
    requires. *)
Example affine_modular_translation_example (R : realType) (V : lmodType R) (B : V -> V -> R)
    (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b) (DG : _ -> R) :
  is_modular_function (affine_group_mul hB hb) (affine_group_inv hB hb) DG ->
  forall z, DG (linear_group_unit hB hb, z) = 1.
Proof. by move=> hDG z; rewrite (affine_group_modular hDG) /= linear_group_det_unit normr1 invr1. Qed.

End Example27164bExamples.

From Federer Require Import InnerProductUP InnerMetric LinearBasis ModuleQuotient GrassmannSubspaces Hom HomInner FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct MeasureUP MeasureBasic MeasureRestriction MeasurePushforward CovariantIntegralUP HaarIntegralUP TopologicalGroupUP TopologicalGroupLaws HomogeneousSpaceUP GroupMultiplicationHomogeneous IsotropyGroupTopology HomSpaceTopology LinearGroupTopology LinearGroupSealed HomHaarCovariance InnerProductRestriction SubspaceStabiliser StabiliserHomSpace StabiliserHaarCovariance OpenSubspaceMeasure LinearGroupHaarMeasure StabiliserHaarMeasure CompactIsotropyNormalisation DualMapHaarMeasure .
From mathcomp Require Import functions topology.
From mathcomp Require Import pseudometric_normed_Zmodule.

Section OpenSubspaceMeasureExamples.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_subspace_measure_empty_example]: regression for
    "phi ... over G", Federer 2.7.16, p. 136, read as the restriction
    T |-> phi(T) to subsets of an open set, in the boundary case of the
    empty open set: the restriction is the zero measure. *)
Example open_subspace_measure_empty_example (R : realType) (T : choiceType) (phi : set T -> \bar R)
    (A : set (set_type (set0 : set T))) :
  is_measure phi -> open_subspace_measure phi A = 0%E.
Proof.
move=> hm; rewrite /open_subspace_measure.
have -> : set_val @` A = set0 by apply/seteqP; split=> [_ [y _ <-]|//]; exact: set_valP y.
exact: measure_empty hm.
Qed.

(** Source for [open_subspace_measure_whole_example]: regression for
    the restriction of phi to an open set S, Federer 2.7.16, p. 136, in
    the boundary case S = X: its image under the inclusion of S is phi L X
    = phi (2.1.2, p. 54). *)
Example open_subspace_measure_whole_example (R : realType) (T : pseudoMetricType R)
    (phi : set T -> \bar R) :
  measure_pushforward (set_val : set_type [set: T] -> T) (open_subspace_measure phi) = phi.
Proof.
rewrite open_subspace_measure_pushforward; apply: funext=> B.
by rewrite /measure_restrict setTI.
Qed.

(** Source for [linear_group_zero_dimension_right_invariant_example]:
    regression for "therefore phi is right |det|^n covariant", Federer
    2.7.16, p. 137, at the boundary n = 0: the restriction of a Haar
    measure of Hom(R^0, R^0) to the linear group is right invariant. *)
Example linear_group_zero_dimension_right_invariant_example (R : realType)
    (phi : set (inner_metric_space (hom_inner_productP (@euclidean_inner_productP R 0)
      (@euclidean_inner_productP R 0) (@coordinate_basisP R 0))) -> \bar R) :
  is_left_haar_measure (fun f g : inner_metric_space (hom_inner_productP (@euclidean_inner_productP R 0)
    (@euclidean_inner_productP R 0) (@coordinate_basisP R 0)) => f + g) phi ->
  is_right_invariant_measure (linear_group_mul (@euclidean_inner_productP R 0) (@coordinate_basisP R 0))
    (linear_group_inv (@euclidean_inner_productP R 0) (@coordinate_basisP R 0))
    (open_subspace_measure (S := linear_group (@euclidean_inner_productP R 0) (@coordinate_basisP R 0)) phi).
Proof.
move=> hphi; have h := linear_group_haar_measure_right_covariant hphi.
have he : (fun g => `|linear_group_det (@euclidean_inner_productP R 0) (@coordinate_basisP R 0) g| ^+ 0)
    = (fun _ => 1) by apply: funext=> g; rewrite expr0.
by rewrite he in h.
Qed.

(** Source for [stabiliser_zero_dimensional_left_covariant_example]:
    regression for "every Haar measure gamma of X is ... chi covariant",
    Federer 2.7.16, p. 137, as a measure over G, at the boundary
    m = dim W = 0 excluded there by 0 < m: chi = |det|^{-n}, the
    character of the linear group in (2). *)
Example stabiliser_zero_dimensional_left_covariant_example (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) n (b : 'I_n -> V) (hb : is_basis b)
    (W : ModuleQuotient.subspace V) (hW : grassmann_pred 0 W) mulS invS eS
    (gamma : set (inner_metric_space (@restricted_inner_productP R (Hom V V) _
      (hom_inner_productP hB hB hb) (subspace_preserving_maps W))) -> \bar R) :
  is_subgroup_restriction (linear_group_mul hB hb) (linear_group_inv hB hb) (linear_group_unit hB hb)
    (subspace_stabiliser hB hb W) mulS invS eS ->
  is_left_haar_measure (fun f g : inner_metric_space (@restricted_inner_productP R (Hom V V) _
    (hom_inner_productP hB hB hb) (subspace_preserving_maps W)) => f + g) gamma ->
  is_left_covariant_measure mulS (fun g => `|stabiliser_det g| ^- n) (stabiliser_haar_restriction gamma).
Proof.
move=> hS hgamma.
have [nu [hm hcov hms hrep hreg]] := stabiliser_haar_measure_left_covariant hW hgamma hS.
exists nu; split=> // u g hu; rewrite hcov //.
by rewrite /stabiliser_character expr0 invr1 mul1r subn0.
Qed.

(** Source for [exterior_one_identity_example]: regression for "the
    linear isomorphism wedge^1: Hom(V, V) ~ Hom(wedge^1 V, wedge^1 V)",
    Federer 2.7.16, p. 137, at the unit of G: wedge^1 1_V is the identity
    of wedge^1 V. *)
Example exterior_one_identity_example (R : realType) (V : lmodType R) :
  exterior_one_fun (hom_identity V) = hom_identity (Hom V R^o).
Proof.
apply: hom_ext=> omega; rewrite exterior_one_funE hom_identityE.
by apply: hom_ext=> x; rewrite hom_compE hom_identityE.
Qed.

(** Source for [left_multiplication_normalised_isotropy_example]:
    regression for "provided mu is chosen so that mu(1) = 1", Federer
    2.7.12, p. 129, in the boundary case X = G with the action 2.7.2(1),
    p. 122: the isotropy group G^x = {e} is compact, and it has a left
    Haar integral mu with mu(1) = 1. *)
Example left_multiplication_normalised_isotropy_example (R : realType) (G : topologicalType) (mul : G -> G -> G)
    (inv : G -> G) (e : G) (x : G) :
  is_locally_compact_hausdorff_group mul inv e ->
  exists mulS invS eS (mu : (isotropy_subgroup (left_multiplication_action mul) x -> R) -> R),
    is_subgroup_restriction mul inv e (isotropy_subgroup (left_multiplication_action mul) x) mulS invS eS /\
    is_left_haar_integral mulS mu /\ mu (fun _ => 1) = 1.
Proof.
move=> hG.
have hT := lch_group_topological hG; have hgl := topological_group_laws hT.
have hA := left_multiplication_homogeneous hT.
have hH := lch_group_hausdorff hG.
have hSe : isotropy_subgroup (left_multiplication_action mul) x = [set e].
  apply/seteqP; split=> g; rewrite /isotropy_subgroup /left_multiplication_action /=.
  - by move=> h; rewrite -(group_mulgK hgl x g) h (group_mulgV hgl).
  - by move=> ->; exact: group_mul1g hgl x.
have hSc : compact (isotropy_subgroup (left_multiplication_action mul) x) by rewrite hSe; exact: compact_set1.
have [mulS [invS [eS [hR _]]]] := isotropy_group_exists x hG hA hH.
have [mu [hmu h1]] := compact_isotropy_normalised_haar_exists R hG hA hH hSc hR.
by exists mulS, invS, eS, mu.
Qed.

End OpenSubspaceMeasureExamples.
