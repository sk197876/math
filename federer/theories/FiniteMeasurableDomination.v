(** Supporting measure comparison for Federer (1969), 2.5.11, p. 102: the
    identity L_1(phi)=L, used in the form of the erratum p. 2, book p. 102
    line 12. Suppose nu <= mu on all sets and every mu measurable set with
    finite mu measure is nu measurable. Then countably mu measurable sets
    are countably nu measurable, a countably mu measurable function is
    countably nu measurable, and every mu summable real function is nu
    summable with no larger absolute integral. The arguments are those of
    the Borel case in BorelDominatedMeasureTransfer.v,
    BorelDominatedFunctionTransfer.v, BorelDominatedNonnegativeIntegral.v
    and BorelDominatedRealSummability.v, with the Borel sandwich of 2.2.3
    replaced by the finite-set hypothesis. They use 2.3.3, p. 76, 2.3.4, p.
    76, 2.4.4(7)-(8), p. 82, and 2.4.8, p. 84. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionPreimages PartialExtendedArithmetic PartialAbsolutePartsGraph
  MeasureUP MeasureFiniteClosure MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel
  TopologicalBorel CountablyMeasurableUP CountablyMeasurableBasic CountablyMeasurableSubsets
  CountablyMeasurableSequences BorelDominatedMeasureTransfer
  CharacteristicFunctionUP WeightedCharacteristicExpansionUP WeightedCharacteristicExpansion
  PositiveVanishingWeightsSealed WeightedCharacteristicIntegral MeasureIntegralUP
  MeasureIntegralUniqueness MeasureIntegralGraphEquivalence NonnegativeSum
  MeasureAbsoluteSummability SummableRealFunctionUP SummableCountableMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_dominated_countably_measurable]: supporting
    transfer of countably measurable sets for the identity
    L_1(phi)=L in Federer 2.5.11, p. 102; the definition of
    countable measurability is 2.3.4, p. 76. *)
Lemma finite_dominated_countably_measurable (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu) :
  (forall B, nu B <= mu B) ->
  (forall B, measure_measurable mu B -> mu B < +oo -> measure_measurable nu B) ->
  forall A, measure_countably_measurable mu A -> measure_countably_measurable nu A.
Proof.
move=> hd hf A /(countably_measurable_sequence_iff hm) [F [he hF]].
apply/(countably_measurable_sequence_iff hn); exists F; split=> // n; split.
- exact: hf (F n) (hF n).1 (hF n).2.
- exact: le_lt_trans (hd (F n)) (hF n).2.
Qed.

(** Source for [finite_dominated_function_measurable]: supporting
    transfer of countably measurable functions, Federer 2.3.4,
    p. 76, for the identity L_1(phi)=L in 2.5.11, p. 102.
    Preimages avoiding zero lie in the countably measurable nonzero
    locus; the other preimages are complements inside the conull
    domain. Partial domains are retained. *)
Lemma finite_dominated_function_measurable (R : realType) (X : choiceType)
    (Y : topologicalType) (mu nu : set X -> \bar R)
    (hm : is_measure mu) (hn : is_measure nu) (zero : Y) (f : partial_function X Y) :
  (forall B, nu B <= mu B) ->
  (forall B, measure_measurable mu B -> mu B < +oo -> measure_measurable nu B) ->
  is_countably_measure_measurable_function mu zero f ->
  is_countably_measure_measurable_function nu zero f.
Proof.
move=> hd hfin [hf hs].
have hdom : measure_almost_everywhere nu (partial_function_domain f).
  exact (@dominated_measure_null R X mu nu hn hd _ (measurable_function_domain hf)).
have hsmall : forall B : set Y, borel_set B -> ~ B zero ->
    measure_measurable nu (partial_function_preimage f B).
  move=> B hB hz.
  have hc : measure_countably_measurable mu (partial_function_preimage f B).
    apply: (@measurable_subset_countably_measurable R X mu hm _
      (partial_function_nonzero_locus zero f)
      (@measurable_function_borel_preimage R X Y mu hm f hf B hB) _ hs).
    move=> x [y [hy hBy]]; exists y; split=> //.
    by move=> ey; apply: hz; rewrite -ey.
  apply: (countably_measurable_set_measurable hn).
  exact (@finite_dominated_countably_measurable R X mu nu hm hn hd hfin _ hc).
constructor.
- constructor=> // U hU.
  case: (pselect (U zero))=> hz.
  + rewrite -[U]setCK partial_function_preimage_complement.
    apply: (@measure_measurable_difference R X nu hn).
    * exact (@conull_partial_function_domain_measurable R X Y nu hn f hdom).
    * apply: hsmall; first exact: borel_set_complement (open_borel_set hU).
      by move=> h; exact: h hz.
  + exact: hsmall (open_borel_set hU) hz.
- exact (@finite_dominated_countably_measurable R X mu nu hm hn hd hfin _ hs).
Qed.

(** Source for [finite_dominated_nonnegative_integral]: supporting
    comparison of nonnegative integrals for the identity
    L_1(phi)=L in Federer 2.5.11, p. 102. The witness for the
    dominated integral is the positive characteristic series of
    2.3.3, p. 76, integrated termwise by 2.4.8, p. 84. *)
Lemma finite_dominated_nonnegative_integral (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu)
    (f : X -> extended_real_line R) a :
  (forall B, nu B <= mu B) ->
  (forall B, measure_measurable mu B -> mu B < +oo -> measure_measurable nu B) ->
  (forall x, 0 <= f x) -> measure_countably_measurable mu [set x | f x <> 0] ->
  is_measure_integral mu (partial_function_total f) a ->
  exists b, is_measure_integral nu (partial_function_total f) b /\ 0 <= b /\ b <= a.
Proof.
move=> hd hfin hp hs hf.
pose r := @PositiveVanishingWeights.value R; have hw := @PositiveVanishingWeights.laws R.
have [E [s [he _]]] := @measurable_weighted_characteristic_expansion R X mu hm f r hf.1 hp hw.
have hsub n : E n `<=` [set x | f x <> 0].
  move=> x hx hz.
  have ht := @nonnegative_sum_term R [the choiceType of (nat : Type)] setT
    (fun j => (r j*s j x)%R%:E) n I.
  rewrite (expansion_pointwise_sum he x)
    (characteristic_on_set (expansion_characteristic_laws he n) hx) mulr1 hz in ht.
  have hh : (0 : \bar R) < (r n)%:E by rewrite lte_fin; exact: expansion_weights_positive hw n.
  by have := lt_le_trans hh ht; rewrite ltxx.
have hE n : measure_measurable nu (E n).
  apply: (countably_measurable_set_measurable hn).
  apply: (@finite_dominated_countably_measurable R X mu nu hm hn hd hfin).
  exact (@measurable_subset_countably_measurable R X mu hm (E n) _
    (expansion_sets_measurable he n) (hsub n) hs).
have hrep : is_weighted_characteristic_expansion nu f r E s.
  constructor; [exact: hE|exact: expansion_characteristic_laws he|exact: expansion_pointwise_sum he].
have hi := @weighted_characteristic_expansion_integral R X mu hm f r E s (expansion_weights_positive hw) he.
have hj := @weighted_characteristic_expansion_integral R X nu hn f r E s (expansion_weights_positive hw) hrep.
exists (nonnegative_sum setT (fun n => (r n)%:E*nu (E n))); split=> //.
split; first exact: nonnegative_sum_nonnegative.
rewrite -(measure_integral_unique hi hf); apply: nonnegative_sum_mono=> n _.
apply: lee_wpmul2l; last exact: hd.
rewrite lee_fin; exact: ltW (expansion_weights_positive hw n).
Qed.

(** Source for [finite_dominated_real_absolute_integral]:
    supporting transfer of summability for the identity
    L_1(phi)=L in Federer 2.5.11, p. 102, by 2.4.4(7)–(8),
    p. 82: a mu summable real function is nu summable, and its
    absolute nu integral does not exceed its absolute mu integral. *)
Theorem finite_dominated_real_absolute_integral (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu) (hn : is_measure nu) (f : X -> R) (a : R) :
  (forall B, nu B <= mu B) ->
  (forall B, measure_measurable mu B -> mu B < +oo -> measure_measurable nu B) ->
  summable_real_functions mu f ->
  is_measure_integral mu (real_total_integrand (fun x => `|f x|%R)) a%:E ->
  summable_real_functions nu f /\ exists b : R,
    is_measure_integral nu (real_total_integrand (fun x => `|f x|%R)) b%:E /\ (b <= a)%R.
Proof.
move=> hd hfin hs ha.
pose F := fun x : X => ((`|f x|%R)%:E : extended_real_line R).
have hi : is_measure_integral mu (partial_function_total F) a%:E.
  apply: (@measure_integral_graph_equivalent R X mu _ _ _ _ ha)=> x z.
  exact: real_total_integrand_graph.
have hcs := @measure_summable_countably_measurable R X mu hm
  (partial_function_total F) (ex_intro _ a hi).
have he : partial_function_nonzero_locus (0 : extended_real_line R) (partial_function_total F) =
    [set x | F x <> 0].
  apply/seteqP; split=> x.
  - move=> [z [hz hnz]]; change (F x <> 0).
    by rewrite (hz : F x = z).
  - move=> hx; exists (F x); by split.
have hcount : measure_countably_measurable mu [set x | F x <> 0].
  rewrite -he; exact: countably_measurable_function_locus hcs.
have hp x : 0 <= F x by rewrite /F lee_fin normr_ge0.
have [b [hbi [hb0 hba]]] := @finite_dominated_nonnegative_integral R X mu nu hm hn
  F a%:E hd hfin hp hcount hi.
have hfb : b \is a fin_num.
  rewrite (ge0_fin_numE hb0); exact: le_lt_trans hba (ltry a).
have habs : is_measure_integral nu (real_total_integrand (fun x => `|f x|%R)) (fine b)%:E.
  rewrite fineK //; apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ hbi)=> x z.
  symmetry; exact: real_total_integrand_graph.
have hmf := @finite_dominated_function_measurable R X (extended_real_line R) mu nu hm hn
  0 (real_total_integrand f) hd hfin (@measure_summable_countably_measurable R X mu hm _ hs).
have habs' : is_measure_summable nu (partial_extended_function_absolute_value (real_total_integrand f)).
  exists (fine b); apply: (@measure_integral_graph_equivalent R X nu _ _ _ _ habs)=> x z.
  rewrite real_total_integrand_graph; split.
  - move=> hz; exists (f x)%:E; split; first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - move=> [y [hy <-]]; have hyE := (real_total_integrand_graph f x y).1 hy.
    by rewrite -hyE abse_EFin.
split.
- exact (@measure_absolute_summable_implies_summable R X nu hn _
    (countably_measurable_function_measurable hmf) habs').
- exists (fine b); split=> //; by move: hba; rewrite -(fineK hfb) lee_fin.
Qed.
