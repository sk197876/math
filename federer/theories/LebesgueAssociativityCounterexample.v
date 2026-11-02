(** Local correction to Federer (1969), 2.6.5, p. 119. The diagonal over
    [0,1] already disproves unrestricted associativity Lebesgue measure is
    obtained from the existing proof of Federer 2.5.17, p. 111. The local
    Federer erratum contains no correction to this associativity claim. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype.
From Federer Require Import CountableOrderIntervals MeasureUP MeasureBasic MeasureSplit
  MeasureFiniteClosure BorelRegularMeasureUP MeasurePushforward ProductMeasure
  InfiniteDiscreteMeasure ProductAssociativityObstruction RealDiagonalMeasurability
  FiniteNullDiagonal LebesgueLineCharacterisation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [interval_length_measure_singleton_null]: supporting
    singleton-null calculation from Federer 2.5.17, p. 111. *)
Lemma interval_length_measure_singleton_null (R : realType) (mu : set R -> \bar R) :
  (forall a b : R, a <= b -> mu `[a,b] = (b-a)%:E) ->
  forall x, mu [set x] = 0%:E.
Proof.
move=> hs x.
have he : [set x] = `[x,x].
  apply/seteqP; split=> y.
  - by move=> <-; rewrite /= in_itv /= lexx.
  - rewrite /= in_itv /= => /andP[hxy hyx].
    apply/eqP; by rewrite eq_le hxy hyx.
by rewrite he hs ?lexx // subrr.
Qed.

(** Source for [lebesgue_bounded_diagonal_null]: The null sections and
    finite rectangle justify the application of Federer 2.6.2(3), p. 115.
    This supports the local correction to Federer 2.6.5, p. 119. *)
Theorem lebesgue_bounded_diagonal_null (R : realType)
    (mu : set R -> \bar R) (hm : is_measure mu)
    (hr : is_borel_regular_measure mu)
    (hs : forall a b : R, a <= b -> mu `[a,b] = (b-a)%:E)
    (a b : R) : a <= b ->
  product_measure hm hm (restricted_diagonal [set x | a <= x /\ x <= b]) = 0%:E.
Proof.
move=> hab.
have hO t : measure_measurable mu [set x | x < t].
  apply: (borel_regular_open_measurable hr).
  exact: order_strict_lower_ray_open.
have hC t : measure_measurable mu [set x | x <= t].
  have hu : measure_measurable mu [set x | t < x].
    apply: (borel_regular_open_measurable hr).
    exact: order_strict_upper_ray_open.
  have he : [set x : R | x <= t] = ~` [set x : R | t < x].
    apply/seteqP; split=> x /=.
    - move=> h; apply/negP; by rewrite -leNgt.
    - move=> /negP h; by rewrite leNgt.
  rewrite he; exact: measure_measurable_complement hu.
have hA : measure_measurable mu [set x | a <= x /\ x <= b].
  have he : [set x : R | a <= x /\ x <= b] = [set x | x <= b] `\` [set x | x < a].
    apply/seteqP; split=> x.
    - move=> [hax hxb]; split=> //; apply/negP; by rewrite -leNgt.
    - move=> [hxb /negP hxa]; split=> //; by rewrite leNgt.
  rewrite he; exact: measure_measurable_difference (hC b) (hO a).
have hvalue : mu [set x | a <= x /\ x <= b] = (b-a)%:E.
  have he : [set x : R | a <= x /\ x <= b] = `[a,b].
    apply/seteqP; split=> x; rewrite /= in_itv /=.
    - by move=> [h1 h2]; rewrite h1 h2.
    - by move=> /andP.
  by rewrite he hs.
have hf : (mu [set x | (a <= x /\ x <= b)%R] < +oo)%E by rewrite hvalue ltry.
apply: (@finite_measurable_diagonal_null R R mu mu hm hm _ hA hA hf hf).
- move=> x _; exact: interval_length_measure_singleton_null hs x.
- exact (@real_closed_segment_diagonal_measurable R mu mu hm hm a b hO hC hO hC hA hA).
Qed.

(** Source for [lebesgue_product_not_associative]: concrete counterexample
    to the unrestricted equality in Federer 2.6.5, p. 119. The third factor
    is nonempty and has infinite measure on all nonempty subsets. The first
    two factors are the Lebesgue measure proved to exist in 2.5.17. This is
    explicitly a local correction, not Federer's erratum. *)
Theorem lebesgue_product_not_associative (R : realType) (Z : choiceType) (z0 : Z) :
  exists mu : set R -> \bar R, exists hm : is_measure mu,
    is_borel_regular_measure mu /\
    (forall a b : R, a <= b -> mu `[a,b] = (b-a)%:E) /\
    measure_pushforward (fun p : (R * R) * Z => (p.1.1,(p.1.2,p.2)))
      (product_measure (product_measure_is_measure hm hm) (infinite_discrete_measure_is_measure R Z)) <>
    product_measure hm (product_measure_is_measure hm (infinite_discrete_measure_is_measure R Z)).
Proof.
have [mu [hm [hr [_ [_ [_ [hs _]]]]]]] := lebesgue_line_measure_characterisation R.
exists mu, hm; split=> //; split=> //.
have hi : forall C : set Z, (exists z, C z) -> infinite_discrete_measure R C = +oo%E.
  exact: infinite_discrete_measure_nonempty.
have hp : (0 < mu [set x : R | (0 <= x /\ x <= 1)%R])%E.
  have he : [set x : R | 0 <= x /\ x <= 1] = `[0,1].
    apply/seteqP; split=> x; rewrite /= in_itv /=.
    - by move=> [h1 h2]; rewrite h1 h2.
    - by move=> /andP.
  by rewrite he hs ?ler01 // subr0 lte_fin ltr01.
have hz := @lebesgue_bounded_diagonal_null R mu hm hr hs 0 1 ler01.
exact (@product_measure_associativity_obstruction R R Z mu (@infinite_discrete_measure R Z)
  hm (infinite_discrete_measure_is_measure R Z) hi z0 [set x | 0 <= x /\ x <= 1] hp hz).
Qed.
