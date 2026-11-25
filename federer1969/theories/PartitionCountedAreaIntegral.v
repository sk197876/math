(** Federer (1969), 3.2.46, p. 282: sum actual
    counting multiplicities over the original disjoint source
    patches, as in the proof of 3.2.3, p. 243.
    Unlike the univalent special case, every patch may
    itself have infinite multiplicity; duplicate image points
    retain their actual counts. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic
  ExtendedRealOrderTopology MeasureUP MeasureCountableAdditivity
  CountingMeasure MappingMultiplicity NonnegativeSum
  MeasureIntegralUP MeasureIntegralGraphEquivalence TotalCountableNonnegativeIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [mapping_multiplicity_countable_partition]:
    exact actual fibre-count sum for a countable disjoint
    partition of the source, supporting 3.2.46, p. 282,
    through 2.1.3(3), p. 55, for counting measure.
    Neither the individual nor total fibre is assumed finite. *)
Theorem mapping_multiplicity_countable_partition (R : realType) (X Y I : choiceType)
    (f : X -> Y) (S : set X) (D : set I) (E : I -> set X) :
  countable D -> S=\bigcup_(i in D) E i ->
  (forall i j, D i -> D j -> i!=j -> forall x, E i x -> E j x -> False) ->
  forall y, @mapping_multiplicity R X Y f S y=
    nonnegative_sum D (fun i=>@mapping_multiplicity R X Y f (E i) y).
Proof.
move=> hCount hCover hDisjoint y.
have hFibre : mapping_fibre f S y=\bigcup_(i in D) mapping_fibre f (E i) y.
  apply/seteqP; split=> x.
  - move=> [hx hf]; rewrite hCover in hx; have [i hi hxE] := hx.
    exists i; first exact hi; by split.
  - move=> [i hi [hx hf]]; split; last exact hf.
    rewrite hCover; by exists i.
rewrite /mapping_multiplicity hFibre.
apply: (@measure_countable_disjoint_additivity R X I (@counting_measure R X)
  (counting_measure_is_measure R X) D (fun i=>mapping_fibre f (E i) y) hCount).
- move=> i hi; exact: counting_measure_measurable.
- move=> i j hi hj hij x [hx hf] [hy hf']; exact: hDisjoint i j hi hj hij x hx hy.
Qed.

(** Source for [partition_counted_area_integral]: local
    area integrals on arbitrary disjoint source pieces sum
    to the integral of the actual whole multiplicity,
    supporting 3.2.46, p. 282. All infinite values
    remain; finite multiplicity and disjoint target images
    are not required. *)
Theorem partition_counted_area_integral (R : realType) (X Y I : choiceType)
    (f : X -> Y) (S : set X) (D : set I) (E : I -> set X)
    (beta : set Y -> \bar R) (a : I -> \bar R) :
  is_measure beta -> countable D -> S=\bigcup_(i in D) E i ->
  (forall i j, D i -> D j -> i!=j -> forall x, E i x -> E j x -> False) ->
  (forall i, D i -> is_measure_integral beta
    (partial_function_total (fun y=>(@mapping_multiplicity R X Y f (E i) y : extended_real_line R))) (a i)) ->
  is_measure_integral beta
    (partial_function_total (fun y=>(@mapping_multiplicity R X Y f S y : extended_real_line R)))
    (nonnegative_sum D a).
Proof.
move=> hBeta hCount hCover hDisjoint hLocal.
have hSum := @total_countable_nonnegative_integral R Y I beta hBeta D
  (fun i y=>(@mapping_multiplicity R X Y f (E i) y : extended_real_line R)) a hCount
  (fun i hi y=>@mapping_multiplicity_nonnegative R X Y f (E i) y) hLocal.
apply: (measure_integral_graph_equivalent _ hSum)=> y z.
change (nonnegative_sum D (fun i=>@mapping_multiplicity R X Y f (E i) y)=z <->
  @mapping_multiplicity R X Y f S y=z).
by rewrite -(@mapping_multiplicity_countable_partition R X Y I f S D E hCount hCover hDisjoint y).
Qed.
