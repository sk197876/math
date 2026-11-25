(** Federer (1969), 2.6.5, p. 120: Borel regularity of finite-dimensional
    Lebesgue measure. Borel rectangles need no countability assumption;
    countable bases ensure that every open set is a countable union of
    measurable rectangles. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import BorelFamilyBasic TopologicalBorel ContinuousBorelPreimages
  TopologicalProductMaps CountableOpenBaseUP CompactTube MeasureUP MeasureCountableClosure
  ProductMeasure ProductRectangleMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_product_rectangle]: Supporting Federer 2.2.1, pp.
    59–60. *)
Lemma borel_product_rectangle (X Y : topologicalType) (A : set X) (B : set Y) :
  borel_set A -> borel_set B -> borel_set (A `*` B).
Proof.
move=> hA hB.
have he : A `*` B = (@fst X Y @^-1` A) `&` (@snd X Y @^-1` B) by [].
rewrite he; apply: (borel_family_binary_intersection (borel_sets_family (X * Y)%type)).
- exact (@continuous_borel_preimage (X * Y)%type X (@fst X Y) (@first_projection_continuous X Y) A hA).
- exact (@continuous_borel_preimage (X * Y)%type Y (@snd X Y) (@second_projection_continuous X Y) B hB).
Qed.

(** Source for [product_open_sets_measurable]: Supporting Federer 2.6.5, p.
    120.Only open-set measurability of the factors and countable topological
    bases are needed; no finite-total-mass hypothesis is imposed. *)
Theorem product_open_sets_measurable (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta)
    (U : nat -> set X) (V : nat -> set Y) :
  is_countable_open_base U -> is_countable_open_base V ->
  (forall A, open A -> measure_measurable alpha A) ->
  (forall B, open B -> measure_measurable beta B) ->
  forall O, open O -> measure_measurable (product_measure ha hb) O.
Proof.
move=> hU hV hAo hBo O hO.
pose D := [set p : nat * nat | U p.1 `*` V p.2 `<=` O].
have he : O = \bigcup_(p in D) (U p.1 `*` V p.2).
  apply/seteqP; split.
  - move=> [x y] hxy.
    have [A [B [hA [hB [hx [hy hAB]]]]]] := open_product_rectangle_at hO hxy.
    have [i [hi hiA]] := @countable_base_refines X U hU A hA x hx.
    have [j [hj hjB]] := @countable_base_refines Y V hV B hB y hy.
    exists (i,j); last by split.
    move=> [u v] [hu hv]; apply: hAB; split; [exact: hiA u hu|exact: hjB v hv].
  - by move=> p [ij hij hp]; exact: hij p hp.
rewrite he; apply: (measure_measurable_countable_union (product_measure_is_measure ha hb) (countableP D)).
move=> [i j] _; apply: (product_measure_rectangle_measurable ha hb).
- exact: hAo (countable_base_open hU i).
- exact: hBo (countable_base_open hV j).
Qed.
