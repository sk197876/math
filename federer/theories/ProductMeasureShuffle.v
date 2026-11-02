(** Finite coordinate rearrangement supporting Federer (1969), 2.10.16, p.
    178, using 2.6.5, pp. 119–120. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward CountablyMeasurableUP CountablyMeasurableProduct
  ProductMeasure ProductMeasureAssociativity ProductMeasureBijections MeasureBijectionUP
  MeasureBijectionLaws MeasureBijectionCoordinateTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_product_association_bijection]: supporting
    abstract association law for 2.10.16, p. 178.
    It packages the corrected 2.6.5, p. 119, with
    explicit inverses; no unrestricted associativity is used. *)
Lemma countable_product_association_bijection (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma) :
  measure_countably_measurable alpha setT -> measure_countably_measurable gamma setT ->
  is_measure_bijection (product_measure (product_measure_is_measure ha hb) hc)
    (product_measure ha (product_measure_is_measure hb hc))
    (@product_associate X Y Z) (@product_unassociate X Y Z).
Proof.
move=> hX hZ; constructor.
- by move=> [[x y] z].
- by move=> [x [y z]].
- exact: product_measure_associative_outer_countable hX hZ.
Qed.

(** Source for [countable_product_four_shuffle]: supporting
    four-factor coordinate exchange for the actual slicing
    integrals of 2.10.16, p. 178. Finite association
    and the flip of 2.6.5, p. 119, give the
    displayed map ((x,y),(z,w)) -> ((x,z),(y,w)). *)
Theorem countable_product_four_shuffle (R : realType) (X Y Z W : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (gamma : set Z -> \bar R) (delta : set W -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma) (hd : is_measure delta) :
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  measure_countably_measurable gamma setT -> measure_countably_measurable delta setT ->
  is_measure_bijection
    (product_measure (product_measure_is_measure ha hb) (product_measure_is_measure hc hd))
    (product_measure (product_measure_is_measure ha hc) (product_measure_is_measure hb hd))
    (fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2)))
    (fun z => ((z.1.1,z.2.1),(z.1.2,z.2.2))).
Proof.
move=> hX hY hZ hW.
have hZW := @product_whole_countably_measurable R Z W gamma delta hc hd hZ hW.
have hYW := @product_whole_countably_measurable R Y W beta delta hb hd hY hW.
have h1 := @countable_product_association_bijection R X Y (Z*W)%type alpha beta
  (product_measure hc hd) ha hb (product_measure_is_measure hc hd) hX hZW.
have h2 := measure_bijection_product ha (product_measure_is_measure hb (product_measure_is_measure hc hd))
  ha (product_measure_is_measure (product_measure_is_measure hb hc) hd)
  (measure_bijection_identity alpha)
  (measure_bijection_inverse (countable_product_association_bijection hb hc hd hY hW)).
have h3 := measure_bijection_product ha (product_measure_is_measure (product_measure_is_measure hb hc) hd)
  ha (product_measure_is_measure (product_measure_is_measure hc hb) hd)
  (measure_bijection_identity alpha)
  (measure_bijection_product (product_measure_is_measure hb hc) hd (product_measure_is_measure hc hb) hd
    (measure_bijection_swap hb hc) (measure_bijection_identity delta)).
have h4 := measure_bijection_product ha (product_measure_is_measure (product_measure_is_measure hc hb) hd)
  ha (product_measure_is_measure hc (product_measure_is_measure hb hd))
  (measure_bijection_identity alpha) (countable_product_association_bijection hc hb hd hZ hW).
have h5 := measure_bijection_inverse
  (countable_product_association_bijection ha hc (product_measure_is_measure hb hd) hX hYW).
exact (measure_bijection_compose (measure_bijection_compose (measure_bijection_compose
  (measure_bijection_compose h1 h2) h3) h4) h5).
Qed.

(** Source for [countable_product_three_exchange]: supporting
    exchange of the last two factors of a triple integral
    in 2.10.16, p. 178. This uses only the corrected
    association of 2.6.5, p. 119, and the flip. *)
Lemma countable_product_three_exchange (R : realType) (X Y Z : choiceType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) (hc : is_measure gamma) :
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  measure_countably_measurable gamma setT ->
  is_measure_bijection (product_measure (product_measure_is_measure ha hb) hc)
    (product_measure (product_measure_is_measure ha hc) hb)
    (fun z => ((z.1.1,z.2),z.1.2)) (fun z => ((z.1.1,z.2),z.1.2)).
Proof.
move=> hX hY hZ.
have h1 := countable_product_association_bijection ha hb hc hX hZ.
have h2 := measure_bijection_product ha (product_measure_is_measure hb hc)
  ha (product_measure_is_measure hc hb) (measure_bijection_identity alpha) (measure_bijection_swap hb hc).
have h3 := measure_bijection_inverse (countable_product_association_bijection ha hc hb hX hY).
exact (measure_bijection_compose (measure_bijection_compose h1 h2) h3).
Qed.
