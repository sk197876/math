(** Federer (1969), 2.4.10, p. 85: reduction of the change-of-density
    formula to nonnegative parts using 2.4.4(6), p. 82. These hold for a
    nonnegative density with the zero-infinity product convention. Source
    editions: PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal topology.
From Federer Require Import ExtendedRealPartial ExtendedRealOrderTopology PartialFunctionUP PartialDensityProduct
  MeasureUpperIntegralPositivePart PartialFunctionIntegralParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ereal_scope.

(** Source for [density_product_positive_part]: Supporting Federer 2.4.10,
    p. 85. *)
Lemma density_product_positive_part (R : realType) (a b : \bar R) :
  0 <= b -> extended_positive_part (a*b)=extended_positive_part a*b.
Proof.
move=> hb; rewrite /extended_positive_part; have [ha|ha] := leP 0 a.
- by rewrite max_l //; exact: mule_ge0 ha hb.
- rewrite mul0e max_r //; exact: mule_le0_ge0 (ltW ha) hb.
Qed.

(** Source for [density_product_negative_part]: Supporting Federer 2.4.10,
    p. 85. *)
Lemma density_product_negative_part (R : realType) (a b : \bar R) :
  0 <= b -> extended_negative_part (a*b)=extended_negative_part a*b.
Proof. by move=> hb; rewrite /extended_negative_part -mulNe density_product_positive_part. Qed.

(** Source for [partial_density_positive_part_graph]: exact positive-part
    graph identity for the final reduction in Federer 2.4.10, p. 85 *)
Lemma partial_density_positive_part_graph (R : realType) (X : Type)
    (f h : partial_function X (extended_real_line R)) :
  (forall x b, partial_function_graph h x b -> 0 <= b) -> forall x z,
  partial_function_graph (partial_density_product (partial_extended_function_positive_part f) h) x z <->
  partial_function_graph (partial_extended_function_positive_part (partial_density_product f h)) x z.
Proof.
move=> hp x z; rewrite partial_density_product_graph; split.
- move=> [a [b [[c [hc eca]] [hb hab]]]]; exists (c*b); split.
  + apply/partial_density_product_graph; exists c,b; by split=> //; split.
  + by rewrite density_product_positive_part ?(hp x b hb) // eca.
- move=> [y [hy eyz]]; have [a [b [ha [hb hab]]]] := (partial_density_product_graph f h x y).1 hy.
  exists (extended_positive_part a),b; split; first by exists a; split.
  split=> //; by rewrite -density_product_positive_part ?(hp x b hb) // hab.
Qed.

(** Source for [partial_density_negative_part_graph]: exact negative-part
    graph identity for the final reduction in Federer 2.4.10, p. 85 *)
Lemma partial_density_negative_part_graph (R : realType) (X : Type)
    (f h : partial_function X (extended_real_line R)) :
  (forall x b, partial_function_graph h x b -> 0 <= b) -> forall x z,
  partial_function_graph (partial_density_product (partial_extended_function_negative_part f) h) x z <->
  partial_function_graph (partial_extended_function_negative_part (partial_density_product f h)) x z.
Proof.
move=> hp x z; rewrite partial_density_product_graph; split.
- move=> [a [b [[c [hc eca]] [hb hab]]]]; exists (c*b); split.
  + apply/partial_density_product_graph; exists c,b; by split=> //; split.
  + by rewrite density_product_negative_part ?(hp x b hb) // eca.
- move=> [y [hy eyz]]; have [a [b [ha [hb hab]]]] := (partial_density_product_graph f h x y).1 hy.
  exists (extended_negative_part a),b; split; first by exists a; split.
  split=> //; by rewrite -density_product_negative_part ?(hp x b hb) // hab.
Qed.
