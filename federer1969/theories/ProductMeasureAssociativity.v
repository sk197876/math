(** Corrected form of Federer (1969), 2.6.5, p. 119. Our extremal-measure
    proof needs countability only of the first and third factors. It uses
    2.6.1, p. 115, and the rectangle equality of 2.6.2(2), p. 115. This is a
    local correction, not one in Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasurePushforward MeasureRestriction
  CountablyMeasurableUP ProductMeasure TripleProductFiniteSlices CountableCylinderBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_associate]: the map s of Federer 2.6.5, p. 119 *)
Definition product_associate (X Y Z : Type) (p : (X * Y) * Z) : X * (Y * Z) :=
  (p.1.1,(p.1.2,p.2)).

(** Source for [product_unassociate]: inverse of the map s in Federer 2.6.5,
    p. 119, supporting the corrected equality. *)
Definition product_unassociate (X Y Z : Type) (p : X * (Y * Z)) : (X * Y) * Z :=
  ((p.1,p.2.1),p.2.2).

Section Associativity.
Variable R : realType.
Variables X Y Z : choiceType.
Variable alpha : set X -> \bar R.
Variable beta : set Y -> \bar R.
Variable gamma : set Z -> \bar R.
Hypothesis ha : is_measure alpha.
Hypothesis hb : is_measure beta.
Hypothesis hg : is_measure gamma.

(** Source for [associated_product_rectangle_bound]: supporting rectangle
    bound for corrected Federer 2.6.5, p. 119 (. Exhaust only the first
    factor by finite measurable sets; the middle and last factors need not
    be countably measurable for this inequality. *)
Lemma associated_product_rectangle_bound :
  measure_countably_measurable alpha setT ->
  forall A B, measure_measurable alpha A ->
    measure_measurable (product_measure hb hg) B ->
  measure_pushforward (@product_associate X Y Z)
    (product_measure (product_measure_is_measure ha hb) hg) (A `*` B) <=
  alpha A * product_measure hb hg B.
Proof.
move=> hX A B hA hB.
change (left_triple_slice_measure ha hb hg A B <= alpha A * product_measure hb hg B).
apply: (@countably_measurable_cylinder_bound R X ((X * Y) * Z)%type
  alpha (product_measure (product_measure_is_measure ha hb) hg) ha
  (product_measure_is_measure (product_measure_is_measure ha hb) hg)
  (fun p => p.1.1) ((fun p => (p.1.2,p.2)) @^-1` B)
  (product_measure hb hg B) hX (measure_nonnegative (product_measure_is_measure hb hg) B) _ A hA).
move=> C hC hf.
exact (@left_triple_finite_slice_bound R X Y Z alpha beta gamma ha hb hg C B hC hf).
Qed.

(** Source for [unassociated_product_rectangle_bound]: symmetric supporting
    bound for corrected Federer 2.6.5, p. 119 (. *)
Lemma unassociated_product_rectangle_bound :
  measure_countably_measurable gamma setT ->
  forall A C, measure_measurable (product_measure ha hb) A ->
    measure_measurable gamma C ->
  measure_pushforward (@product_unassociate X Y Z)
    (product_measure ha (product_measure_is_measure hb hg)) (A `*` C) <=
  product_measure ha hb A * gamma C.
Proof.
move=> hZ A C hA hC; rewrite muleC.
have he : measure_pushforward (@product_unassociate X Y Z)
    (product_measure ha (product_measure_is_measure hb hg)) (A `*` C) =
    right_triple_slice_measure ha hb hg C A.
  rewrite /measure_pushforward /right_triple_slice_measure /measure_pushforward /measure_restrict.
  congr (product_measure ha (product_measure_is_measure hb hg) _).
  apply/seteqP; split; move=> [x [y z]] /=; by move=> [h1 h2]; split.
rewrite he.
apply: (@countably_measurable_cylinder_bound R Z (X * (Y * Z))%type
  gamma (product_measure ha (product_measure_is_measure hb hg)) hg
  (product_measure_is_measure ha (product_measure_is_measure hb hg))
  (fun p => p.2.2) ((fun p => (p.1,p.2.1)) @^-1` A)
  (product_measure ha hb A) hZ (measure_nonnegative (product_measure_is_measure ha hb) A) _ C hC).
move=> D hD hf.
exact (@right_triple_finite_slice_bound R X Y Z alpha beta gamma ha hb hg D A hD hf).
Qed.

(** Source for [product_measure_associate_le]: supporting first extremal
    comparison for corrected Federer 2.6.5, p. 119 (. Countability of the
    first factor suffices for this direction. *)
Lemma product_measure_associate_le :
  measure_countably_measurable alpha setT -> forall S,
  measure_pushforward (@product_associate X Y Z)
    (product_measure (product_measure_is_measure ha hb) hg) S <=
  product_measure ha (product_measure_is_measure hb hg) S.
Proof.
move=> hX S.
apply: (product_measure_greatest ha (product_measure_is_measure hb hg)); last exact: associated_product_rectangle_bound hX.
exact: measure_pushforward_is_measure (product_measure_is_measure (product_measure_is_measure ha hb) hg).
Qed.

(** Source for [product_measure_unassociate_le]: supporting reverse extremal
    comparison for corrected Federer 2.6.5, p. 119 (. *)
Lemma product_measure_unassociate_le :
  measure_countably_measurable gamma setT -> forall S,
  measure_pushforward (@product_unassociate X Y Z)
    (product_measure ha (product_measure_is_measure hb hg)) S <=
  product_measure (product_measure_is_measure ha hb) hg S.
Proof.
move=> hZ S.
apply: (product_measure_greatest (product_measure_is_measure ha hb) hg); last exact: unassociated_product_rectangle_bound hZ.
exact: measure_pushforward_is_measure (product_measure_is_measure ha (product_measure_is_measure hb hg)).
Qed.

(** Source for [product_measure_associative_outer_countable]: corrected
    equality of Federer 2.6.5, p. 119, with countability required only of
    the outer factors. The proof above establishes this weaker sufficient
    hypothesis. *)
Theorem product_measure_associative_outer_countable :
  measure_countably_measurable alpha setT -> measure_countably_measurable gamma setT ->
  measure_pushforward (@product_associate X Y Z)
    (product_measure (product_measure_is_measure ha hb) hg) =
  product_measure ha (product_measure_is_measure hb hg).
Proof.
move=> hX hZ; apply: funext=> S; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (product_measure_associate_le hX S).
- have h := product_measure_unassociate_le hZ ((@product_associate X Y Z) @^-1` S).
  have he : (@product_unassociate X Y Z) @^-1` ((@product_associate X Y Z) @^-1` S) = S.
    by apply/seteqP; split; move=> [x [y z]].
  by rewrite /measure_pushforward he in h.
Qed.

(** Source for [product_measure_associative_countable]: Supporting Federer
    2.6.5, p. 119.All three spaces are countably measurable, including the
    condition on Z whose necessity in general is shown *)
Corollary product_measure_associative_countable :
  measure_countably_measurable alpha setT -> measure_countably_measurable beta setT ->
  measure_countably_measurable gamma setT ->
  measure_pushforward (@product_associate X Y Z)
    (product_measure (product_measure_is_measure ha hb) hg) =
  product_measure ha (product_measure_is_measure hb hg).
Proof. by move=> hX _ hZ; exact: product_measure_associative_outer_countable hX hZ. Qed.

End Associativity.
