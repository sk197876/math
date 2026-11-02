(** Sums of measures supporting the rectangle obstruction in Federer (1969),
    2.8.20, p. 152. Cesari1939, section II.4, p. 307, sums the nonnegative
    large-average functions at dyadic indices. We use their associated
    finite measures instead; this avoids using a differentiation theorem to
    prove failure of a Vitali relation. The measure laws follow locally from
    Federer's numerical sums 2.1.1(2), (10), pp. 52–53, and the measure
    definition 2.1.2, p. 53. This is supporting infrastructure, not a
    separately numbered book assertion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd NonnegativeSumProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_measure_sum]: abstract specification of
    the sum measure supporting Federer 2.8.20, p. 152,
    through the dyadic sum in Cesari1939, p. 307.
    The value on each set is the existing nonnegative sum;
    this predicate introduces no unproved measure axiom. *)
Definition is_measure_sum (R : realType) (X J : choiceType) (D : set J)
    (mu : J -> set X -> \bar R) (rho : set X -> \bar R) :=
  forall A, rho A = nonnegative_sum D (fun j => mu j A).

(** Source for [measure_sum_is_measure]: supporting sum
    construction for Federer 2.8.20, p. 152. The
    countable-cover inequality follows by interchanging two
    nonnegative sums using 2.1.1(10), p. 53. The
    index set of component measures need not be countable. *)
Lemma measure_sum_is_measure (R : realType) (X J : choiceType) (D : set J)
    (mu : J -> set X -> \bar R) (rho : set X -> \bar R) :
  (forall j, D j -> is_measure (mu j)) -> is_measure_sum D mu rho -> is_measure rho.
Proof.
move=> hm hs; constructor.
- move=> A; rewrite hs; exact: nonnegative_sum_nonnegative.
- move=> A F hF hc; rewrite hs.
  have hb : nonnegative_sum D (fun j => mu j A) <=
      nonnegative_sum D (fun j => nonnegative_sum F (mu j)).
    apply: nonnegative_sum_mono=> j hj; exact (@measure_countable_cover R X (mu j) (hm j hj) A F hF hc).
  apply: le_trans hb _.
  have hn (p : J * set X) : (D `*` F) p -> 0 <= mu p.1 p.2.
    move=> [hj _]; exact: measure_nonnegative (hm p.1 hj) p.2.
  rewrite -(@nonnegative_sum_product_first R J [the choiceType of set X] D F
    (fun p => mu p.1 p.2) hn)
    (@nonnegative_sum_product_second R J [the choiceType of set X] D F
    (fun p => mu p.1 p.2) hn).
  apply: nonnegative_sum_mono=> B hB; by rewrite hs.
Qed.

(** Source for [measure_sum_measurable]: supporting
    measurability for the summed obstruction measure in Federer
    2.8.20, p. 152. A set measurable for each
    component remains measurable for their nonnegative sum,
    by splitting each test set and using 2.1.1(2), p. 52. *)
Lemma measure_sum_measurable (R : realType) (X J : choiceType) (D : set J)
    (mu : J -> set X -> \bar R) (rho : set X -> \bar R) (S : set X) :
  (forall j, D j -> is_measure (mu j)) -> is_measure_sum D mu rho ->
  (forall j, D j -> measure_measurable (mu j) S) -> measure_measurable rho S.
Proof.
move=> hm hs hS T; rewrite !hs.
rewrite -nonnegative_sum_add; last first.
- move=> j hj; exact (@measure_nonnegative R X (mu j) (hm j hj) _).
- move=> j hj; exact (@measure_nonnegative R X (mu j) (hm j hj) _).
apply: nonnegative_sum_ext=> j hj; exact: hS j hj T.
Qed.

(** Source for [measure_sum_component_bound]: supporting
    domination of every finite-scale measure by the dyadic
    sum for Federer 2.8.20, p. 152; Cesari1939,
    p. 307. It uses the single-term bound of
    numerical summation 2.1.1, p. 52. *)
Lemma measure_sum_component_bound (R : realType) (X J : choiceType) (D : set J)
    (mu : J -> set X -> \bar R) (rho : set X -> \bar R) j A :
  is_measure_sum D mu rho -> D j -> mu j A <= rho A.
Proof. move=> hs hj; rewrite hs; exact: nonnegative_sum_term hj. Qed.

(** Source for [measure_sum_exists]: existence of the
    abstract sum measure supporting Federer 2.8.20, p. 152.
    The witness is confined to this opaque proof; later
    arguments use only its defining laws and consequences. *)
Theorem measure_sum_exists (R : realType) (X J : choiceType) (D : set J)
    (mu : J -> set X -> \bar R) : exists rho, is_measure_sum D mu rho.
Proof. exists (fun A => nonnegative_sum D (fun j => mu j A)); by move=> A. Qed.
