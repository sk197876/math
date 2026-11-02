(** Federer (1969), 2.1.1(8), p. 53: comparison of sums with the printed
    one-sided finiteness condition. editions: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial ExtendedRealAddVariations
  NonnegativeSum NumericalSum NumericalSumValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_positive_part_mono]: Federer
    2.1.1(8), p. 53; supporting monotonicity of positive parts. *)
Lemma extended_positive_part_mono (R : realType) (x y : \bar R) :
  x <= y -> extended_positive_part x <= extended_positive_part y.
Proof. move=> h; apply: le_max2 h _; exact: lexx. Qed.

(** Source for [extended_negative_part_antimono]: Federer
    2.1.1(8), p. 53; supporting reversed comparison of negative parts. *)
Lemma extended_negative_part_antimono (R : realType) (x y : \bar R) :
  x <= y -> extended_negative_part y <= extended_negative_part x.
Proof.
move=> h; apply: extended_positive_part_mono; by rewrite leeN2.
Qed.

(** Source for [numerical_sum_values_mono]: Federer
    2.1.1(8), p. 53; comparison once both sums are known to be
    defined. Existence under the book's weaker premise is proved below. *)
Lemma numerical_sum_values_mono (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) a b :
  (forall x, A x -> f x <= g x) ->
  numerical_sum A f = Some a -> numerical_sum A g = Some b -> a <= b.
Proof.
move=> h ha hb; rewrite -(numerical_sum_value ha) -(numerical_sum_value hb).
apply: leeB; apply: nonnegative_sum_mono=> x hx.
- exact: extended_positive_part_mono (h x hx).
- exact: extended_negative_part_antimono (h x hx).
Qed.

(** Source for [numerical_sum_comparison]: Federer 2.1.1(8), p. 53; either a
    defined lower sum above negative infinity or a defined upper sum below
    positive infinity suffices to make both sums defined and ordered. *)
Theorem numerical_sum_comparison (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) :
  (forall x, A x -> f x <= g x) ->
  ((exists a, numerical_sum A f = Some a /\ -oo < a) \/
   (exists b, numerical_sum A g = Some b /\ b < +oo)) ->
  exists a b, numerical_sum A f = Some a /\ numerical_sum A g = Some b /\ a <= b.
Proof.
move=> h [[a [ha hfa]]|[b [hb hgb]]].
- have [_ hn] := nonnegative_difference_finite_sides
    (nonnegative_sum_nonnegative A (fun x => extended_positive_part (f x)))
    (nonnegative_sum_nonnegative A (fun x => extended_negative_part (f x))) ha.
  have hng : nonnegative_sum A (fun x => extended_negative_part (g x)) < +oo.
    apply: le_lt_trans (_ : nonnegative_sum A (fun x => extended_negative_part (f x)) < +oo).
    + apply: nonnegative_sum_mono=> x hx; exact: extended_negative_part_antimono (h x hx).
    + by rewrite hn.
  have [b hb] : exists b, numerical_sum A g = Some b.
    apply/numerical_sum_defined; by rewrite hng orbT.
  exists a, b; split=> //; split=> //; exact: numerical_sum_values_mono h ha hb.
- have [hp _] := nonnegative_difference_finite_sides
    (nonnegative_sum_nonnegative A (fun x => extended_positive_part (g x)))
    (nonnegative_sum_nonnegative A (fun x => extended_negative_part (g x))) hb.
  have hpf : nonnegative_sum A (fun x => extended_positive_part (f x)) < +oo.
    apply: le_lt_trans (_ : nonnegative_sum A (fun x => extended_positive_part (g x)) < +oo).
    + apply: nonnegative_sum_mono=> x hx; exact: extended_positive_part_mono (h x hx).
    + by rewrite hp.
  have [a ha] : exists a, numerical_sum A f = Some a.
    apply/numerical_sum_defined; by rewrite hpf.
  exists a, b; split=> //; split=> //; exact: numerical_sum_values_mono h ha hb.
Qed.
