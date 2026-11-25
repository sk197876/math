(** Federer (1969), 2.1.1(7), p. 53: adding two defined sums without
    opposite infinities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NumericalSumValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_difference_finite_sides]: Federer
    2.1.1(5),(7), pp. 52-53; supporting identification of which
    variation is finite from the value of a defined difference. *)
Lemma nonnegative_difference_finite_sides (R : realType) (p n z : \bar R) :
  0 <= p -> 0 <= n -> extended_subtract p n = Some z ->
  ((p < +oo) = (z < +oo)) /\ ((n < +oo) = (-oo < z)).
Proof.
case: p=> [p| |]; case: n=> [n| |] //= hp hn;
  rewrite /extended_subtract /extended_add /adde_def /= ?eqxx //;
  move=> [<-]; by rewrite ?ltry ?ltNyr ?ltxx.
Qed.

(** Source for [extended_add_same_side_finite]: Federer
    2.1.1(7), p. 53; supporting arithmetic observation: a defined
    sum excludes opposite infinities, hence one common side is finite. *)
Lemma extended_add_same_side_finite (R : realType) (a b : \bar R) :
  adde_def a b ->
  ((a < +oo) && (b < +oo)) || ((-oo < a) && (-oo < b)).
Proof.
case: a=> [a| |]; case: b=> [b| |];
  by rewrite /adde_def /= ?eqxx ?ltry ?ltNyr ?ltxx.
Qed.

(** Source for [nonnegative_differences_add_domain]: Federer
    2.1.1(7), p. 53; the total positive or negative variation
    of the sum is finite under the printed hypothesis. *)
Lemma nonnegative_differences_add_domain (R : realType) (p n q m a b : \bar R) :
  0 <= p -> 0 <= n -> 0 <= q -> 0 <= m ->
  extended_subtract p n = Some a -> extended_subtract q m = Some b ->
  adde_def a b -> (p+q < +oo) || (n+m < +oo).
Proof.
move=> hp hn hq hm ha hb hd.
have [hpa hna] := nonnegative_difference_finite_sides hp hn ha.
have [hqb hmb] := nonnegative_difference_finite_sides hq hm hb.
have := extended_add_same_side_finite hd.
rewrite -hpa -hna -hqb -hmb => /orP[/andP[h1 h2]|/andP[h1 h2]]; apply/orP.
- left; exact: lte_add_pinfty.
- right; exact: lte_add_pinfty.
Qed.

(** Source for [extended_parts_difference]: Federer 2.1.1,
    p. 52, second display; the total arithmetic agrees with the
    already proved, always defined difference of the two parts. *)
Lemma extended_parts_difference (R : realType) (x : \bar R) :
  extended_positive_part x - extended_negative_part x = x.
Proof. exact: extended_subtract_value (extended_positive_negative_parts x). Qed.

(** Source for [nonnegative_differences_add_identity]: Federer
    2.1.1(7), p. 53; supporting regrouping of four nonnegative
    variations. Application to partial sums separately checks the domain. *)
Lemma nonnegative_differences_add_identity (R : realType) (p n q m : \bar R) :
  0 <= n -> 0 <= m -> (p+q)-(n+m) = (p-n)+(q-m).
Proof.
move=> hn hm; rewrite oppeD; last exact: ge0_adde_def.
exact: addeACA.
Qed.

(** Source for [extended_add_parts_difference]: Federer
    2.1.1(7), p. 53; the sum of two values is the difference
    of their combined positive and negative parts. *)
Lemma extended_add_parts_difference (R : realType) (x y : \bar R) :
  (extended_positive_part x + extended_positive_part y) -
  (extended_negative_part x + extended_negative_part y) = x+y.
Proof.
rewrite nonnegative_differences_add_identity ?extended_negative_part_nonnegative //.
by rewrite !extended_parts_difference.
Qed.

(** Source for [extended_add_parts_domain]: Federer 2.1.1(7),
    p. 53; a defined difference of the combined variations excludes
    opposite infinities in the two original values. *)
Lemma extended_add_parts_domain (R : realType) (x y : \bar R) :
  adde_def (extended_positive_part x + extended_positive_part y)
    (- (extended_negative_part x + extended_negative_part y)) -> adde_def x y.
Proof.
case: x=> [x| |]; case: y=> [y| |];
  rewrite /extended_negative_part /extended_positive_part /adde_def /= //;
  by rewrite ?maxNye ?maxye ?add0e ?adde0 ?eqxx.
Qed.
