(** Local correction to Federer (1969), 2.6.5, p. 119. If gamma gives
    infinite measure to every nonempty subset of Z, beta times gamma gives
    infinite measure to any set with positive beta-measure projection onto
    Y. This generalises the intermediate claim from Lebesgue beta to any
    measure. No associativity correction occurs in the local Federer
    erratum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic
  ProductMeasure ProductMeasureSequenceInfimum PositiveCoverMember.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [product_first_projection]: Supporting Federer 2.6.5, p. 119. *)
Definition product_first_projection (Y Z : Type) (E : set (Y * Z)) : set Y :=
  [set y | exists z, E (y,z)].

(** Source for [infinite_product_positive_projection]: Supporting Federer
    2.6.1, pp. 114–115. *)
Theorem infinite_product_positive_projection (R : realType) (Y Z : choiceType)
    (beta : set Y -> \bar R) (gamma : set Z -> \bar R)
    (hb : is_measure beta) (hg : is_measure gamma)
    (hginf : forall C, (exists z, C z) -> gamma C = +oo) (E : set (Y * Z)) :
  0 < beta (product_first_projection E) -> product_measure hb hg E = +oo.
Proof.
move=> hp; apply/eqP; rewrite eq_le leey /=.
apply: (product_measure_sequence_cover_greatest hb hg)=> B C hm hc.
pose D n : set Y := [set y | B n y /\ exists z, C n z].
have hcover : product_first_projection E `<=` \bigcup_n D n.
  move=> y [z hyz]; have [n _ [hy hz]] := hc (y,z) hyz.
  exists n=> //; split=> //; by exists z.
have [n hn] := @positive_countable_cover_member R Y beta hb
  (product_first_projection E) D hp hcover.
have hB : 0 < beta (B n).
  apply: lt_le_trans hn _; apply: (measure_mono hb)=> y [hy _]; exact hy.
have hC : exists z, C n z.
  apply: contrapT=> hnone.
  have he : D n = set0.
    apply/seteqP; split=> y; last by [].
    by move=> [_ h]; exfalso; exact: hnone h.
  by rewrite he (measure_empty hb) ltxx in hn.
have hcost : beta (B n) * gamma (C n) = +oo.
  by rewrite (hginf _ hC) gt0_muley.
rewrite -hcost; exact: nonnegative_sum_term I.
Qed.
