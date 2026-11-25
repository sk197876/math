(** Federer (1969), 2.1.5(5), p. 57: supporting properties of restriction
    needed to identify its measurable sets. The restriction itself is 2.1.2,
    p. 54. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_restrict_subset_value]: Federer
    2.1.5(5), proof p. 57; restriction by S has its original
    value on every subset of S. Supporting identity from 2.1.2. *)
Lemma measure_restrict_subset_value (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (S A : set I) :
  A `<=` S -> measure_restrict mu S A = mu A.
Proof.
move=> h; rewrite /measure_restrict.
have he : S `&` A = A.
  apply/seteqP; split=> [x [_ hx]|x hx] //; split=> //; exact: h.
by rewrite he.
Qed.

(** Source for [measure_restrict_outside_null]: Federer
    2.1.5(5), p. 57, supporting fact for the arbitrary set C outside
    S: its restricted measure is zero, without a measurability condition. *)
Lemma measure_restrict_outside_null (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (S C : set I) :
  C `<=` ~` S -> measure_restrict mu S C = 0.
Proof.
move=> h; rewrite /measure_restrict.
have he : S `&` C = set0.
  apply/seteqP; split=> [x [hs hc]|x []]; exact: h x hc hs.
by rewrite he (measure_empty hm).
Qed.

(** Source for [measure_restrict_support_measurable]: Federer
    2.1.5(5), p. 57, supporting reduction of a restricted measurable
    set to its intersection with S. S is measurable for phi L S
    even when S is not measurable for phi. *)
Lemma measure_restrict_support_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (S : set I) :
  measure_measurable (measure_restrict mu S) S.
Proof.
move=> T; rewrite /measure_restrict.
have hi : S `&` (T `&` S) = S `&` T.
  apply/seteqP; split=> [x [hs [ht _]]|x [hs ht]]; by split=> //; split.
have hd : S `&` (T `\` S) = set0.
  apply/seteqP; split=> [x [hs [ht hn]]|x []]; exact: hn hs.
by rewrite hi hd (measure_empty hm) adde0.
Qed.
