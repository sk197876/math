(** Federer (1969), 2.5.11, p. 102: beta_j measures Y_j, its measurable sets
    are the subsets of cardinal less than aleph_j and their complements, and
    the whole space has measure one. The laws are derived from the two
    defining clauses and the countable-union hypothesis of
    CardinalMeasureUP.v. Kelley, General Topology, Appendix, Theorem 180, p.
    280 (Dover 2017 reprint of 1955), is the cardinal background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureFiniteClosure
  CardinalMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

Section Laws.
Variable R : realType.
Variable K : choiceType.
Variable K' : Type.
Variable P : set K'.
Hypothesis hP : is_sigma_small_bound K P.
Local Notation beta := (@cardinal_measure R K K' P).

(** Source for [cardinal_small_union]: supporting binary case of the
    countable-union requirement for beta_j in Federer 2.5.11, p. 102. *)
Lemma cardinal_small_union (A B : set K) : A #<= P -> B #<= P -> A `|` B #<= P.
Proof.
move=> hA hB.
have -> : A `|` B = \bigcup_(C in [set A] `|` [set B]) C.
  apply/seteqP; split=> [x [hx|hx]|x [C [->|->] hx]].
  - by exists A=> //; left.
  - by exists B=> //; right.
  - by left.
  - by right.
apply: hP; last by move=> C [->|->].
by apply: finite_set_countable; rewrite finite_setU; split; exact: finite_set1.
Qed.

(** Source for [cardinal_measure_is_measure]: Federer 2.5.11, p. 102,
    beta_j is a measure over Y_j. If some member of a countable cover
    is large the sum is at least one; otherwise the union is small. *)
Theorem cardinal_measure_is_measure : is_measure beta.
Proof.
constructor; first by move=> A; exact: cardinal_measure_nonnegative.
move=> A F hF hsub.
case: (pselect (exists B, F B /\ ~ (B #<= P)))=> [[B [hB hn]]|hall].
- apply: le_trans (cardinal_measure_le1 R P A) _.
  by rewrite -(cardinal_measure_large R hn); exact: nonnegative_sum_term hB.
- have hsmall : forall B, F B -> B #<= P.
    by move=> B hB; apply: contrapT=> hn; apply: hall; exists B.
  rewrite cardinal_measure_small; first exact: nonnegative_sum_nonnegative.
  exact: card_le_trans (subset_card_le hsub) (hP hF hsmall).
Qed.

(** Source for [cardinal_measure_small_measurable]: supporting
    measurability of the null sets of beta_j, Federer 2.5.11, p. 102,
    by the null-set law of 2.1.3(6), p. 55. *)
Lemma cardinal_measure_small_measurable (A : set K) :
  A #<= P -> measure_measurable beta A.
Proof.
move=> h; apply: (measure_null_measurable cardinal_measure_is_measure).
exact: cardinal_measure_small.
Qed.

(** Source for [cardinal_measure_cosmall_measurable]: supporting
    measurability of the complements of null sets of beta_j, Federer
    2.5.11, p. 102, by 2.1.3(3), p. 55. *)
Lemma cardinal_measure_cosmall_measurable (A : set K) :
  ~` A #<= P -> measure_measurable beta A.
Proof.
move=> h; rewrite -(setCK A); apply: measure_measurable_complement.
exact: cardinal_measure_small_measurable.
Qed.

(** Source for [cardinal_measure_measurable_iff]: the beta_j
    measurable sets used in Federer 2.5.11, p. 102: exactly the
    sets of cardinal less than aleph_j and their complements. A set
    with large complement and large intersection fails the
    Caratheodory test on the whole space. *)
Theorem cardinal_measure_measurable_iff (A : set K) :
  measure_measurable beta A <-> (A #<= P \/ ~` A #<= P).
Proof.
split=> [h|[h|h]]; [|exact: cardinal_measure_small_measurable|exact: cardinal_measure_cosmall_measurable].
apply: contrapT=> hn.
have hA : ~ (A #<= P) by move=> h'; apply: hn; left.
have hC : ~ (~` A #<= P) by move=> h'; apply: hn; right.
have := h setT; rewrite setTI setTD (cardinal_measure_large R hA) (cardinal_measure_large R hC).
move=> heq; have := cardinal_measure_le1 R P (@setT K); rewrite heq -EFinD lee_fin leNgt.
by move=> /negP; apply; rewrite ltrDl ltr01.
Qed.

(** Source for [cardinal_measure_whole]: beta_j(Y_j)=1 in Federer
    2.5.11, p. 102, since Y_j has cardinal aleph_j. *)
Lemma cardinal_measure_whole : ~ ((@setT K) #<= P) -> beta setT = 1.
Proof. exact: cardinal_measure_large. Qed.

(** Source for [cardinal_measure_union_large]: supporting continuity
    of beta_j along sequences of sets, Federer 2.5.11, p. 102: a
    large countable union has a large member. *)
Lemma cardinal_measure_union_large (V : nat -> set K) :
  ~ (\bigcup_n V n #<= P) -> exists n, ~ (V n #<= P).
Proof.
move=> h; apply: contrapT=> hn; apply: h.
have hall : forall n, V n #<= P.
  by move=> n; apply: contrapT=> h'; apply: hn; exists n.
have -> : \bigcup_n V n = \bigcup_(B in V @` setT) B.
  apply/seteqP; split=> [x [n _ hx]|x [B [n _ <-] hx]]; last by exists n.
  by exists (V n)=> //; exists n.
apply: hP; last by move=> B [n _ <-].
exact: sub_countable (card_image_le V setT) (card_lexx _).
Qed.

End Laws.
