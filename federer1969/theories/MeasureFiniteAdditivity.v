(** Federer (1969), 2.1.3(3),(7), pp. 55-56: finite additivity and
    inclusion-exclusion. it does not list Federer's (7). *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_disjoint_union]: Federer 2.1.3,
    p. 55, inductive step in the proof of (3). A measurable piece
    splits a disjoint union; the other piece need not be measurable. *)
Lemma measure_disjoint_union (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (A B : set I) :
  measure_measurable mu A -> (forall x, A x -> B x -> False) ->
  mu (A `|` B) = mu A + mu B.
Proof.
move=> hA hd; rewrite (hA (A `|` B)).
have hi : (A `|` B) `&` A = A.
  apply/seteqP; split=> [x [_ ha]|x ha] //; by split; first left.
have he : (A `|` B) `\` A = B.
  apply/seteqP; split.
  - move=> x [[ha|hb] hna] //; by exfalso; exact: hna.
  - move=> x hb; split; first by right.
    move=> ha; exact: hd x ha hb.
by rewrite hi he.
Qed.

(** Source for [measure_inclusion_exclusion]: Federer 2.1.3(7), p. 55, with
    proof p. 56; one set is measurable, the other arbitrary. This equality
    permits infinite values and involves no subtraction. *)
Lemma measure_inclusion_exclusion (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (A B : set I) :
  measure_measurable mu A ->
  mu A + mu B = mu (A `&` B) + mu (A `|` B).
Proof.
move=> hA.
have hu : A `|` B = A `|` (B `\` A).
  apply/seteqP; split.
  - move=> x [ha|hb]; first by left.
    case: (pselect (A x))=> ha; [by left|right; by split].
  - by move=> x [ha|[hb _]]; [left|right].
have hd : forall x, A x -> (B `\` A) x -> False by move=> x ha [_ hna]; exact: hna.
rewrite hu (measure_disjoint_union hA hd) (hA B) (setIC B A).
by rewrite !addeA (addeC (mu A) (mu (A `&` B))).
Qed.

(** Source for [measure_finite_disjoint_additivity]: Federer
    2.1.3(3), p. 55, finite-union induction in the proof. This
    supporting version indexes the finite family by a finite set,
    rather than an initial segment of the positive integers. *)
Lemma measure_finite_disjoint_additivity (R : realType)
    (I J : choiceType) (mu : set I -> \bar R) (hm : is_measure mu)
    (F : J -> set I) (B : {fset J}) :
  (forall j, j \in B -> measure_measurable mu (F j)) ->
  (forall j k, j \in B -> k \in B -> j != k ->
    forall x, F j x -> F k x -> False) ->
  mu (\bigcup_(j in [set` B]) F j) = \sum_(j <- B) mu (F j).
Proof.
elim/fset1U_rect: B=> [|a B ha IH] hF hd.
- by rewrite set_fset0 bigcup_set0 big_seq_fset0 (measure_empty hm).
- rewrite set_fsetU1 bigcup_setU1 big_fsetU1 //.
  have hFa : measure_measurable mu (F a) by apply: hF; rewrite !inE eqxx.
  have hdis : forall x, F a x -> (\bigcup_(j in [set` B]) F j) x -> False.
    move=> x hax [j hj hjx].
    have hne : a != j by apply/eqP=> he; move: ha; rewrite he hj.
    apply: (hd a j _ _ hne x hax hjx); by rewrite !inE ?eqxx ?hj ?orbT.
  rewrite (measure_disjoint_union hFa hdis) IH //.
  + by move=> j hj; apply: hF; rewrite !inE hj orbT.
  + move=> j k hj hk; apply: hd; by rewrite !inE ?hj ?hk ?orbT.
Qed.
