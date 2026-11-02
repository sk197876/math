(** Supporting Federer (1969), 2.10.47(1), pp. 204–205: finite closed cells
    whose overlaps are null can be summed just as disjoint interiors can.
    This is a consequence of 2.1.3(3),(6),(7), p. 55, with no finiteness
    hypothesis on the measure values. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureFiniteAdditivity MeasureAlmostBasic NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_finite_null_overlap_additivity]:
    supporting finite sum in 2.10.47(1), pp. 204–205.
    Applied to the restricted content, this allows closed
    cubes instead of deleting their null boundaries first. *)
Theorem measure_finite_null_overlap_additivity (R : realType)
    (X J : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
    (F : J -> set X) (B : {fset J}) :
  (forall j, j \in B -> measure_measurable mu (F j)) ->
  (forall j k, j \in B -> k \in B -> j != k -> mu (F j `&` F k)=0) ->
  mu (\bigcup_(j in [set` B]) F j)=\sum_(j <- B) mu (F j).
Proof.
elim/fset1U_rect: B=> [|a B ha IH] hF hd.
- by rewrite set_fset0 bigcup_set0 big_seq_fset0 (measure_empty hm).
- rewrite set_fsetU1 bigcup_setU1 big_fsetU1 //.
  have hFa : measure_measurable mu (F a) by apply: hF; rewrite !inE eqxx.
  have hz : mu (F a `&` (\bigcup_(j in [set` B]) F j))=0.
    apply: (@measure_null_subset R X mu hm _ (\bigcup_(j in [set` B]) (F a `&` F j))).
    + move=> x [hax [j hj hjx]]; exists j=> //; by split.
    + apply: (measure_null_countable_union hm (finite_set_countable (finite_fset B)))=> j hj.
      have hne : a != j by apply/eqP=> he; move: ha; rewrite he hj.
      apply: (hd a j _ _ hne); by rewrite !inE ?eqxx ?hj ?orbT.
  have he := @measure_inclusion_exclusion R X mu (F a) (\bigcup_(j in [set` B]) F j) hFa.
  rewrite hz add0e in he; rewrite -he IH //.
  + by move=> j hj; apply: hF; rewrite !inE hj orbT.
  + move=> j k hj hk; apply: hd; by rewrite !inE ?hj ?hk ?orbT.
Qed.

(** Source for [measure_finite_family_null_overlap_additivity]:
    supporting finite-family formulation of the sum in
    2.10.47(1), pp. 204–205, using the book's
    arbitrary-set summation convention from 2.1.1, p. 52. *)
Corollary measure_finite_family_null_overlap_additivity (R : realType)
    (X J : choiceType) (mu : set X -> \bar R) (hm : is_measure mu)
    (F : J -> set X) (D : set J) :
  finite_set D ->
  (forall j, D j -> measure_measurable mu (F j)) ->
  (forall j k, D j -> D k -> j != k -> mu (F j `&` F k)=0) ->
  mu (\bigcup_(j in D) F j)=nonnegative_sum D (fun j=>mu (F j)).
Proof.
move=> /finite_fsetP [B ->] hF hd.
rewrite (@nonnegative_sum_finite R J B (fun j=>mu (F j))
  (fun j _=>@measure_nonnegative R X mu hm (F j))).
exact: measure_finite_null_overlap_additivity hF hd.
Qed.
