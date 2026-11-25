(** Federer (1969), 2.4.8, p. 84: finite pointwise sums are obtained by
    adjoining one summand, using the finite additivity of numerical sums in
    2.1.1(2), p. 52. This graph identity preserves partial domains and
    permits infinite nonnegative values. Source context:
    PartialNumericalSumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealPartial PartialFunctionUP PartialExtendedArithmetic
  PartialNumericalSumUP PartialNumericalSum PartialFiniteNumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_nonnegative_sum_insert_graph]: supporting
    finite-sum recursion for Federer 2.4.8, p. 84,
    derived from the abstract sum graph laws. *)
Lemma partial_nonnegative_sum_insert_graph (R : realType) (X : Type) (J : choiceType)
    (C : {fset J}) (i : J) (f : J -> partial_function X (extended_real_line R)) :
  i \notin C ->
  (forall j, j \in (i |` C)%fset -> forall x y, partial_function_graph (f j) x y -> 0 <= y) ->
  forall x z,
  partial_function_graph (partial_function_numerical_sum [set j | j \in (i |` C)%fset] f) x z <->
  partial_function_graph (partial_extended_function_add (f i)
    (partial_function_numerical_sum [set j | j \in C] f)) x z.
Proof.
move=> hi hp x z.
have hC j : j \in C -> j \in (i |` C)%fset by move=> hj; rewrite in_fset1U hj orbT.
have hiC : i \in (i |` C)%fset by rewrite in_fset1U eqxx.
have hsmall j : j \in C -> forall x y, partial_function_graph (f j) x y -> 0 <= y.
  move=> hj; exact: hp j (hC j hj).
rewrite (@partial_numerical_finite_sum_graph R X J (i |` C)%fset f _
  (partial_function_numerical_sum_laws _ f) hp x z) partial_extended_function_add_graph.
split.
- move=> [u [hu hsum]]; exists (u i),(\sum_(j <- C) u j); split; first exact: hu i hiC.
  split.
  + apply: (partial_numerical_finite_sum_graph (partial_function_numerical_sum_laws _ f) hsmall x _).2.
    exists u; split=> // j hj; exact: hu j (hC j hj).
  + have hpos : 0 <= \sum_(j <- C) u j.
      rewrite big_seq; apply: sume_ge0=> j hj; exact: hp j (hC j hj) x (u j) (hu j (hC j hj)).
    have hpi := hp i hiC x (u i) (hu i hiC).
    rewrite /extended_add (ge0_adde_def hpi hpos).
    by rewrite big_fsetU1 // in hsum; rewrite hsum.
- move=> [a [b [ha [hb hab]]]].
  have [u [hu hsum]] := (partial_numerical_finite_sum_graph
    (partial_function_numerical_sum_laws _ f) hsmall x b).1 hb.
  pose v j := if j == i then a else u j.
  have hvi : v i = a by rewrite /v eqxx.
  have hvC j : j \in C -> v j = u j.
    move=> hj; rewrite /v; case: ifP=> // /eqP eji.
    by move: hi; rewrite -eji hj.
  have hvsum : (\sum_(j <- C) v j) = b.
    rewrite -hsum; apply: eq_big_seq=> j hj; exact: hvC.
  exists v; split.
  + move=> j; rewrite in_fset1U=> /orP[/eqP->|hj].
    * by rewrite hvi.
    * rewrite hvC //; exact: hu j hj.
  + rewrite big_fsetU1 // hvi hvsum.
    rewrite /extended_add in hab; case: (adde_def a b) in hab=> //; by case: hab.
Qed.
