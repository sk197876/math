(** Every finite cylinder cover of the binary product has cost at least one.
    This finite counting argument supports the concrete counterexample to
    Federer (1969), 2.3.8, p. 78, and its covering measure from 2.10.1, p.
    170. Source context and the different interval example. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumScale NonnegativeSumContinuity
  MeasureUP MeasureIndexedCover CountingMeasure CountingFinitePredicate
  BinarySequenceCylinders BinaryCylinderCost BinaryCylinderFiniteTrace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [binary_finite_cylinder_cover_cost]: finite
    combinatorial lower bound for the local counterexample to
    Federer 2.3.8, p. 78. Count all words at a
    common finer level, apply counting-measure subadditivity, and
    divide by the number of such words. *)
Lemma binary_finite_cylinder_cover_cost (R : realType) (G : {fset seq bool}) :
  @setT binary_sequence_space `<=` \bigcup_(w in [set` G]) binary_cylinder w ->
  1 <= nonnegative_sum [set` G] (@binary_cylinder_cost R).
Proof.
move=> hcov.
have [n hn] : exists n, forall w, w \in G -> (size w <= n)%N.
  apply: (@finite_increasing_cover [the eqType of (seq bool : Type)] (fun n => [set w | (size w <= n)%N]) G).
  - move=> n m hnm w hw; exact: leq_trans hw hnm.
  - move=> w hw; exists (size w); exact: leqnn.
pose I := [the finType of n.-tuple bool].
pose T w : set I := [set u | binary_cylinder w (binary_word_sequence u)].
have hc : @setT I `<=` \bigcup_(w in [set` G]) T w.
  move=> u _; exact: hcov (binary_word_sequence u) Logic.I.
have hb := @measure_indexed_cover R I [the choiceType of (seq bool : Type)]
  (@counting_measure R I) (counting_measure_is_measure R I) setT [set` G] T
  (finite_set_countable (finite_fset G)) hc.
have ht w (hw : w \in G) : counting_measure (R:=R) (T w) =
    ((2 : R)^+n)%:E * (@binary_cylinder_cost R w).
  rewrite /T (@binary_cylinder_trace_count R n w (hn w hw)).
  exact (@binary_cylinder_cost_refinement R n w (hn w hw)).
have hpow : (0 < (2 : R)^+n)%R by rewrite exprn_gt0 // ltr0n.
have he : nonnegative_sum [set` G] (fun w => counting_measure (R:=R) (T w)) =
    ((2 : R)^+n)%:E * nonnegative_sum [set` G] (@binary_cylinder_cost R).
  have hcost w (hw : [set` G] w) : 0 <= @binary_cylinder_cost R w := ltW (binary_cylinder_cost_positive R w).
  rewrite -(@nonnegative_sum_scale R [the choiceType of (seq bool : Type)] [set` G]
    (@binary_cylinder_cost R) ((2 : R)^+n)%R (ltW hpow) hcost).
  apply: nonnegative_sum_ext=> w hw; exact: ht hw.
rewrite counting_finite_whole /I card_tuple card_bool natrX he in hb.
move: hb; rewrite -{1}[((2 : R)^+n)%:E]mule1 lee_pmul2l //.
Qed.
