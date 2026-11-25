(** Federer (1969), 2.3.8, p. 78: zero pseudodistance means almost equality.
    These graph lemmas distinguish a zero difference from absent values.
    Source context and domain correction: PartialNormedArithmetic.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic MeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_difference_positive_locus]: supporting
    exact positive-distance locus for Federer 2.3.8, p. 78:
    the functions are both defined and have unequal values. *)
Lemma partial_difference_positive_locus (R : realType) (X : Type) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (f g : partial_function X V) :
  partial_norm_superlevel N (partial_vector_subtract f g) 0 =
    (partial_function_domain f `&` partial_function_domain g) `\` partial_function_agreement f g.
Proof.
apply/seteqP; split.
- move=> x [z [hz hp]].
  have [a [b [ha [hb he]]]] := proj1 (partial_vector_subtract_graph f g x z) hz.
  split; first by split; [exists a|exists b].
  move=> [y [hfy hgy]].
  have ea := partial_function_single_valued ha hfy.
  have eb := partial_function_single_valued hb hgy.
  have hp' : (0 < N z)%R := hp.
  by move: hp'; rewrite he ea eb subrr (real_seminorm_zero hN.1) ltxx.
- move=> x [[[a ha] [b hb]] hn].
  exists (a-b)%R; split.
  + apply: (proj2 (partial_vector_subtract_graph f g x _)); exists a,b; by split=> //; split.
  + change (0 < N (a-b))%R.
    rewrite (real_norm_positive hN.1 hN.2) subr_eq0.
    apply/negP=> /eqP he; apply: hn; exists a; split=> //; by rewrite he.
Qed.
