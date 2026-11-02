(** Federer (1969), 2.10.43, printed p. 201: the finite-ball scale argument
    uses positive distances from the new source point to the finitely many
    original source points. These supporting finite-sum lemmas allow
    nonnegative weights of total one, including zero entries, instead of
    pruning the representation to strictly positive coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_unit_weight_positive_entry]: supporting
    finite coefficient fact for the last scale
    inequality in 2.10.43, p. 201. Any finite
    real family of total one has a positive entry. *)
Lemma finite_unit_weight_positive_entry (R : realType) (I : finType) (w : I -> R) :
  (\sum_i w i= 1) -> exists i, 0<w i.
Proof.
move=> hsum; apply: contrapT=> hnone.
have hle i : w i<=0.
  rewrite leNgt; apply/negP=> hi; apply: hnone; by exists i.
have hs : \sum_i w i<=0 by apply: sumr_le0=> i _; exact: hle.
rewrite hsum in hs.
have hh := lt_le_trans (@ltr01 R) hs; by rewrite ltxx in hh.
Qed.

(** Source for [finite_positive_weighted_budget]: supporting
    strict positivity in the finite-ball argument of
    2.10.43, p. 201. Nonnegative weights of
    total one and strictly positive costs give a
    strictly positive weighted total, even with zero weights. *)
Lemma finite_positive_weighted_budget (R : realType) (I : finType) (w a : I -> R) :
  (forall i, 0<=w i) -> (\sum_i w i= 1) -> (forall i, 0<a i) ->
  0<\sum_i w i*a i.
Proof.
move=> hw hs ha.
have [i hi] := finite_unit_weight_positive_entry hs.
have hsingle : w i*a i<=\sum_j w j*a j.
  rewrite (bigD1 i) //= lerDl.
  apply: sumr_ge0=> j hj; exact: mulr_ge0 (hw j) (ltW (ha j)).
exact: lt_le_trans (mulr_gt0 hi (ha i)) hsingle.
Qed.
