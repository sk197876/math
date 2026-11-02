(** Federer (1969), 3.1.4, pp. 215–216: coordinate exceptional
    increments and the remainder bound outside their union. The weak
    variation threshold follows the erratum, book p. 214 line 24. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm EuclideanCoordinateStaircase ApproximateCoordinateTelescoping.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section ExceptionalIncrements.
Variable R : realType.
Variable n : nat.
Variable f : R_n R n -> R.
Variable g : 'I_n -> R_n R n -> R.
Variable a : R_n R n.
Variable e : R.

(** Source for [coordinate_staircase_exception]: the two sources
    of error controlled by S_i in Federer 3.1.4, p. 215. This
    auxiliary set omits the radius restriction and the larger
    leave-B alternative, both supplied in the measure estimate. *)
Definition coordinate_staircase_exception (i : 'I_n) : set (R_n R n) :=
  [set h | let x:=a+coordinate_prefix h i in
    e*`|h i|<`|f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i x| \/
    e<=`|g i x-g i a|].

(** Source for [coordinate_staircase_remainder_exception_cover]:
    the last display on p. 215 and the final display on p. 216
    of Federer 3.1.4. Outside all coordinate exceptions, the
    telescoped remainder is bounded by 2 n e times the increment norm. *)
Theorem coordinate_staircase_remainder_exception_cover :
  0<=e ->
  [set h | (2*n%:R*e)*inner_norm (@euclidean_inner_productP R n) h <
    `|f (a+h)-f a-\sum_(i<n) h i*g i a|] `<=`
    \bigcup_i coordinate_staircase_exception i.
Proof.
move=> he h hh; apply: contrapT=> hn.
have hnot i : ~coordinate_staircase_exception i h.
  move=> hi; apply: hn; by exists i.
have hb := @coordinate_staircase_approximation_bound R n f g a h e he.
have hs (i : 'I_n) : let x:=a+coordinate_prefix h i in
    `|f (x+h i*:(@coordinate_basis R n i))-f x-h i*g i x|<=e*`|h i|.
  rewrite /= leNgt; apply/negP=> hx; apply: (hnot i); by left.
have hv (i : 'I_n) : `|g i (a+coordinate_prefix h i)-g i a|<=e.
  apply: ltW; rewrite ltNge; apply/negP=> hx; apply: (hnot i); by right.
have := le_lt_trans (hb hs hv) hh; by rewrite ltxx.
Qed.
End ExceptionalIncrements.
