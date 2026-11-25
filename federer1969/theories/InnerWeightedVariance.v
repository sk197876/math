(** Federer (1969), 2.10.43, printed p. 201: expand the double weighted
    squared-distance sum in the finite-ball step of Kirszbraun's theorem.
    These intrinsic identities hold for any finite real inner-product family
    with weights of total one; nonnegativity is needed only in later
    inequalities. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import InnerProductUP InnerNorm Bilinear BilinearDoubleExpansion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_difference_norm_square]: supporting
    identity twice x dot y = |x| squared plus
    |y| squared minus |x-y| squared in 2.10.43,
    p. 201, written with the difference norm on the left. *)
Lemma inner_difference_norm_square (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (x y : V) :
  inner_norm hB (x-y)^+2=inner_norm hB x^+2+inner_norm hB y^+2-2*B x y.
Proof.
rewrite !inner_norm_sqr (bilBl (inner_bilinear hB)) !(bilBr (inner_bilinear hB))
  (inner_symmetric hB y x); ring.
Qed.

(** Source for [inner_weighted_square_expansion]: direct
    double bilinear expansion in 2.10.43, p. 201.
    The squared norm of the weighted sum equals
    the double sum of weighted inner products. *)
Lemma inner_weighted_square_expansion (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (I : finType)
    (v : I -> V) (w : I -> R) :
  inner_norm hB (\sum_i w i*:v i)^+2=
    \sum_i \sum_j (w i*w j)*B (v i) (v j).
Proof.
rewrite inner_norm_sqr (@bilinear_double_expansion R V V R^o B (inner_bilinear hB) I I v v w w).
by [].
Qed.

(** Source for [inner_weighted_variance_identity]: direct weighted variance
    expansion used twice in 2.10.43, p. 201 For weights of total one, the
    double weighted squared-distance sum is twice the weighted squared norm
    sum minus twice the squared norm of the barycentre. *)
Theorem inner_weighted_variance_identity (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (I : finType)
    (v : I -> V) (w : I -> R) :
  (\sum_i w i= 1) ->
  (\sum_i \sum_j (w i*w j)*inner_norm hB (v i-v j)^+2)=
    2*(\sum_i w i*inner_norm hB (v i)^+2)-2*inner_norm hB (\sum_i w i*:v i)^+2.
Proof.
move=> hw.
have hfirst : (\sum_i \sum_j (w i*w j)*inner_norm hB (v i)^+2)=
    \sum_i w i*inner_norm hB (v i)^+2.
  apply: eq_bigr=> i _.
  transitivity ((w i*inner_norm hB (v i)^+2)*(\sum_j w j)); last by rewrite hw mulr1.
  rewrite mulr_sumr; apply: eq_bigr=> j _; ring.
have hsecond : (\sum_i \sum_j (w i*w j)*inner_norm hB (v j)^+2)=
    \sum_i w i*inner_norm hB (v i)^+2.
  transitivity ((\sum_i w i)*(\sum_j w j*inner_norm hB (v j)^+2)); last by rewrite hw mul1r.
  rewrite mulr_suml; apply: eq_bigr=> i _.
  rewrite mulr_sumr; apply: eq_bigr=> j _; ring.
have htotal : (\sum_i \sum_j (w i*w j)*inner_norm hB (v i-v j)^+2)=
    (\sum_i \sum_j (w i*w j)*inner_norm hB (v i)^+2)+
    (\sum_i \sum_j (w i*w j)*inner_norm hB (v j)^+2)-
    2*(\sum_i \sum_j (w i*w j)*B (v i) (v j)).
  rewrite mulr_sumr -big_split -sumrB; apply: eq_bigr=> i _.
  rewrite mulr_sumr -big_split -sumrB; apply: eq_bigr=> j _.
  rewrite inner_difference_norm_square.
  change ((w i*w j)*(inner_norm hB (v i)^+2+inner_norm hB (v j)^+2-2*B (v i) (v j))=
    (w i*w j)*inner_norm hB (v i)^+2+(w i*w j)*inner_norm hB (v j)^+2-
    2*((w i*w j)*B (v i) (v j))).
  ring.
rewrite htotal hfirst hsecond -inner_weighted_square_expansion.
ring.
Qed.
