(** Federer (1969), 3.2.7, p. 246: elementary
    positivity laws for the prescribed cutoff weight. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import ReciprocalRootWeightUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reciprocal_root_weight_nonnegative]:
    the weight in the third example of
    Federer 3.2.7, p. 246, is nonnegative,
    including its specified zero value at zero. *)
Lemma reciprocal_root_weight_nonnegative (R:realType) (g:R->R):
  is_reciprocal_root_weight g -> forall y,0<=g y.
Proof.
move=>hg y; case:(pselect (0<`|y| /\ `|y|<=1))=>[[hy0 hy1]|hOff].
- rewrite (reciprocal_root_weight_on hg hy0 hy1) invr_ge0 sqrtr_ge0; by [].
- by rewrite (reciprocal_root_weight_off hg hOff).
Qed.

(** Source for [reciprocal_root_weight_positive_value]:
    on positive levels y<=1 the weight is
    precisely 1/sqrt(y), used in the divergence
    argument of Federer 3.2.7, p. 246. *)
Lemma reciprocal_root_weight_positive_value (R:realType) (g:R->R):
  is_reciprocal_root_weight g -> forall y,0<y -> y<=1 -> g y=(Num.sqrt y)^-1.
Proof.
move=>hg y hy hy1.
have hNorm:`|y|=y:=ger0_norm (ltW hy).
have h0:0<`|y| by rewrite hNorm.
have h1:`|y|<=1 by rewrite hNorm.
by rewrite (@reciprocal_root_weight_on R g hg y h0 h1) hNorm.
Qed.
