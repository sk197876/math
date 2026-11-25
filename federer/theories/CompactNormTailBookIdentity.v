(** Federer (1969), 4.1.5, p. 350: the
    continuous positive-tail cutoff has exactly the
    printed identity with the original plateau majorant
    g, and its removed tail has norm at most eta g.
    This identifies the independent cutoff with the
    book's original decomposition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric CompactSupportFunctionUP CompactNormTailUP CompactNormTailFieldLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CompactNormTailBookIdentity.
Variable R:realType.
Variable X:topologicalType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable w:X->Y.
Variable eta:R.
Hypothesis hEta:0<eta.
Variable h:X->R.
Hypothesis hH:is_compact_norm_tail_cutoff NY w eta h.
Variable g:X->R.
Hypothesis hG:forall x,0<=g x.
Hypothesis hOne:forall x,@real_function_support R X (fun x=>NY (w x)) x ->g x= 1.

(** Source for [compact_norm_tail_book_product]: the original
    identity h||w||=(||w||-eta g)+ of Federer 4.1.5,
    p. 350, including every zero of the original field. *)
Theorem compact_norm_tail_book_product x:
  h x*NY (w x)=Num.max (NY (w x)-eta*g x) 0.
Proof.
case:(eqVneq (NY (w x)) 0)=>[hx|hx].
- have hNonnegative:=mulr_ge0 (ltW hEta) (hG x).
  have hNeg:-(eta*g x)<=0 by lra.
  by rewrite hx mulr0 sub0r (max_r hNeg).
- have hAt:g x= 1.
    apply:hOne; apply:subset_closure; exact/eqP.
  by rewrite hAt mulr1 (compact_norm_tail_product hH x).
Qed.

(** Source for [compact_norm_tail_book_remainder]: the
    original removed-tail bound by eta g in Federer
    4.1.5, p. 350, before applying the actual
    positive convolution. *)
Theorem compact_norm_tail_book_remainder x:
  NY (w x-h x*:w x)<=eta*g x.
Proof.
case:(eqVneq (NY (w x)) 0)=>[hx|hx].
- by rewrite (hNY.2 _ hx) scaler0 subrr (real_seminorm_zero hNY.1);
    exact:mulr_ge0 (ltW hEta) (hG x).
- have hAt:g x= 1.
    apply:hOne; apply:subset_closure; exact/eqP.
  rewrite hAt mulr1; exact:(@compact_norm_tail_remainder_bound R X Y NY hNY w eta h hH hEta x).
Qed.
End CompactNormTailBookIdentity.
