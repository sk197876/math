(** Federer (1969), 3.2.3, p. 244: one graph
    singular length is epsilon and the remaining m-1
    lengths are at most Lip(f)+epsilon. This finite
    product estimate makes that step explicit. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [single_factor_product_bound]: the
    estimate J_m g<=epsilon (Lip(f)+epsilon)^(m-1)
    in Federer 3.2.3, p. 244, at the scalar
    product level. A distinguished factor is required,
    so no predecessor convention is used on an empty family. *)
Lemma single_factor_product_bound (R:realType) (I:finType)
    (f:I->R) (i0:I) e C:
  0<=e -> 0<=C -> (forall i,0<=f i) -> f i0<=e ->
  (forall i,i!=i0 -> f i<=C) ->
  \prod_i f i<=e*C^+(#|I|.-1).
Proof.
move=>he hC hf h0 hOther.
rewrite (bigD1 i0) //=.
have hCard:#|[pred i:I|i!=i0]|=#|I|.-1 by rewrite cardC1.
have hRest:(\prod_(i:I|i!=i0) f i)<=C^+(#|I|.-1).
  rewrite -hCard -prodr_const.
  apply:ler_prod=>i hi; apply/andP; split; [exact:hf|exact:hOther].
have hRest0:0<=\prod_(i:I|i!=i0) f i by apply:prodr_ge0=>i _; exact:hf.
apply:le_trans (ler_wpM2r hRest0 h0) _.
exact (ler_wpM2l he hRest).
Qed.
