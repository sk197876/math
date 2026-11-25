(** Federer (1969), 3.1.24, pp. 238–239:
    continuity of polynomial partial sums and their differential
    fields, using the finite-sum calculus of 3.1.11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP
  NormClassZeroArithmetic NormClassHigherDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_prefix_sum]: supporting the
    differentiated partial sums in Federer 3.1.24, pp. 238–239.
    Finite sums of continuous fields are continuous on their
    common open domain. The empty sum is included. *)
Lemma norm_class_zero_prefix_sum (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:X->Prop) (F:nat->X->Y) n :
  (forall x,A x -> norm_domain_interior NX A x) ->
  (forall m,(m<n)%N -> norm_class_zero NX NY A (F m)) ->
  norm_class_zero NX NY A (fun x=>\sum_(m<n) F m x).
Proof.
move=>hA; elim:n=>[|n ih] hF.
- have he:(fun x=>\sum_(m<0) F m x)= (fun _=>0).
    by apply: funext=>x; rewrite big_ord0.
  rewrite he; exact (norm_class_zero_constant hNY 0 hA).
- have hp:norm_class_zero NX NY A (fun x=>\sum_(m<n) F m x).
    apply: ih=>m hm; exact (hF m (ltn_trans hm (ltnSn n))).
  have hs:=norm_class_zero_add hNY hp (hF n (ltnSn n)).
  apply: (norm_class_zero_domain_agreement _ hs)=>x _.
  by rewrite big_ord_recr.
Qed.
