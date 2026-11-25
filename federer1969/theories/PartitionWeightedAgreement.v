(** Federer (1969), 3.1.22, p. 236: a weighted
    partition sum agrees with the prescribed values on S. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import FiniteFamilySumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope fset_scope.

(** Source for [partition_weighted_agreement]: supporting the
    partition-of-unity extension in Federer 3.1.22, p. 236.
    At a point of S every summand is the corresponding
    partition weight times f(x); the finite evaluation laws
    and sum-one identity therefore give the exact value f(x). *)
Lemma partition_weighted_agreement (R:realType) (X:Type) (Y:lmodType R) (J:choiceType)
    (U S:X->Prop) (I:J->Prop) (u:J->X->R^o) (w:J->X->Y) (f g:X->Y) :
  finite_active_family_on U I u ->
  is_finite_family_sum_on U I u (fun _=>1) ->
  is_finite_family_sum_on U I w g ->
  (forall j,I j -> forall x,S x -> U x -> w j x=u j x*:f x) ->
  forall x,S x -> U x -> g x=f x.
Proof.
move=>hfin hOne hSum hweight x hxS hxU.
have [F [hFI hF]]:=hfin x hxU.
have hFw j (hj:I j) (hn:j \notin F):w j x=0.
  by rewrite (hweight j hj x hxS hxU) (hF j hj hn) scale0r.
rewrite (hSum x hxU F hFI hFw).
have heq:(\sum_(j <- F) w j x)=\sum_(j <- F) u j x*:f x.
  apply: eq_big_seq=>j hj; exact (hweight j (hFI j hj) x hxS hxU).
rewrite heq -scaler_suml -(hOne x hxU F hFI hF) scale1r.
by [].
Qed.
