(** Federer (1969), 3.1.24, pp. 238–239:
    continuity of the uniformly convergent differential series. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_uniform_limit_class_zero]: supporting
    the termwise differentiation induction in Federer 3.1.24,
    pp. 238–239. A uniform limit of continuous functions
    on the same open domain is continuous there. The
    proof uses three epsilon contributions and requires neither
    compactness nor completeness. *)
Lemma norm_uniform_limit_class_zero (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:X->Prop) (F:nat->X->Y) (f:X->Y) :
  (forall n,norm_class_zero NX NY A (F n)) ->
  (forall eps:R,0<eps -> exists n:nat,forall N,(n<=N)%N ->
    forall x,A x -> NY (F N x-f x)<eps) ->
  norm_class_zero NX NY A f.
Proof.
move=>hF hu a ha; split; first exact (hF 0%N a ha).1.
move=>eps he.
have he3:0<eps/3 by lra.
have [n hn]:=hu (eps/3) he3.
have [d [hd hb]]:=(hF n a ha).2 (eps/3) he3.
exists d; split; first exact hd.
move=>h hah hh.
have haerr:=hn n (leqnn n) a ha.
have hherr:=hn n (leqnn n) (a+h) hah.
rewrite (real_seminorm_subtract hNY.1) in hherr.
have hmid:=hb h hah hh.
have hid:f (a+h)-f a=
    (f (a+h)-F n (a+h))+((F n (a+h)-F n a)+(F n a-f a)).
  have hinner:(F n (a+h)-F n a)+(F n a-f a)= F n (a+h)-f a.
    by rewrite addrA subrK.
  by rewrite hinner addrA subrK.
rewrite hid.
have ht:=real_seminorm_triangle hNY.1 (f (a+h)-F n (a+h))
  ((F n (a+h)-F n a)+(F n a-f a)).
have ht2:=real_seminorm_triangle hNY.1 (F n (a+h)-F n a) (F n a-f a).
have h2:=le_lt_trans ht2 (ltrD hmid haerr).
have h3:=le_lt_trans ht (ltrD hherr h2).
have heq:eps/3+(eps/3+eps/3)= eps by lra.
by rewrite heq in h3.
Qed.
