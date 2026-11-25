(** Federer (1969), 3.1.24, p. 240: the positive
    discriminant in the scalar quadratic inverse describes an
    open actual domain. This follows from continuity. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import RealNormUP NormDifferentialUP NormClassOneUP NormClassZeroTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_positive_locus_interior]:
    supporting the square-root domain of the scalar inverse in
    Federer 3.1.24, p. 240. The inverse image of
    the positive reals under a continuous scalar function on
    an open normed domain is open, in the intrinsic ball form. *)
Lemma norm_class_zero_positive_locus_interior (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:X->Prop) (f:X->R) :
  norm_class_zero NX (fun t:R^o=>`|t|) A f ->
  forall a,A a -> 0<f a -> norm_domain_interior NX (fun x=>A x /\ 0<f x) a.
Proof.
move=>hf a ha hp.
have [r [hr hb]]:=@norm_class_zero_local_control R X R^o NX (fun t=>`|t|) hNX A f a (f a) hf ha hp.
exists r; split; first exact hr.
move=>v hv.
have hsmall:NX ((a+v)-a)<r by rewrite addrAC subrr add0r.
have [hav hrem]:=hb (a+v) hsmall.
split; first exact hav.
rewrite ltr_norml in hrem; have hh:=(andP hrem).1; lra.
Qed.
