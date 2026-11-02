(** Federer (1969), 3.1.11, p. 223,
    and 3.1.13, p. 225:
    scalar reciprocals and quotients preserve higher
    regularity wherever the denominator is nonzero. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom AlgebraUP ScalarCoefficients RealNormUP AlgebraInverseUP
  ContinuousMultilinearUP NormBoundedBilinearUP NormClassHigherUP
  NormClassHigherInverseField NormClassHigherBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ScalarQuotient.
Variable R : realType.
Variable X : lmodType R.
Variable NX : X->R.
Hypothesis hNX : is_real_norm NX.
Variable Z : nat->lmodType R.
Variable ez : forall k, {ffun 'I_k->X}->Hom (Z k) R^o.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX
  (fun t : R^o=>`|t|) (@ez k) (@ZN k).
Variable U : X->Prop.

(** Source for [norm_class_higher_scalar_reciprocal]:
    regularity of 1/f in Federer 3.1.11,
    p. 223, prior to its explicit
    differential formula. The same assertion is
    used to normalize the partition in 3.1.13,
    p. 225. The denominator is required
    to be nonzero only on U. *)
Theorem norm_class_higher_scalar_reciprocal (f : X->R) k :
  (forall x, U x -> f x!=0) ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U f k ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U (fun x=>(f x)^-1) k.
Proof.
move=> hn hf.
have hm (s t : scalar_algebra R) :
    `|alg_mul (scalar_algebra R) s t|<=`|s|*`|t|.
  by change (`|s*t|<=`|s|*`|t|); rewrite normrM.
have hi x (hx : U x) :
    @is_two_sided_algebra_inverse R (scalar_algebra R) (f x) ((f x)^-1).
  split; [exact: (mulfV (hn x hx))|exact: (mulVf (hn x hx))].
exact: (@norm_class_higher_inverse_field R X (scalar_algebra R) NX
  (fun t : R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
  hm Z ez ZN hZ U f (fun x=>(f x)^-1) hi k hf).
Qed.

(** Source for [norm_class_higher_scalar_product]:
    scalar multiplication of two class-k functions
    is the bilinear case of Federer 3.1.11,
    p. 220, used for the quotient
    in 3.1.13, p. 225. *)
Theorem norm_class_higher_scalar_product (f g : X->R) k :
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U f k ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U g k ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U (fun x=>f x*g x) k.
Proof.
move=> hf hg.
have hb : norm_bounded_bilinear (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (fun s t : R^o=>s*t).
  split; first exact: scalar_bilinear.
  exists 1; split; first exact: ler01; by move=>s t; rewrite mul1r normrM.
exact: (@norm_class_higher_bilinear R X NX hNX k R^o R^o R^o
  (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
  (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
  (@scalar_absolute_value_norm R) Z Z Z ez ZN ez ZN ez ZN hZ hZ hZ
  U f g (fun s t=>s*t) hb hf hg).
Qed.

(** Source for [norm_class_higher_scalar_quotient]:
    the normalized partition functions v_s=u_s/u
    retain class k, Federer 3.1.13, p. 225,
    as follows from the reciprocal calculus in
    3.1.11, p. 223. *)
Corollary norm_class_higher_scalar_quotient (f g : X->R) k :
  (forall x, U x -> g x!=0) ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U f k ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U g k ->
  norm_class_higher NX (fun t : R^o=>`|t|) ez ZN U (fun x=>f x/g x) k.
Proof.
move=> hn hf hg; exact: norm_class_higher_scalar_product hf
  (norm_class_higher_scalar_reciprocal hn hg).
Qed.
End ScalarQuotient.
