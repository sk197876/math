(** Federer (1969), 3.1.11, p. 220:
    the first differential field of a bilinear
    product, represented in the abstract one-linear
    space. Its two terms use the proved bilinear lifts. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearOne NormHigherDifferentialUP
  NormHigherDifferentialFirst NormBoundedBilinearUP
  NormBilinearDifferentialAlgebra NormDifferentialBilinearProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_first_bilinear_field]:
    D B(f,g)=B(Df,g)+B(f,Dg),
    used in the higher-class induction of Federer
    3.1.11, p. 220. Both input
    fields are proved first differentials, and the
    output field is identified through its evaluation laws. *)
Theorem norm_higher_first_bilinear_field (R : realType)
    (X U V W : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNX : is_real_norm NX) (hNU : is_real_norm NU)
    (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (P Q S : nat->lmodType R)
    (ep : forall k, {ffun 'I_k->X}->Hom (P k) U) (PN : forall k, P k->R)
    (eq : forall k, {ffun 'I_k->X}->Hom (Q k) V) (QN : forall k, Q k->R)
    (es : forall k, {ffun 'I_k->X}->Hom (S k) W) (SN : forall k, S k->R)
    (hP : forall k, is_continuous_multilinear_space NX NU (@ep k) (@PN k))
    (hQ : forall k, is_continuous_multilinear_space NX NV (@eq k) (@QN k))
    (hS : forall k, is_continuous_multilinear_space NX NW (@es k) (@SN k))
    (B : U->V->W) (CF : P 1%N->V->S 1%N) (CG : U->Q 1%N->S 1%N)
    (A : X->Prop) (f : X->U) (g : X->V)
    (F : X->P 1%N) (G : X->Q 1%N) :
  norm_bounded_bilinear NU NV NW B ->
  (forall p v u, @es 1%N u (CF p v)=B (@ep 1%N u p) v) ->
  (forall u q v, @es 1%N v (CG u q)=B u (@eq 1%N v q)) ->
  (forall x, A x -> has_norm_higher_differential NX ep PN A f 1%N x (F x)) ->
  (forall x, A x -> has_norm_higher_differential NX eq QN A g 1%N x (G x)) ->
  forall x, A x -> has_norm_higher_differential NX es SN A
    (fun t=>B (f t) (g t)) 1%N x (CF (F x) (g x)+CG (f x) (G x)).
Proof.
move=> [hbil [b [hb hbound]]] hCF hCG hF hG a ha.
pose LF := @continuous_multilinear_one_operator R X U (P 1%N) NX NU
  (@ep 1%N) (@PN 1%N) (@hP 1%N) (F a).
pose LG := @continuous_multilinear_one_operator R X V (Q 1%N) NX NV
  (@eq 1%N) (@QN 1%N) (@hQ 1%N) (G a).
have hf : has_norm_differential NX NU A f a LF.
  exact ((@norm_higher_differential_first R X U NX NU hNX hNU
    P ep PN hP A f a (F a)).1 (hF a ha)).
have hg : has_norm_differential NX NV A g a LG.
  exact ((@norm_higher_differential_first R X V NX NV hNX hNV
    Q eq QN hQ A g a (G a)).1 (hG a ha)).
have hd := @norm_differential_bilinear_product R X U V W NX NU NV NW
  hNX hNU hNV hNW B hbil b A f g a LF LG hb hbound hf hg.
apply: (@norm_higher_differential_first R X W NX NW hNX hNW S es SN hS
  A (fun t=>B (f t) (g t)) a (CF (F a) (g a)+CG (f a) (G a))).2.
have he : @continuous_multilinear_one_operator R X W (S 1%N) NX NW
    (@es 1%N) (@SN 1%N) (@hS 1%N) (CF (F a) (g a)+CG (f a) (G a))=
    norm_bilinear_product_linear_term hbil (f a) (g a) LF LG.
  apply: hom_ext=>v.
  change (@es 1%N [ffun _ : 'I_1=>v] (CF (F a) (g a)+CG (f a) (G a))=
    B (LF v) (g a)+B (f a) (LG v)).
  by rewrite linearD /= hCF hCG.
by rewrite he.
Qed.
