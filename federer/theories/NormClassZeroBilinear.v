(** Federer (1969), 3.1.11, p. 220:
    continuity under a bounded bilinear operation.
    This is the base of the higher-class induction
    for composition of linear maps and multiplication. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormClassOneUP
  NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_class_zero_bilinear]:
    continuous factors give a continuous bilinear
    product on their common open domain, supporting
    the induction in Federer 3.1.11, p. 220.
    The operation is abstract and its finite
    homogeneous bound is supplied as a proved law. *)
Theorem norm_class_zero_bilinear (R : realType)
    (X U V W : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNU : is_real_norm NU) (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (B : U->V->W) (hB : norm_bounded_bilinear NU NV NW B)
    (A : X->Prop) (f : X->U) (g : X->V) :
  norm_class_zero NX NU A f -> norm_class_zero NX NV A g ->
  norm_class_zero NX NW A (fun x=>B (f x) (g x)).
Proof.
move=> hf hg a ha; split; first exact: (hf a ha).1.
move=> e he.
have [hbil [C [hC hbound]]] := hB.
have hnf := real_seminorm_nonnegative hNU.1 (f a).
have hng := real_seminorm_nonnegative hNV.1 (g a).
pose K := C*(NU (f a)+1+NV (g a))+1.
have hsum : 0<=NU (f a)+1+NV (g a) by lra.
have hmul := mulr_ge0 hC hsum.
have hK : 0<K by rewrite /K; lra.
pose p := e/K.
have hp : 0<p by rewrite /p divr_gt0.
have [d1 [hd1 hf1]] := (hf a ha).2 1 ltr01.
have [df [hdf hfp]] := (hf a ha).2 p hp.
have [dg [hdg hgp]] := (hg a ha).2 p hp.
exists (Num.min d1 (Num.min df dg)).
split; first by rewrite !lt_min hd1 hdf hdg.
move=> h hah; rewrite !lt_min=>/andP [hh1 /andP [hhf hhg]].
have hvalue : NU (f (a+h))<=NU (f a)+1.
  have ht := real_seminorm_triangle hNU.1 (f a) (f (a+h)-f a).
  rewrite addrC subrK in ht.
  exact: le_trans ht (lerD (lexx _) (ltW (hf1 h hah hh1))).
have hfirst : NW (B (f (a+h)) (g (a+h)-g a))<=C*((NU (f a)+1)* p).
  apply: le_trans (hbound _ _) _; apply: (ler_wpM2l hC).
  exact (ler_pM (real_seminorm_nonnegative hNU.1 _)
    (real_seminorm_nonnegative hNV.1 _) hvalue (ltW (hgp h hah hhg))).
have hsecond : NW (B (f (a+h)-f a) (g a))<=C*(p*NV (g a)).
  apply: le_trans (hbound _ _) _; apply: (ler_wpM2l hC).
  exact (ler_wpM2r hng (ltW (hfp h hah hhf))).
have heq : B (f (a+h)) (g (a+h))-B (f a) (g a)=
    B (f (a+h)) (g (a+h)-g a)+B (f (a+h)-f a) (g a).
  by rewrite (bilBr hbil) (bilBl hbil) addrA subrK.
rewrite heq; apply: le_lt_trans (real_seminorm_triangle hNW.1 _ _) _.
apply: le_lt_trans (lerD hfirst hsecond) _.
have hcoef : p*K=e by rewrite /p divfK // gt_eqF.
rewrite /K in hcoef; nra.
Qed.
