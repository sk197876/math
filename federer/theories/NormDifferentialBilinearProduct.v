(** Federer (1969), 3.1.11, pp. 220–222:
    the first differential of a continuous bilinear
    operation on two differentiable functions. This
    supports higher composition and Leibniz rules. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  NormDifferentialLocal NormBoundedBilinearUP NormBilinearDifferentialAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_bilinear_product]:
    first-order product rule for the bilinear
    operations used in Federer 3.1.11,
    p. 220. The remainder estimate is
    proved in arbitrary normed spaces; neither
    finite dimension nor completeness is required. *)
Theorem norm_differential_bilinear_product (R : realType)
    (X U V W : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNX : is_real_norm NX) (hNU : is_real_norm NU)
    (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (B : U->V->W) (hB : bilinear B) (C : R)
    (A : X->Prop) (f : X->U) (g : X->V) a
    (L : Hom X U) (M : Hom X V) :
  0<=C -> (forall u v, NW (B u v)<=C*(NU u*NV v)) ->
  has_norm_differential NX NU A f a L ->
  has_norm_differential NX NV A g a M ->
  has_norm_differential NX NW A (fun x=>B (f x) (g x)) a
    (norm_bilinear_product_linear_term hB (f a) (g a) L M).
Proof.
move=> hC hbound hf hg; constructor.
- exact: norm_differential_interior hf.
- exact (@norm_bilinear_product_linear_bound R X U V W NX NU NV NW
    hNU hNV hNW B hB C (f a) (g a) L M hC hbound
    (norm_differential_bounded hf) (norm_differential_bounded hg)).
- move=> e he.
  have [F [hF [r [hr hinc]]]] := norm_differential_increment_bound hNU hf.
  have [G [hG hM]] := norm_differential_bounded hg.
  have hnf := real_seminorm_nonnegative hNU.1 (f a).
  have hng := real_seminorm_nonnegative hNV.1 (g a).
  have hFG := mulr_ge0 (ltW hF) hG.
  pose K := C*(NU (f a)+F+NV (g a)+F*G)+1.
  have hsum : 0<=NU (f a)+F+NV (g a)+F*G by lra.
  have hCK := mulr_ge0 hC hsum.
  have hK : 0<K by rewrite /K; lra.
  pose p := e/K.
  have hp : 0<p by rewrite /p divr_gt0.
  have [df [hdf hrf]] := norm_differential_remainder hf hp.
  have [dg [hdg hrg]] := norm_differential_remainder hg hp.
  exists (Num.min 1 (Num.min p (Num.min r (Num.min df dg)))).
  split; first by rewrite !lt_min ltr01 hp hr hdf hdg.
  move=> h ha hh.
  move: hh; rewrite !lt_min=>/andP [hh1 /andP [hhp /andP [hhr /andP [hhf hhg]]]].
  have hn := real_seminorm_nonnegative hNX.1 h.
  have hincf := hinc h ha hhr.
  have hvalue : NU (f (a+h))<=NU (f a)+F.
    have htri : NU (f (a+h))<=NU (f a)+NU (f (a+h)-f a).
      have ht := real_seminorm_triangle hNU.1 (f a) (f (a+h)-f a).
      by rewrite addrC subrK in ht.
    apply: le_trans htri _; apply: lerD (lexx _) _.
    apply: le_trans hincf _.
    have ht := ler_wpM2l (ltW hF) (ltW hh1); by rewrite mulr1 in ht.
  have hfirst : NW (B (f (a+h)) (g (a+h)-g a-M h))<=
      C*((NU (f a)+F)*(p*NX h)).
    apply: le_trans (hbound _ _) _; apply: (ler_wpM2l hC).
    exact (ler_pM (real_seminorm_nonnegative hNU.1 _)
      (real_seminorm_nonnegative hNV.1 _) hvalue (hrg h ha hhg)).
  have hsecond : NW (B (f (a+h)-f a-L h) (g a))<=
      C*((p*NX h)*NV (g a)).
    apply: le_trans (hbound _ _) _; apply: (ler_wpM2l hC).
    exact (ler_wpM2r hng (hrf h ha hhf)).
  have hthird : NW (B (f (a+h)-f a) (M h))<=C*F*G* p*NX h.
    apply: le_trans (hbound _ _) _.
    have hprod := ler_pM (real_seminorm_nonnegative hNU.1 _)
      (real_seminorm_nonnegative hNV.1 _) hincf (hM h).
    apply: le_trans (ler_wpM2l hC hprod) _.
    have hs := ler_wpM2r hn (ltW hhp).
    have hCScale := ler_wpM2l (mulr_ge0 hC hFG) hs.
    nra.
  change (NW (B (f (a+h)) (g (a+h))-B (f a) (g a)-
    (B (L h) (g a)+B (f a) (M h)))<=e*NX h).
  rewrite (norm_bilinear_product_remainder hB).
  apply: le_trans (real_seminorm_triangle hNW.1 _ _) _.
  apply: le_trans (lerD (le_trans (real_seminorm_triangle hNW.1 _ _)
    (lerD hfirst hsecond)) hthird) _.
  have hcoef : p*K=e by rewrite /p divfK // gt_eqF.
  have hpn : 0<=p*NX h := mulr_ge0 (ltW hp) hn.
  rewrite /K in hcoef; nra.
Qed.
