(** Federer (1969), 3.1.11, pp. 220–222:
    algebraic part of the first bilinear product rule.
    It supports the induction for composition and
    the higher Leibniz formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  NormBoundedBilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_bilinear_product_remainder]:
    the exact three-term remainder for the bilinear
    operations in Federer 3.1.11, p. 220.
    This supporting identity uses only bilinearity. *)
Lemma norm_bilinear_product_remainder (R : realType)
    (U V W : lmodType R) (B : U->V->W) (hB : bilinear B)
    (u c l : U) (v w m : V) :
  B u v-B c w-(B l w+B c m)=
    B u (v-w-m)+B (u-c-l) w+B (u-c) m.
Proof.
have h1 : B u v-B c w=B u (v-w)+B (u-c) w.
  by rewrite (bilBr hB) (bilBl hB) addrA subrK.
have h2 : B u (v-w)-B c m=B u (v-w-m)+B (u-c) m.
  by rewrite (bilBr hB u (v-w) m) (bilBl hB) addrA subrK.
rewrite h1 opprD [(- (B l w))+(- (B c m))]addrC addrACA h2 -(bilBl hB).
by rewrite addrAC.
Qed.

(** Source for [norm_bilinear_product_linear]:
    the first-order term B(Lh,v)+B(u,Mh)
    is linear in h, supporting the product
    calculus of Federer 3.1.11, p. 220. *)
Lemma norm_bilinear_product_linear (R : realType)
    (X U V W : lmodType R) (B : U->V->W) (hB : bilinear B)
    (u : U) (v : V) (L : Hom X U) (M : Hom X V) :
  linear (fun h=>B (L h) v+B u (M h)).
Proof.
move=> c x y.
rewrite (hom_linear L) (hom_linear M) (hB.1 v) (hB.2 u).
by rewrite scalerDr addrACA.
Qed.

(** Source for [norm_bilinear_product_linear_term]:
    the linear map in the first bilinear product
    rule, supporting Federer 3.1.11, p. 220.
    Its definition is solely the stated evaluation formula. *)
Definition norm_bilinear_product_linear_term (R : realType)
    (X U V W : lmodType R) (B : U->V->W) (hB : bilinear B)
    (u : U) (v : V) (L : Hom X U) (M : Hom X V) : Hom X W :=
  @HomMap R X W (fun h=>B (L h) v+B u (M h))
    (introT (asboolP _) (norm_bilinear_product_linear hB u v L M)).

(** Source for [norm_bilinear_product_linear_bound]:
    continuity of the candidate product differential,
    supporting Federer 3.1.11, p. 220.
    Bounds of the two factors and the bilinear map
    yield a finite linear bound. *)
Lemma norm_bilinear_product_linear_bound (R : realType)
    (X U V W : lmodType R)
    (NX : X->R) (NU : U->R) (NV : V->R) (NW : W->R)
    (hNU : is_real_norm NU) (hNV : is_real_norm NV) (hNW : is_real_norm NW)
    (B : U->V->W) (hB : bilinear B) (C : R)
    (u : U) (v : V) (L : Hom X U) (M : Hom X V) :
  0<=C -> (forall x y, NW (B x y)<=C*(NU x*NV y)) ->
  norm_bounded_linear NX NU L -> norm_bounded_linear NX NV M ->
  norm_bounded_linear NX NW (norm_bilinear_product_linear_term hB u v L M).
Proof.
move=> hC hbound [a [ha hL]] [b [hb hM]].
have hu := real_seminorm_nonnegative hNU.1 u.
have hv := real_seminorm_nonnegative hNV.1 v.
exists (C*(a*NV v+NU u*b)); split.
- exact: mulr_ge0 hC (addr_ge0 (mulr_ge0 ha hv) (mulr_ge0 hu hb)).
- move=> h; change (is_true (NW (B (L h) v+B u (M h))<=(C*(a*NV v+NU u*b))*NX h)).
  apply: le_trans (real_seminorm_triangle hNW.1 _ _) _.
  have hl := le_trans (hbound (L h) v)
    (ler_wpM2l hC (ler_wpM2r hv (hL h))).
  have hr := le_trans (hbound u (M h))
    (ler_wpM2l hC (ler_wpM2l hu (hM h))).
  have he : C*((a*NX h)*NV v)+C*(NU u*(b*NX h))=
      (C*(a*NV v+NU u*b))*NX h.
    by ring.
  have hh := lerD hl hr; by rewrite he in hh.
Qed.
