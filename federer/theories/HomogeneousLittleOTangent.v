(** Federer (1969), 3.4.11, p. 338:
    a continuous homogeneous polynomial whose values on
    the original set are negligible in its own
    degree vanishes on the original tangent cone.
    Reuse the actual two-radius tangent laws and norm
    estimates, without assuming an analytic tangent cone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals lra.
From Federer Require Import RealNormUP NormClassOneUP TangentConeUP TangentConeBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [homogeneous_little_o_tangent_zero]: the
    implication from the first Taylor remainder display
    to P(v)=0 on Tan(S,0), 3.4.11,
    p. 338. The degree-zero and zero-vector
    cases remain; no division by a source norm occurs. *)
Theorem homogeneous_little_o_tangent_zero (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (S:set X) (P:X->R) k:
  norm_class_zero NX (fun t:R^o=>`|t|) setT P ->
  (forall (t:R) x,0<t ->P (t*:x)=t^+k*P x) ->
  (forall e:R,0<e ->exists r:R,0<r /\
    forall x,S x ->NX x<r ->`|P x|<=e*(NX x)^+k) ->
  forall v,norm_tangent_cone NX S 0 v ->P v=0.
Proof.
move=>hContinuous hHomogeneous hSmall v hTangent.
case:(eqVneq (P v) 0)=>[h|hNonzero];first exact:h.
exfalso.
pose E:=`|P v|.
have hE:0<E by rewrite /E normr_gt0.
have hNv:=real_seminorm_nonnegative hNX.1 v.
pose C:=(NX v+1)^+k.
have hBase:0<NX v+1 by lra.
have hC:0<C:=exprn_gt0 _ hBase.
pose e:=E/(4*C+4).
have hDen:0<4*C+4 by lra.
have he:0<e by rewrite /e divr_gt0.
have hProduct:e*(4*C+4)=E by rewrite /e divfK ?gt_eqF.
have hE4:0<E/4 by rewrite divr_gt0 // ltr0n.
have [d [hd hContinuity]]:=(hContinuous v Logic.I).2 (E/4) hE4.
have [r [hr hRemainder]]:=hSmall e he.
have hTol:0<Num.min d 1 by rewrite lt_min hd ltr01.
have [x [t [hx [ht [hX hNear]]]]]:=
  (@norm_tangent_two_radii R X NX S 0 v).1 hTangent r (Num.min d 1) hr hTol.
rewrite subr0 in hX hNear.
have hD:NX (t*:x-v)<d:=lt_le_trans hNear (real_minimum_left_bound d 1).
have hOne:NX (t*:x-v)<1:=lt_le_trans hNear (real_minimum_right_bound d 1).
have hCont:=hContinuity (t*:x-v) Logic.I hD.
have hShift:v+(t*:x-v)=t*:x by rewrite addrC subrK.
rewrite hShift in hCont.
have hNorm:NX (t*:x)<NX v+1.
  have hTriangle:=real_seminorm_triangle hNX.1 (t*:x-v) v.
  rewrite subrK in hTriangle;lra.
have hPower:(NX (t*:x))^+k<=C.
  apply:lerXn2r.
  - exact:real_seminorm_nonnegative hNX.1 (t*:x).
  - exact:ltW hBase.
  - exact:ltW hNorm.
have hRaw:=hRemainder x hx hX.
have hScaled:`|P (t*:x)|<=e*(NX (t*:x))^+k.
  rewrite hHomogeneous // normrM (ger0_norm (ltW (exprn_gt0 k ht)))
    (real_seminorm_scale hNX.1) (ger0_norm (ltW ht)) exprMn.
  have h:=ler_wpM2l (ltW (exprn_gt0 k ht)) hRaw.
  nra.
have hBound:`|P (t*:x)|<=e*C.
  exact:le_trans hScaled (ler_wpM2l (ltW he) hPower).
have hTriangle:=ler_normD (P v-P (t*:x)) (P (t*:x)).
rewrite subrK distrC in hTriangle.
change (is_true (`|P (t*:x)-P v|<E/4)) in hCont.
change (is_true (E<=`|P (t*:x)-P v|+`|P (t*:x)|)) in hTriangle.
nra.
Qed.
