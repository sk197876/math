(** Federer (1969), 3.1.11, p. 222:
    multiplication by a locally bounded factor
    preserves a Taylor remainder's order.
    This supplies the product-of-jets argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra ring.
From Federer Require Import TensorUP Bilinear RealNormUP NormLittleOPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_little_o_bilinear_bounded_right]:
    a negligible remainder times a bounded
    factor is negligible, supporting the first
    displayed limit on Federer 3.1.11,
    p. 222. Neither normed space
    is assumed complete. *)
Lemma norm_little_o_bilinear_bounded_right (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (B : X->Y->Z) C (f : R->X) (g : R->Y) k M r :
  0<=C -> (forall x y, NZ (B x y)<=C*NX x*NY y) ->
  0<=M -> 0<r -> (forall t, `|t|<r -> NY (g t)<=M) ->
  norm_little_o_power NX f k ->
  norm_little_o_power NZ (fun t=>B (f t) (g t)) k.
Proof.
move=>hC hB hM hr hg hf e he.
pose K := C*M+1.
have hCM := mulr_ge0 hC hM.
have hK : 0<K by rewrite /K; lra.
have heK : 0<e/K by rewrite divr_gt0.
have [d [hd hdf]] := hf (e/K) heK.
exists (Num.min r d); split; first by rewrite lt_min hr hd.
move=>t /andP [ht0 ht].
have /andP [htr htd] : (`|t|<r)&&(`|t|<d) by rewrite -lt_min.
have hnf := real_seminorm_nonnegative hNX.1 (f t).
have hp := exprn_ge0 k (normr_ge0 t).
have h0 := hB (f t) (g t).
have h1 := ler_wpM2l (mulr_ge0 hC hnf) (hg t htr).
have h2 := ler_wpM2l hCM (hdf t (introT andP (conj ht0 htd))).
have hcmK : C*M<=K by rewrite /K; lra.
have h3 := ler_wpM2r (mulr_ge0 (ltW heK) hp) hcmK.
have heq : K*((e/K)*`|t|^+k)=e*`|t|^+k.
  by rewrite mulrA [K*(e/K)]mulrC divfK ?gt_eqF.
apply: le_trans (le_trans h0 h1) _.
have heq2 : C*NX (f t)*M=C*M*NX (f t) by ring.
rewrite heq2; apply: le_trans h2 _.
by rewrite heq in h3.
Qed.

(** Source for [norm_little_o_bilinear_bounded_left]:
    the counterpart with the bounded factor
    on the left, supporting Federer 3.1.11,
    p. 222. The bilinear operation
    need not be commutative. *)
Lemma norm_little_o_bilinear_bounded_left (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (B : X->Y->Z) C (f : R->X) (g : R->Y) k M r :
  0<=C -> (forall x y, NZ (B x y)<=C*NX x*NY y) ->
  0<=M -> 0<r -> (forall t, `|t|<r -> NX (f t)<=M) ->
  norm_little_o_power NY g k ->
  norm_little_o_power NZ (fun t=>B (f t) (g t)) k.
Proof.
move=>hC hB hM hr hf hg.
apply: (@norm_little_o_bilinear_bounded_right R Y X Z NY NX NZ hNY hNX
  (fun y x=>B x y) C g f k M r hC _ hM hr hf hg).
move=>y x; rewrite [C*NY y*NX x]mulrAC; exact: hB.
Qed.

(** Source for [norm_product_of_approximations_remainder]:
    replacing both factors by their jets
    changes the product by o(|t|^k),
    Federer 3.1.11, p. 222.
    Local boundedness is used only in this
    auxiliary estimate and is discharged by
    continuity in its calculus applications. *)
Theorem norm_product_of_approximations_remainder (R : realType)
    (X Y Z : lmodType R) (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (B : X->Y->Z) (hB : bilinear B) C
    (f P : R->X) (g Q : R->Y) k M L r s :
  0<=C -> (forall x y, NZ (B x y)<=C*NX x*NY y) ->
  0<=M -> 0<r -> (forall t, `|t|<r -> NY (g t)<=M) ->
  0<=L -> 0<s -> (forall t, `|t|<s -> NX (P t)<=L) ->
  norm_little_o_power NX (fun t=>f t-P t) k ->
  norm_little_o_power NY (fun t=>g t-Q t) k ->
  norm_little_o_power NZ (fun t=>B (f t) (g t)-B (P t) (Q t)) k.
Proof.
move=>hC hb hM hr hg hL hs hP hfO hgO.
have hleft := norm_little_o_bilinear_bounded_right hNX hNY hC hb hM hr hg hfO.
have hright := norm_little_o_bilinear_bounded_left hNX hNY hC hb hL hs hP hgO.
have hh := norm_little_o_power_add hNZ hleft hright.
have he : (fun t=>B (f t-P t) (g t)+B (P t) (g t-Q t))=
    (fun t=>B (f t) (g t)-B (P t) (Q t)).
  apply: funext=>t; rewrite (bilBl hB) (bilBr hB).
  by rewrite addrA subrK.
by rewrite he in hh.
Qed.
