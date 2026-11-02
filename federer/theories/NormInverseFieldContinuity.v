(** Federer (1969), 3.1.1, p. 210: continuity of the inverse
    differential field, supporting the class-one inverse assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  NormInversePerturbation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_inverse_field_continuous]: supporting step in
    Federer 3.1.1, p. 210: a continuous field of bounded invertible
    linear maps has a continuous inverse field. The proof derives the
    needed uniform inverse bounds locally; none is assumed globally. *)
Theorem norm_inverse_field_continuous (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop)
    (D : X -> Hom X Y) (E : X -> Hom Y X) :
  norm_field_continuous NX NY A D ->
  (forall x, A x -> norm_bounded_linear NY NX (E x)) ->
  (forall x, A x -> forall v, E x (D x v)=v) ->
  (forall x, A x -> forall w, D x (E x w)=w) ->
  forall a, A a -> forall e : R, 0 < e -> exists r : R, 0 < r /\
    forall h, A (a+h) -> NX h < r -> forall w,
      NX (E (a+h) w-E a w) <= e*NY w.
Proof.
move=> hD hE hED hDE a ha e he.
have [C0 [hC0 hE0]] := hE a ha.
pose C := C0+1.
have hC : 0 < C by rewrite /C; lra.
have hMC : forall w, NX (E a w) <= C*NY w.
  move=> w; apply: le_trans (hE0 w) _.
  apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNY.1 w.
  rewrite /C; lra.
have h2C : 0 < 2*C by rewrite mulr_gt0 // ltr0n.
have h2CC : 0 < 2*C*C by rewrite mulr_gt0.
pose p := Num.min (1/(2*C)) (e/(2*C*C)).
have hp : 0 < p by rewrite /p lt_min !divr_gt0 // ltr01 he.
have hp1 : p <= 1/(2*C) by rewrite /p ge_min lexx.
have hp2 : p <= e/(2*C*C) by rewrite /p ge_min lexx orbT.
have hpC : 2*C * p <= 1 by move: hp1; rewrite ler_pdivlMr // mulrC.
have hpCC : p*(2*C*C) <= e by move: hp2; rewrite ler_pdivlMr.
have [r [hr hb]] := hD a ha p hp.
exists r; split=> // h hh hs w.
have hpert : forall v, NY (D (a+h) v-D a v) <= p*NX v := hb h hh hs.
have hM := @norm_inverse_perturbation_bound R X Y NX NY hNX hNY
  (D a) (D (a+h)) (E a) (E (a+h)) C p hC (ltW hp) hpC
  (hED a ha) (hDE (a+h) hh) hMC hpert.
have hdif := @norm_inverse_difference_bound R X Y NX NY hNY
  (D a) (D (a+h)) (E a) (E (a+h)) C (2*C) p (ltW h2C) (ltW hp)
  (hDE a ha) (hED (a+h) hh) hMC hM hpert w.
apply: le_trans hdif _.
apply: ler_wpM2r; first exact: real_seminorm_nonnegative hNY.1 w.
have heq : 2*C * p*C = p*(2*C*C) by ring.
by rewrite heq.
Qed.
