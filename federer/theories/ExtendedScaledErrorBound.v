(** Vanishing finite error in Federer (1969), 2.10.18(1), p. 180, proof: the
    finite-tail estimate contains an arbitrarily small positive error. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal lra.
From Federer Require Import ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_upper_bound_from_scaled_errors]: supporting removal
    of a finite scaled error in 2.10.18(1), p. 180 Infinite x is allowed,
    but the approximating base and error coefficient are finite. *)
Lemma extended_upper_bound_from_scaled_errors (R : realType) (x : \bar R) (p b : R) :
  (0<=b)%R -> (forall e : R, (0<e)%R -> x<=(p+b*e)%:E) -> x<=p%:E.
Proof.
move=> hb herror; apply: extended_real_reciprocal_upper_bound=> n.
pose r := (((n.+1)%:R : R)^-1)%R.
have hr : (0<r)%R by rewrite /r invr_gt0 ltr0n.
have hbp : (0<b+1)%R by lra.
have hbne : (b+1!=0)%R by rewrite gt_eqF.
pose e := (r/(b+1))%R.
have he : (0<e)%R by rewrite /e divr_gt0.
have hble : (b<=b+1)%R by lra.
have hmul := ler_wpM2r (ltW he) hble.
have heq : ((b+1)*e=r)%R by rewrite mulrC /e divfK.
rewrite heq in hmul.
apply: le_trans (herror e he) _; rewrite lee_fin; exact: lerD (lexx p) hmul.
Qed.
