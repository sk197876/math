(** Federer (1969), 3.2.13, p. 251: cancel the
    positive sphere mass and common Gamma powers in the
    comparison of the coordinate moment and its Haar integral. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_moment_quotient_cancel]: scalar
    cancellation in the displayed beta_t(m,1) formula, Federer
    3.2.13, p. 251. Positivity of every factor being
    cancelled is required and is proved for Gamma before use. *)
Lemma projection_moment_quotient_cancel (R:realType) (H P D S A b:R):
  0<H ->0<P ->0<D ->0<S ->
  (2*H*P/D)*b= 2*A*P/S ->b=A*D/(S*H).
Proof.
move=>hH hP hD hS hEq.
have hTwo:0<(2:R) by lra.
have hCoef:0<2*H*P/D:=divr_gt0 (mulr_gt0 (mulr_gt0 hTwo hH) hP) hD.
have hHN:H!= 0:=lt0r_neq0 hH.
have hDN:D!= 0:=lt0r_neq0 hD.
have hSN:S!= 0:=lt0r_neq0 hS.
apply:(mulfI (lt0r_neq0 hCoef)).
rewrite hEq.
field; by rewrite ?mulf_eq0 ?(negbTE hHN) ?(negbTE hDN) ?(negbTE hSN).
Qed.
