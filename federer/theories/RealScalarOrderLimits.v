(** Federer (1969), 2.4.17, p. 90: continuity in the exponent. These
    supporting scalar sequence laws use order intervals only. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [real_constant_order_limit]: constant-sequence background
    supporting the continuity claim in Federer 2.4.17, p. 90 *)
Lemma real_constant_order_limit (R : realType) (a : R) :
  extended_order_limit (fun _ : nat => a%:E) a%:E.
Proof. split=> b hb; exists 0%N=> n hn; exact hb. Qed.

(** Source for [real_scalar_order_limit]: passage to a scalar multiple of
    the exponent in the exponential formula for powers, supporting Federer
    2.4.17, p. 90 No integration assertion is imported here. *)
Lemma real_scalar_order_limit (R : realType) (u : nat -> R) (l c : R) :
  extended_order_limit (fun n => (u n)%:E) l%:E ->
  extended_order_limit (fun n => (c * u n)%:E) (c * l)%:E.
Proof.
move=> hl; apply: real_error_extended_order_limit=> e he.
have hc : (0 < 1+`|c|)%R := ltr_pwDl ltr01 (normr_ge0 c).
have hene : (0 < e/(1+`|c|))%R by rewrite divr_gt0.
have [k hk] := @extended_finite_order_limit_error R u l _ hl hene.
exists k=> n hn; rewrite -mulrBr normrM.
have h1 : (`|c|*`|u n-l| <= (1+`|c|)*`|u n-l|)%R.
  apply: (ler_wpM2r (normr_ge0 _)); by rewrite lerDr ler01.
have h2 : ((1+`|c|) * `|u n-l| < (1+`|c|) * (e/(1+`|c|)))%R.
  by rewrite (ltr_pM2l hc); exact: hk n hn.
rewrite mulrCA mulfV ?gt_eqF // mulr1 in h2.
exact: le_lt_trans h1 h2.
Qed.

(** Source for [real_affine_order_limit]: elementary affine passage
    supporting the logarithmic upper bound at infinity in Federer 2.4.17, p.
    90 The limit is proved in order intervals. *)
Lemma real_affine_order_limit (R : realType) (u : nat -> R) (l c d : R) :
  extended_order_limit (fun n => (u n)%:E) l%:E ->
  extended_order_limit (fun n => (d+c * u n)%:E) (d+c * l)%:E.
Proof.
move=> hl; have hscaled := @real_scalar_order_limit R u l c hl.
apply: real_error_extended_order_limit=> e he.
have [k hk] := @extended_finite_order_limit_error R (fun n => (c * u n)%R) (c * l)%R e hscaled he.
exists k=> n hn; rewrite opprD addrACA subrr add0r; exact: hk n hn.
Qed.
