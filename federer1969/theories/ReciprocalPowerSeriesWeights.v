(** Federer (1969), 4.1.12, p. 369:
    the original reciprocal-cube weights cancel
    the derivative and squared endpoint
    factors in psi_m. These are
    finite scalar identities, with the
    original positive integer index. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ReciprocalPowerSeriesBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reciprocal_power_series_weight_le_one]:
    every original reciprocal-power coefficient
    is at most one, supporting the
    comass estimate in Federer 4.1.12,
    p. 369. Power zero is included. *)
Lemma reciprocal_power_series_weight_le_one (R:realType) p n:
  reciprocal_power_series_weight R p n<=1.
Proof.
pose x:R:=(n.+1)%:R.
have hPositive:0<x by rewrite /x ltr0n.
have hInversePositive:0<x^-1 by rewrite invr_gt0.
have hOne:1<=x by rewrite /x ler1n.
have hInverseBound:x^-1<=1.
  rewrite -[1]invr1 (@lef_pV2 R x 1 hPositive (@ltr01 R)).
  exact:hOne.
change (is_true (x^-1^+p<=1)).
exact:(@exprn_ile1 R p x^-1 (ltW hInversePositive) hInverseBound).
Qed.

(** Source for [reciprocal_cube_derivative_product]: the
    original k^(-3) cancels k^3,
    supporting M(d psi_m)<=2 in
    Federer 4.1.12, p. 369. *)
Lemma reciprocal_cube_derivative_product (R:realType) n:
  reciprocal_power_series_weight R 3%N n*((n.+1)%:R)^+3= 1.
Proof.
rewrite /reciprocal_power_series_weight exprVn.
by rewrite mulVf ?expf_neq0 ?pnatr_eq0.
Qed.

(** Source for [reciprocal_cube_endpoint_square_product]:
    the original k^(-3) k^2 equals
    k^(-1), giving the harmonic terms
    in Federer 4.1.12, p. 369. *)
Lemma reciprocal_cube_endpoint_square_product (R:realType) n:
  reciprocal_power_series_weight R 3%N n*((n.+1)%:R)^+2=((n.+1)%:R:R)^-1.
Proof.
rewrite /reciprocal_power_series_weight exprS -mulrA exprVn.
by rewrite mulVf ?expf_neq0 ?pnatr_eq0 // mulr1.
Qed.
