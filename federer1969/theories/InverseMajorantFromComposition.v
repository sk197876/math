(** Federer (1969), 3.1.24, p. 240: the exact
    scalar inverse-composition coefficients satisfy the defining
    inverse-majorant recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import ScalarAffineDifferentials InverseMajorantUP InverseCompositionScalarSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_majorant_from_composition]: supporting
    the identification of lambda_p with the normalized scalar
    inverse derivatives in Federer 3.1.24, p. 240.
    Separating the outer-linear term in g composed with f
    gives lambda_1=(beta gamma)^-1 and the displayed lower-
    order recurrence. All required coefficient identities are
    hypotheses about the actual composition, not assumed bounds. *)
Theorem inverse_majorant_from_composition (R:realType) (b g:R) (lambda:nat->R) :
  0<b -> 0<g -> lambda 0%N=0 ->
  (forall p,(1<=p)%N -> inverse_composition_scalar_sum b g lambda p=
    scalar_affine_derivative_coefficient 1 0 p 0/(p`!)%:R) ->
  is_inverse_majorant_sequence b g lambda.
Proof.
move=>hb hg h0 hsum.
have hbg:0<b*g:=mulr_gt0 hb hg.
have hbg0:b*g!=0 by rewrite gt_eqF.
have hFirst:(b*g)*lambda 1%N= 1.
  have hh:=hsum 1%N (leqnn 1%N).
  rewrite inverse_composition_scalar_sum_split // inverse_majorant_remainder_one subr0
    /scalar_affine_derivative_coefficient /= ?divr1 in hh.
  exact hh.
have h1:lambda 1%N=(b*g)^-1.
  apply:(mulfI hbg0); by rewrite hFirst mulfV.
split; first exact h0.
split; first exact h1.
move=>p hp.
have hRight:(@scalar_affine_derivative_coefficient R 1 0 p 0)/(p`!)%:R=0.
  case:p hp=>[|[|p]] hp.
  - by [].
  - by [].
  - change ((0:R)/(p.+2`!)%:R=0); by rewrite mul0r.
have hp1:(1<=p)%N:=leq_trans (leqnSn 1%N) hp.
have hh:=hsum p hp1.
rewrite (inverse_composition_scalar_sum_split b g lambda hp1) hRight in hh.
have hProd:(b*g)*lambda p= inverse_majorant_remainder g lambda p.
  apply/eqP; rewrite -subr_eq0; exact/eqP.
apply:(mulfI hbg0).
by rewrite h1 mulrA mulfV // mul1r hProd.
Qed.
