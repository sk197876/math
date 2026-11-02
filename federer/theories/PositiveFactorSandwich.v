(** Federer (1969), 3.2.22, pp. 259–260:
    supporting algebra for the two almost-isometric
    chart comparisons. All divisors are proved positive. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_factor_sandwich]: the bounds
    for J_mu phi_ij from J_mu(F composed psi_i)
    and J_mu gamma_j in Federer 3.2.22, p. 259.
    A factor between p inverse and p may be removed
    at the cost of the same two multiplicative bounds. *)
Lemma positive_factor_sandwich (R:realType) (p t f h:R):
  0<p ->0<=f ->p^-1<=t ->t<=p ->h=t*f ->
  p^-1*h<=f /\ f<=p*h.
Proof.
move=>hp hf hLo hHi ->.
have hInv:0<p^-1 by rewrite invr_gt0.
have hCancel1:p^-1*(p*f)=f by rewrite mulrA mulVf ?gt_eqF ?mul1r.
have hCancel2:p*(p^-1*f)=f by rewrite mulrA mulfV ?gt_eqF ?mul1r.
split.
- have hScaled:=ler_wpM2l (ltW hInv) (ler_wpM2r hf hHi).
  by rewrite hCancel1 in hScaled.
- have hScaled:=ler_wpM2l (ltW hp) (ler_wpM2r hf hLo).
  by rewrite hCancel2 in hScaled.
Qed.

(** Source for [iterated_positive_factor_sandwich]: the
    lambda^(+/-2mu) comparison implicit in Federer 3.2.22,
    p. 259, combines the source and target chart
    inequalities. This is multiplication of nonnegative
    bounds, with no finiteness or nonzero Jacobian premise. *)
Lemma iterated_positive_factor_sandwich (R:realType) (p j h f:R):
  0<p ->p^-1*j<=h ->h<=p*j ->p^-1*h<=f ->f<=p*h ->
  (p* p)^-1*j<=f /\ f<=(p* p)*j.
Proof.
move=>hp hSL hSU hTL hTU.
have hInv:0<p^-1 by rewrite invr_gt0.
have hInvProduct:(p* p)^-1=p^-1* p^-1.
  by rewrite invrM ?unitfE ?(gt_eqF hp).
split.
- have hLower:=le_trans (ler_wpM2l (ltW hInv) hSL) hTL.
  rewrite hInvProduct.
  change (is_true ((p^-1* p^-1)*j<=f)).
  by rewrite -mulrA.
- rewrite -mulrA.
  exact:(le_trans hTU (ler_wpM2l (ltW hp) hSU)).
Qed.
