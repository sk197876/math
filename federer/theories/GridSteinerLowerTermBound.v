(** Federer (1969), 3.2.38, p. 275: every coefficient below
    the source degree gives an error of order 1/v after normalization. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import GridReversePowerNormalization SteinerReversePolynomialBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [grid_steiner_lower_term_bound]: supporting the
    j<m terms in the corrected full Steiner estimate of Federer
    3.2.38, p. 275. In particular j=0 is included. Positive
    radius and v>=1 give (1/v)^(m-j)<=1/v, without cancelling
    a zero normalizer or assuming a positive exterior Jacobian. *)
Lemma grid_steiner_lower_term_bound (R:realType) (v r A U b C:R) j m n:
  1<=v ->0<r ->0<=A ->0<=C ->(j<m)%N ->(m<=n)%N ->
  A^+(n-j)<=U ->b<=C*(v*r)^+j ->
  b*(A*r)^+(n-j)/r^+(n-m)<=C*(v*r)^+m*U/v.
Proof.
move=>hv1 hr hA hC hjm hmn hPower hCoefficient.
have hv:0<v:=lt_le_trans ltr01 hv1.
have ht0:0<=v^-1 by rewrite invr_ge0; exact:ltW hv.
have ht1:v^-1<=1 by rewrite invf_le1.
have hFactor:0<=(A*r)^+(n-j)/r^+(n-m).
  apply:divr_ge0.
  - exact:exprn_ge0 _ (mulr_ge0 hA (ltW hr)).
  - exact:exprn_ge0 _ (ltW hr).
have hFirst:b*(A*r)^+(n-j)/r^+(n-m)<=
    C*((v*r)^+j*(A*r)^+(n-j)/r^+(n-m)).
  have h:=ler_wpM2r hFactor hCoefficient.
  rewrite !mulrA in h; rewrite !mulrA; exact h.
apply:le_trans hFirst _.
rewrite (@grid_reverse_power_normalization R v r A j m n hv hr (ltnW hjm) hmn).
have hPositiveExponent:(0<m-j)%N by rewrite subn_gt0.
have hSmallPower:(v^-1)^+(m-j)<=v^-1.
  exact:(@unit_interval_positive_power_le R (v^-1) ht0 ht1 (m-j) hPositiveExponent).
have hProduct:A^+(n-j)*(v^-1)^+(m-j)<=U*v^-1.
  exact:ler_pM (exprn_ge0 _ hA) (exprn_ge0 _ ht0) hPower hSmallPower.
have hPrefactor:0<=C*(v*r)^+m.
  exact:mulr_ge0 hC (exprn_ge0 _ (mulr_ge0 (ltW hv) (ltW hr))).
have hLeft:C*((v*r)^+m*A^+(n-j)*(v^-1)^+(m-j))=
    (C*(v*r)^+m)*(A^+(n-j)*(v^-1)^+(m-j)) by ring.
have hRight:C*(v*r)^+m*U/v=(C*(v*r)^+m)*(U*v^-1) by ring.
rewrite hLeft hRight; exact (ler_wpM2l hPrefactor hProduct).
Qed.
