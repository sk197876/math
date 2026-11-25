(** Federer (1969), 3.2.28(5), p. 267:
    the actual positive-parameter Euler Gamma product
    in the denominator of the Stiefel volume formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [stiefel_gamma_argument_positive]: all Gamma
    arguments (n-j+1)/2 in Federer 3.2.28(5),
    p. 267, are positive when 1<=j<=m<=n.
    The ordinal index i=j-1 is zero based. *)
Lemma stiefel_gamma_argument_positive (R:realType) n m (hmn:(m<=n)%N) (i:'I_m):
  0<((n-i)%N%:R:R)/2.
Proof.
apply:positive_dimension_half.
rewrite subn_gt0; exact:leq_trans (ltn_ord i) hmn.
Qed.

(** Source for [stiefel_gamma_factor]: the actual Gamma
    factor at (n-j+1)/2 in Federer 3.2.28(5),
    p. 267. Evaluation uses its proved positive
    domain, rather than a default value outside it. *)
Definition stiefel_gamma_factor (R:realType) n m (hmn:(m<=n)%N) (i:'I_m):R:=
  euler_gamma (@stiefel_gamma_argument_positive R n m hmn i).

(** Source for [stiefel_gamma_product]: the displayed
    denominator product of Gamma((n-j+1)/2),
    1<=j<=m, Federer 3.2.28(5), p. 267.
    Its empty product is one. *)
Definition stiefel_gamma_product (R:realType) n m (hmn:(m<=n)%N):R:=
  \prod_(i:'I_m) (@stiefel_gamma_factor R n m hmn i).

(** Source for [stiefel_gamma_product_positive]: positivity
    justifies division by the product in Federer
    3.2.28(5), p. 267. *)
Lemma stiefel_gamma_product_positive (R:realType) n m (hmn:(m<=n)%N):
  0<stiefel_gamma_product R hmn.
Proof.
apply:prodr_gt0=>i _; exact:euler_gamma_positive.
Qed.

(** Source for [stiefel_gamma_product_zero]: empty-product
    boundary of the formula in Federer 3.2.28(5),
    p. 267, supporting its degree-zero extension. *)
Lemma stiefel_gamma_product_zero (R:realType) n (h:(0<=n)%N):
  stiefel_gamma_product R h= 1.
Proof. by rewrite /stiefel_gamma_product big_ord0. Qed.

(** Source for [stiefel_gamma_product_successor]: separate
    the last denominator factor for the induction in
    Federer 3.2.28(5), p. 267. Positivity
    proof arguments do not change a Gamma value. *)
Lemma stiefel_gamma_product_successor (R:realType) n k
    (hkn:(k.+1<=n)%N) (hk:(k<=n)%N) (hPos:(0<n-k)%N):
  stiefel_gamma_product R hkn=stiefel_gamma_product R hk*
    euler_gamma (@positive_dimension_half R (n-k) hPos).
Proof.
rewrite /stiefel_gamma_product big_ord_recr.
congr (_ * _).
- apply:eq_bigr=>i _; exact:euler_gamma_proof_irrelevant.
- exact:euler_gamma_proof_irrelevant.
Qed.
