(** Federer (1969), 3.2.13, p. 251: the Gamma
    product formula for beta_t(n,m)^t, with the printed
    dimensions m+1 through n indexed by their offsets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal ring.
From Federer Require Import ProjectionBeta ProjectionBetaRatio ProjectionBetaFiniteProduct ProjectionBetaOneGamma
  GammaHalfSequences EulerGamma EulerGammaHalfParameters RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_beta_one_gamma_sequences]: the
    degree-one Gamma quotient in half-sequence notation,
    Federer 3.2.13, p. 251. *)
Lemma projection_beta_one_gamma_sequences (R:realType) (t:R) (ht:1<=t) j:
  real_power (@projection_beta R j.+1 1 (ltn0Sn j) t%:E) t=
    gamma_shifted_half_sequence ht 0*gamma_half_sequence R j/
    (gamma_shifted_half_sequence ht j*gamma_half_sequence R 0).
Proof.
rewrite gamma_half_sequence_zero gamma_shifted_half_sequence_zero
  /gamma_half_sequence /gamma_shifted_half_sequence.
exact:projection_beta_one_gamma_formula ht.
Qed.

(** Source for [gamma_projection_common_factors_cancel]: cancellation
    of common Gamma((t+1)/2) and Gamma(1/2) factors
    in the one-dimensional quotient, Federer 3.2.13, p. 251. *)
Lemma gamma_projection_common_factors_cancel (R:realType) (A H B C D E:R):
  0<A ->0<H ->0<C ->0<D ->0<E ->
  (A*B/(C*H))/(A*D/(E*H))=B*E/(D*C).
Proof.
move=>hA hH hC hD hE.
have hAN:A!= 0:=lt0r_neq0 hA.
have hHN:H!= 0:=lt0r_neq0 hH.
have hCN:C!= 0:=lt0r_neq0 hC.
have hDN:D!= 0:=lt0r_neq0 hD.
have hEN:E!= 0:=lt0r_neq0 hE.
field; by rewrite ?mulf_eq0 ?(negbTE hAN) ?(negbTE hHN) ?(negbTE hCN) ?(negbTE hDN) ?(negbTE hEN).
Qed.

(** Source for [projection_beta_gamma_ratio_factor]: the j-th
    Gamma factor in the finite product of Federer 3.2.13,
    p. 251, after substituting the degree-one quotient. *)
Lemma projection_beta_gamma_ratio_factor (R:realType) m (t:R) (ht:1<=t) j:
  projection_beta_one_power_ratio m ht j=
    gamma_half_sequence R (m+j)*gamma_shifted_half_sequence ht j/
      (gamma_half_sequence R j*gamma_shifted_half_sequence ht (m+j)).
Proof.
rewrite /projection_beta_one_power_ratio !projection_beta_one_gamma_sequences.
exact (@gamma_projection_common_factors_cancel R
  (gamma_shifted_half_sequence ht 0) (gamma_half_sequence R 0) (gamma_half_sequence R (m+j))
  (gamma_shifted_half_sequence ht (m+j)) (gamma_half_sequence R j) (gamma_shifted_half_sequence ht j)
  (gamma_shifted_half_sequence_positive ht 0) (gamma_half_sequence_positive R 0)
  (gamma_shifted_half_sequence_positive ht (m+j)) (gamma_half_sequence_positive R j)
  (gamma_shifted_half_sequence_positive ht j)).
Qed.

(** Source for [projection_beta_offset_gamma_product]: the
    printed Gamma product with n=m+k, Federer 3.2.13,
    p. 251. No product identity is part of the beta definition. *)
Lemma projection_beta_offset_gamma_product (R:realType) m (hm:(0<m)%N) k (t:R) (ht:1<=t):
  real_power (@projection_beta R (m+k) m (leq_addr k m) t%:E) t=
    \prod_(j<k) (gamma_half_sequence R (m+j)*gamma_shifted_half_sequence ht j/
      (gamma_half_sequence R j*gamma_shifted_half_sequence ht (m+j))).
Proof.
rewrite (projection_beta_offset_product hm ht).
apply:eq_bigr=>j _; exact:projection_beta_gamma_ratio_factor.
Qed.

(** Source for [projection_beta_gamma_product]: the displayed
    finite product for every n>=m>= 1 and finite t>= 1,
    Federer 3.2.13, p. 251. Offset j denotes the printed
    index m+j+1, so the factors are exactly Gamma((m+j+1)/2)
    Gamma((t+j+1)/2) divided by Gamma((j+1)/2)
    Gamma((t+m+j+1)/2). *)
Theorem projection_beta_gamma_product (R:realType) n m (hm:(0<m)%N)
    (hmn:(m<=n)%N) (t:R) (ht:1<=t):
  real_power (@projection_beta R n m hmn t%:E) t=
    \prod_(j<n-m) (gamma_half_sequence R (m+j)*gamma_shifted_half_sequence ht j/
      (gamma_half_sequence R j*gamma_shifted_half_sequence ht (m+j))).
Proof.
have hDim:(m+(n-m)=n)%N:=subnKC hmn.
have hProd:=@projection_beta_offset_gamma_product R m hm (n-m)%N t ht.
rewrite (@projection_beta_dimension_transport R (m+(n-m)) n m
  (leq_addr (n-m) m) hmn t%:E hDim) in hProd.
exact:hProd.
Qed.
