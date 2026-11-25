(** Federer (1969), 3.2.13, p. 251: the last
    formula beta_1(n,m)=Gamma((m+1)/2)Gamma((n-m+1)/2)
    divided by Gamma((n+1)/2)Gamma(1/2), for n>=m>=1. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp constructive_ereal.
From Federer Require Import ProjectionBeta ProjectionBetaGammaProduct GammaHalfSequences
  PositiveTelescopingProduct RealPower.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [projection_beta_first_gamma_formula]: the final
    displayed formula of Federer 3.2.13, p. 251. The
    half-sequence is exactly Gamma((j+1)/2), so the statement
    retains the printed quotient in every n>=m>=1. *)
Theorem projection_beta_first_gamma_formula (R:realType) n m
    (hm:(0<m)%N) (hmn:(m<=n)%N):
  @projection_beta R n m hmn (1%R:R)%:E=
    gamma_half_sequence R m*gamma_half_sequence R (n-m)/
      (gamma_half_sequence R n*gamma_half_sequence R 0%N).
Proof.
have ht:(1:R)<=1:=lexx 1.
have htE:(1<=(1%R:R)%:E)%E by rewrite lee_fin.
have hPos:=@projection_beta_positive R n m hmn (1%R:R)%:E htE.
have hProd:=@projection_beta_gamma_product R n m hm hmn 1 ht.
rewrite real_power_one_exponent ?(ltW hPos) // in hProd.
have hFactors:(\prod_(j<n-m)
    (gamma_half_sequence R (m+j)*gamma_shifted_half_sequence ht j/
      (gamma_half_sequence R j*gamma_shifted_half_sequence ht (m+j))))=
    \prod_(j<n-m) (gamma_half_sequence R (m+j)*gamma_half_sequence R j.+1/
      (gamma_half_sequence R j*gamma_half_sequence R (m+j).+1)).
  apply:eq_bigr=>j _; by rewrite !gamma_shifted_half_sequence_one.
rewrite hFactors (@positive_shifted_telescoping_product R (gamma_half_sequence R) m (n-m)%N
  (fun j=>gamma_half_sequence_positive R j)) in hProd.
have hDim:(m+(n-m)=n)%N:=subnKC hmn.
by rewrite hDim in hProd.
Qed.
