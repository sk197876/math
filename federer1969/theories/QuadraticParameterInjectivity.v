(** Federer (1969), 3.4.5, p. 321: both original
    quadratic parameter coefficient families determine all
    original two-coordinate Taylor coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import QuadraticSubstitutionParameterCoefficients QuadraticFormalRemainder
  QuadraticParameterRemainderIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [quadratic_parameter_coefficients_injective]: the
    actual finite even and odd parameter equations force
    every original coefficient to be zero, supporting
    the example cited in 3.4.5, p. 321. *)
Theorem quadratic_parameter_coefficients_injective (K:fieldType) (a:nat->nat->K):
  (forall parity,(parity=0%N \/parity= 1%N) ->forall N ell,
    quadratic_substitution_parameter_coefficient parity N ell (fun i k=>a i (2*k+parity)%N)=0) ->
  forall i j,a i j=0.
Proof.
move=>hZero.
have hOriginal parity (hParity:parity=0%N \/parity= 1%N) N ell:
    @quadratic_formal_remainder_coefficient K K^o a parity N ell=0.
  case:(leqP ell N)=>[hEll|hBeyond].
  - rewrite -quadratic_parameter_original_remainder //;exact:hZero parity hParity N ell.
  - have hSub:(N-ell=0)%N by apply/eqP;rewrite subn_eq0;exact:ltnW hBeyond.
    have hPositive:(0<ell)%N:=leq_ltn_trans (leq0n N) hBeyond.
    have hNot:~~(ell<=0)%N by rewrite -ltnNge.
    by rewrite /quadratic_formal_remainder_coefficient hSub big_mkcond big_ord1 /= (negbTE hNot).
exact:(@quadratic_formal_remainder_injective K K^o a
  (hOriginal 0%N (or_introl (erefl _))) (hOriginal 1%N (or_intror (erefl _)))).
Qed.
