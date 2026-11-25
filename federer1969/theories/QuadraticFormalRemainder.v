(** Federer (1969), 3.4.5, p. 321: finite
    coefficient identities for the actual substitution
    y^2=-x^2+t*x^3 in the real Taylor proof of
    the example cited to Cartan (1957), pp. 97–99.
    Only finite sums of coefficients occur here. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import FiniteUpperTriangularVanishing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [quadratic_formal_remainder_coefficient]:
    the coefficient of x^N*t^ell in the even or
    odd remainder after the quadratic substitution, supporting
    the example cited in 3.4.5, p. 321. Parity
    zero is the even y part and parity one is
    the coefficient of y in the odd part. *)
Definition quadratic_formal_remainder_coefficient (K:fieldType) (V:lmodType K)
    (a:nat->nat->V) (parity N ell:nat):V:=
  \sum_(k<(N-ell).+1 | ((ell<=k) && (2 * k+parity<=N-ell))%N)
    (('C(k,ell))%:R*(-1)^+(k-ell))*:a (N-ell-(2 * k+parity))%N (2 * k+parity)%N.

(** Source for [quadratic_formal_remainder_parity_injective]:
    zero finite quadratic-substitution remainders force every
    original coefficient of the corresponding parity to be
    zero, supporting the actual Taylor argument for the
    example cited in 3.4.5, p. 321. The
    signed finite binomial system has proved unit diagonal. *)
Theorem quadratic_formal_remainder_parity_injective (K:fieldType) (V:lmodType K)
    (a:nat->nat->V) parity:
  (forall N ell,@quadratic_formal_remainder_coefficient K V a parity N ell=0) ->
  forall i k,a i (2 * k+parity)%N=0.
Proof.
move=>hRemainder i k.
pose d:=(i+(2 * k+parity))%N.
pose b j:=if (2 * j+parity<=d)%N then a (d-(2 * j+parity))%N (2 * j+parity)%N else 0.
have hTransform ell (hEll:(ell<d.+1)%N):
    \sum_(j<d.+1 | (ell<=j)%N) (('C(j,ell))%:R*(-1)^+(j-ell))*:b j=0.
  have hZero:=hRemainder (d+ell)%N ell.
  rewrite /quadratic_formal_remainder_coefficient addnK in hZero.
  have hEquality:(\sum_(j<d.+1 | (ell<=j)%N) (('C(j,ell))%:R*(-1)^+(j-ell))*:b j)=
      \sum_(j<d.+1 | ((ell<=j) && (2 * j+parity<=d))%N)
        (('C(j,ell))%:R*(-1)^+(j-ell))*:a (d-(2 * j+parity))%N (2 * j+parity)%N.
    rewrite [LHS]big_mkcond [RHS]big_mkcond.
    apply:eq_bigr=>j _;rewrite /b.
    by case:(ell<=j)%N;case:(2 * j+parity<=d)%N;rewrite /= ?scaler0.
  by rewrite hEquality.
have hAll:=@finite_signed_binomial_vanishing K V b d.+1 hTransform.
have hBound:(2 * k+parity<=d)%N by rewrite /d leq_addl.
have hKTwo:(k<=2 * k+parity)%N.
  rewrite mul2n -addnn;exact:leq_trans (leq_addr k k) (leq_addr parity (k+k)).
have hK:(k<d.+1)%N by rewrite ltnS;exact:leq_trans hKTwo hBound.
have hZero:=hAll k hK.
by rewrite /b hBound /d addnK in hZero.
Qed.

(** Source for [quadratic_formal_remainder_injective]: the
    actual even and odd finite coefficient identities together
    determine every original Taylor coefficient, supporting the
    example cited at 3.4.5, p. 321. *)
Theorem quadratic_formal_remainder_injective (K:fieldType) (V:lmodType K)
    (a:nat->nat->V):
  (forall N ell,@quadratic_formal_remainder_coefficient K V a 0%N N ell=0) ->
  (forall N ell,@quadratic_formal_remainder_coefficient K V a 1%N N ell=0) ->
  forall i j,a i j=0.
Proof.
move=>hEven hOdd i j.
have hParity p:(p=0%N \/p= 1%N) ->forall k,a i (2 * k+p)%N=0.
  move=>[->|->].
  - exact:(@quadratic_formal_remainder_parity_injective K V a 0%N hEven i).
  - exact:(@quadratic_formal_remainder_parity_injective K V a 1%N hOdd i).
have hChoice:((odd j:bool):nat)=0%N \/((odd j:bool):nat)= 1%N by case:(odd j);[right|left].
have hZero:=hParity (odd j) hChoice j./2.
by rewrite mul2n addnC odd_double_half in hZero.
Qed.
