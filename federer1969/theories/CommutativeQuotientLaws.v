(** Federer (1969), 3.4.8(8), pp. 329–330:
    the original prime-ideal quotient is a domain.
    Use only its independent kernel and surjection
    laws, without a chosen quotient representation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeDomainUP CommutativeQuotientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Laws.
Variables A C:comNzRingType.
Variable I:set A.
Variable pi:{rmorphism A->C}.
Variable hQuotient:is_commutative_ideal_quotient I pi.

(** Source for [commutative_quotient_equality]: two original
    germs have equal quotient image exactly when
    their difference is in I_g,
    supporting 3.4.8(8), pp. 329–330. *)
Lemma commutative_quotient_equality x y:pi x = pi y <->I (x-y).
Proof.
split.
- move=>hEqual;apply:(commutative_quotient_kernel hQuotient (x-y)).1.
  by rewrite rmorphB hEqual subrr.
- move=>hI;apply/eqP;rewrite -subr_eq0 -rmorphB;apply/eqP.
  exact:(commutative_quotient_kernel hQuotient (x-y)).2 hI.
Qed.

(** Source for [commutative_quotient_nonzero]: an original
    germ has nonzero image exactly when it
    lies outside I_g, 3.4.8(8), p. 330. *)
Lemma commutative_quotient_nonzero x:pi x<>0 <->~I x.
Proof.
split.
- move=>hNonzero hI;apply:hNonzero;exact:(commutative_quotient_kernel hQuotient x).2 hI.
- move=>hNotI hZero;apply:hNotI;exact:(commutative_quotient_kernel hQuotient x).1 hZero.
Qed.

(** Source for [prime_commutative_quotient_domain]: the
    original quotient by prime I_g is an
    integral domain, 3.4.8(8), p. 329.
    No absence-of-zero-divisors premise is added. *)
Theorem prime_commutative_quotient_domain:is_prime_commutative_ideal I ->is_commutative_integral_domain C.
Proof.
move=>hPrime x y.
have [a <-]:=commutative_quotient_surjective hQuotient x.
have [b <-]:=commutative_quotient_surjective hQuotient y.
move=>hZero.
have hProduct:I (a*b).
  apply:(commutative_quotient_kernel hQuotient (a*b)).1;by rewrite rmorphM.
have [hA|hB]:=hPrime.2.2 a b hProduct.
- left;exact:(commutative_quotient_kernel hQuotient a).2 hA.
- right;exact:(commutative_quotient_kernel hQuotient b).2 hB.
Qed.
End Laws.
