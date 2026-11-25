(** Federer (1969), 3.4.7, p. 325: existence and
    uniqueness of the actual degree follow from the
    independent finite coefficient laws. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialBasicLaws
  CommutativePolynomialDegreeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section Degree.
Variables A B:comNzRingType.
Variable embed:{rmorphism A->B}.
Variable variable:B.
Variable coefficient:B->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.

(** Source for [polynomial_degree_exists]: every nonzero
    polynomial has an actual leading coefficient, supporting
    degree induction in 3.4.7, p. 325. *)
Theorem polynomial_degree_exists (P:B):P<>0 ->exists d,is_polynomial_degree coefficient P d.
Proof.
move=>hNonzero.
have [M hM]:=@polynomial_coefficients_finite A B embed variable coefficient hP P.
have hBound:exists N,`[<forall i,(N<=i)%N ->coefficient P i = 0>].
  exists M;apply/asboolP;exact:hM.
have [N /asboolP hN hMinimum]:=ex_minnP hBound.
case:N hN hMinimum=>[|d] hN hMinimum.
- exfalso;apply:hNonzero;apply/(@polynomial_zero_coefficients A B embed variable coefficient hP).
  move=>i;exact:hN i (leq0n i).
- exists d;split.
  + move=>hZero.
    have hSmaller:`[<forall i,(d<=i)%N ->coefficient P i = 0>].
      apply/asboolP=>i hI;case:(eqVneq i d)=>[->|hDifferent];first exact:hZero.
      have hStrict:(d<i)%N by rewrite ltn_neqAle eq_sym hDifferent hI.
      exact:hN i hStrict.
    have hContradiction:=hMinimum d hSmaller.
    by rewrite ltnn in hContradiction.
  + move=>i hi;exact:hN i hi.
Qed.

(** Source for [polynomial_degree_unique]: the original
    highest nonzero coefficient determines a unique degree,
    supporting 3.4.7, p. 325. *)
Lemma polynomial_degree_unique (P:B) m n:
  is_polynomial_degree coefficient P m ->is_polynomial_degree coefficient P n ->m = n.
Proof.
move=>[hm hM] [hn hN];case:(ltngtP m n)=>[h|h|h];last exact:h.
- exfalso;exact:hn (hM n h).
- exfalso;exact:hm (hN m h).
Qed.
End Degree.
