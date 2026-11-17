(** Federer (1969), 3.4.12, p. 339: algebraic closedness
    supplies an actual root of every original nonconstant coefficient
    polynomial. Normalize only its leading coefficient and reuse the
    project's finite evaluation expression. No polynomial implementation
    or external factorization theorem is inspected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialDegreeUP
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [closed_field_original_polynomial_root]: the
    original root existence used to replace the real fibre-count
    strata in 3.4.12, p. 339. Every evaluation extending the
    original coefficients retains this root. *)
Theorem closed_field_original_polynomial_root (K:fieldType)
    (hClosed:GRing.closed_field_axiom [the pzRingType of (K:Type)])
    (B:comNzRingType) (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
    (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B) d:
  is_polynomial_degree coefficient P d ->(0<d)%N ->
  exists x:K,forall E:{rmorphism B->K},
    is_commutative_polynomial_evaluation embed variable (GRing.RMorphism.clone K K idfun _) x E ->E P=0.
Proof.
move=>hDegree hPositive.
pose a:=coefficient P d.
have hA:a!=0 by apply/eqP;exact:hDegree.1.
have [x hX]:=hClosed d (fun i=>-a^-1*coefficient P i) hPositive.
exists x=>E hE.
have hBound i (hi:(d.+1<=i)%N):coefficient P i=0:=hDegree.2 i hi.
have hValue:=@polynomial_evaluation_finite_expression K B K embed variable coefficient hP
  (GRing.RMorphism.clone K K idfun _) x E hE P d.+1 hBound.
change (E P=\sum_(i<d.+1) coefficient P i*x^+(i:nat)) in hValue.
rewrite big_ord_recr in hValue.
have hLeading:a*x^+d= -(\sum_(i<d) coefficient P i*x^+(i:nat)).
  rewrite hX mulr_sumr -sumrN;apply:eq_bigr=>i _.
  by rewrite !mulrA mulrN (mulfV hA) mulN1r mulNr.
change (E P=(\sum_(i<d) coefficient P i*x^+(i:nat))+a*x^+d) in hValue.
by rewrite hValue hLeading addrN.
Qed.
