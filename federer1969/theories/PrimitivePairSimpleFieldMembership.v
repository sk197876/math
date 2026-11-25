(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: a separating original pair sum
    generates both original algebraic elements.
    Use sealed polynomial carriers and their
    public laws to instantiate the proved gcd
    descent. All selected carriers remain local. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialCoefficientMapUP PolynomialCoefficientMapSealed PolynomialFieldPrincipalIdeals
  CommutativeSubringRealisationUP PolynomialLinearSplitUP FormalPolynomialDerivativeUP
  CommutativeBezoutGCDExistence PrimitivePairGCDDescent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [primitive_pair_simple_field_membership]:
    the coefficient ratio descends beta, and
    alpha=z-t beta then belongs to the same
    original polynomial image. This is the
    classical primitive-element argument invoked in
    3.4.8(8), p. 330; compare Bourbaki (1990),
    Chapter V, section 7, no. 4, Theorem 1,
    pp. V.40–41. The complete root list
    and separating slope are supplied independently. *)
Theorem primitive_pair_simple_field_membership (K L F T:fieldType)
  (phi:{rmorphism K->L}) (inclusion:{rmorphism F->L}) (scalar:{rmorphism K->F})
  (psi:{rmorphism L->T}) (hTriangle:forall c:K,inclusion (scalar c) = phi c)
  (a b:L) (t:K) (z:F) (hZ:inclusion z = a+phi t*b)
  (B O:comNzRingType) (embedK:{rmorphism K->B}) (variableK:B) (source:B->nat->K)
  (hB:is_commutative_polynomial_ring embedK variableK source)
  (embedL:{rmorphism L->O}) (variableL:O) (original:O->nat->L)
  (hO:is_commutative_polynomial_ring embedL variableL original)
  (M0:{rmorphism B->O}) (hM0:is_polynomial_coefficient_map source original phi M0)
  (f g dg:B) n (c:T) (roots:seq T)
  (hSplit:is_linear_polynomial_split embedL variableL (M0 (f*g)) n psi c roots)
  (hSeparation:forall u:T,u \in roots ->forall v:T,v \in roots ->
    psi a+psi (phi t)*psi b = u+psi (phi t)*v ->u = psi a /\v = psi b)
  (Ea Eb Ez:{rmorphism B->L})
  (hEa:is_commutative_polynomial_evaluation embedK variableK phi a Ea)
  (hEb:is_commutative_polynomial_evaluation embedK variableK phi b Eb)
  (hEz:is_commutative_polynomial_evaluation embedK variableK phi (a+phi t*b) Ez)
  (hImage:is_commutative_subring_realisation (fun y:L=>exists P:B,y = Ez P) inclusion):
  Ea f = 0 ->Eb g = 0 ->g<>0 ->
  is_formal_polynomial_derivative source g dg ->Eb dg<>0 ->
  exists PA PB:B,a = Ez PA /\b = Ez PB.
Proof.
move=>hFRoot hGRoot hGNonzero hDerivative hSimple.
pose C:=CommutativePolynomial.space F.
pose embedF:=CommutativePolynomial.embed F.
pose variableF:=CommutativePolynomial.variable F.
pose middle:=@CommutativePolynomial.coefficient F.
have hC:=CommutativePolynomial.laws F.
pose D:=CommutativePolynomial.space T.
pose embedT:=CommutativePolynomial.embed T.
pose variableT:=CommutativePolynomial.variable T.
pose target:=@CommutativePolynomial.coefficient T.
have hD:=CommutativePolynomial.laws T.
pose rho:{rmorphism F->T}:=GRing.RMorphism.clone F T (psi \o inclusion) _.
pose MF:=@PolynomialCoefficientMap.map K B F C embedK variableK source embedF variableF middle hB hC scalar.
have hMF:=@PolynomialCoefficientMap.laws K B F C embedK variableK source embedF variableF middle hB hC scalar.
pose N:=@PolynomialCoefficientMap.map F C T D embedF variableF middle embedT variableT target hC hD rho.
have hN:=@PolynomialCoefficientMap.laws F C T D embedF variableF middle embedT variableT target hC hD rho.
pose M1:=@PolynomialCoefficientMap.map L O T D embedL variableL original embedT variableT target hO hD psi.
have hM1:=@PolynomialCoefficientMap.laws L O T D embedL variableL original embedT variableT target hO hD psi.
pose coefficients:{rmorphism K->C}:=GRing.RMorphism.clone K C (embedF \o scalar) _.
pose point:=embedF z-embedF (scalar t)*variableF.
pose A:=@CommutativePolynomialEvaluation.map K B C embedK variableK source hB coefficients point.
have hA:=@CommutativePolynomialEvaluation.laws K B C embedK variableK source hB coefficients point.
have [H hGCD]:=@commutative_bezout_gcd_exists C
  (@polynomial_field_principal_ideals F C embedF variableF middle hC) (A f) (MF g).
have hBeta:=@primitive_pair_gcd_coefficient_descent K L F T phi inclusion scalar psi hTriangle
  a b t z hZ B C O D embedK variableK source hB embedF variableF middle hC
  embedL variableL original hO embedT variableT target hD MF hMF N hN M0 hM0 M1 hM1 A hA
  f g dg n c roots hSplit hSeparation Ea Eb hEa hEb hFRoot hGRoot hGNonzero hDerivative hSimple H hGCD.
have [PB hPB]:=(commutative_subring_inclusion_image hImage b).2
  (ex_intro _ (-middle H 0%N/middle H 1%N) hBeta).
exists (variableK-embedK t*PB),PB;split;last exact:hPB.
rewrite rmorphB rmorphM (polynomial_evaluation_variable hEz) (polynomial_evaluation_constants hEz) -hPB.
by rewrite addrK.
Qed.
