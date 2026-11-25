(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: the original linear gcd descends
    beta to the simple coefficient field.
    Apply the proved common-root, simplicity,
    linear-gcd and coefficient-descent results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed PolynomialCoefficientMapUP PolynomialMappedEvaluation
  PolynomialScalarComposition PolynomialLinearSplitUP FormalPolynomialDerivativeUP
  CommutativeBezoutGCDUP CommutativeBezoutGCDLaws PolynomialUniqueSimpleGCD
  PolynomialCoefficientDegreeReflection PolynomialLinearRootDescent
  PrimitivePairCoefficientSquare PrimitivePairRootValues PrimitivePairCommonRoots.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Descent.
Variables K L F T:fieldType.
Variable phi:{rmorphism K->L}.
Variable inclusion:{rmorphism F->L}.
Variable scalar:{rmorphism K->F}.
Variable psi:{rmorphism L->T}.
Hypothesis hTriangle:forall a:K,inclusion (scalar a) = phi a.
Variables a b:L.
Variable t:K.
Variable z:F.
Hypothesis hZ:inclusion z = a+phi t*b.
Local Notation rho:=(GRing.RMorphism.clone F T (psi \o inclusion) _).
Local Notation kappa:=(GRing.RMorphism.clone K T (psi \o phi) _).
Local Notation identity:=(GRing.RMorphism.clone T T idfun _).
Variables B C O D:comNzRingType.
Variable embedK:{rmorphism K->B}.
Variable variableK:B.
Variable source:B->nat->K.
Hypothesis hB:is_commutative_polynomial_ring embedK variableK source.
Variable embedF:{rmorphism F->C}.
Variable variableF:C.
Variable middle:C->nat->F.
Hypothesis hC:is_commutative_polynomial_ring embedF variableF middle.
Variable embedL:{rmorphism L->O}.
Variable variableL:O.
Variable original:O->nat->L.
Hypothesis hO:is_commutative_polynomial_ring embedL variableL original.
Variable embedT:{rmorphism T->D}.
Variable variableT:D.
Variable target:D->nat->T.
Hypothesis hD:is_commutative_polynomial_ring embedT variableT target.
Variable MF:{rmorphism B->C}.
Hypothesis hMF:is_polynomial_coefficient_map source middle scalar MF.
Variable N:{rmorphism C->D}.
Hypothesis hN:is_polynomial_coefficient_map middle target rho N.
Variable M0:{rmorphism B->O}.
Hypothesis hM0:is_polynomial_coefficient_map source original phi M0.
Variable M1:{rmorphism O->D}.
Hypothesis hM1:is_polynomial_coefficient_map original target psi M1.
Variable A:{rmorphism B->C}.
Hypothesis hA:is_commutative_polynomial_evaluation embedK variableK
  (GRing.RMorphism.clone K C (embedF \o scalar) _)
  (embedF z-embedF (scalar t)*variableF) A.
Variables f g dg:B.
Variable n:nat.
Variable c:T.
Variable roots:seq T.
Hypothesis hSplit:is_linear_polynomial_split embedL variableL (M0 (f*g)) n psi c roots.
Hypothesis hSeparation:forall u:T,u \in roots ->forall v:T,v \in roots ->
  psi a+kappa t*psi b = u+kappa t*v ->u = psi a /\v = psi b.
Variables Ea Eb:{rmorphism B->L}.
Hypothesis hEa:is_commutative_polynomial_evaluation embedK variableK phi a Ea.
Hypothesis hEb:is_commutative_polynomial_evaluation embedK variableK phi b Eb.
Hypothesis hFRoot:Ea f = 0.
Hypothesis hGRoot:Eb g = 0.
Hypothesis hGNonzero:g<>0.
Hypothesis hDerivative:is_formal_polynomial_derivative source g dg.
Hypothesis hSimple:Eb dg<>0.

(** Source for [primitive_pair_gcd_coefficient_descent]:
    the gcd is linear over the simple
    field, and its coefficient ratio recovers
    the original beta. This is the classical
    primitive-element argument invoked in 3.4.8(8),
    p. 330; compare Bourbaki, Algebra II (1990),
    Chapter V, section 7, no. 4, Theorem 1,
    pp. V.40–41. All root and simplicity
    premises concern the original polynomials. *)
Theorem primitive_pair_gcd_coefficient_descent (H:C):
  is_commutative_bezout_gcd (A f) (MF g) H ->
  inclusion (-middle H 0%N/middle H 1%N) = b.
Proof.
move=>hGCD.
pose Et:=@CommutativePolynomialEvaluation.map T D T embedT variableT target hD identity (psi b).
have hEt:=@CommutativePolynomialEvaluation.laws T D T embedT variableT target hD identity (psi b).
have hGValues:=@primitive_pair_coefficient_original_value K L F T phi inclusion scalar psi hTriangle
  b B C D embedK variableK source hB embedF variableF middle hC
  embedT variableT target hD MF hMF N hN Eb Et hEb hEt.
have hFValues:=@primitive_pair_substitution_original_value K L F T phi inclusion scalar psi hTriangle
  a b t z hZ B C D embedK variableK source hB embedF variableF middle hC
  embedT variableT target hD N hN A hA Ea Et hEa hEt.
have hTargetF:Et (N (A f)) = 0 by rewrite hFValues hFRoot rmorph0.
have hTargetG:Et (N (MF g)) = 0 by rewrite hGValues hGRoot rmorph0.
have hTargetSimple:Et (N (MF dg))<>0.
  rewrite hGValues;move=>hZero;apply:hSimple;apply:(fmorph_inj psi);by rewrite hZero rmorph0.
have hTargetDerivative:=@primitive_pair_second_derivative_extension K L F T inclusion scalar psi
  B C D source middle target MF hMF N hN g dg hDerivative.
have hNonzero:=@primitive_pair_second_nonzero K L F T inclusion scalar psi B C D embedK variableK source hB
  embedF variableF middle hC target MF hMF N hN g hGNonzero.
have hDivides:=@primitive_pair_second_divides_split_product K L F T phi inclusion scalar psi hTriangle
  B C O D source middle original embedT variableT target hD MF hMF N hN M0 hM0 M1 hM1 f g.
have hTargetGCD:=commutative_bezout_gcd_ring_map N hGCD.
have hUnique (r:T) (E:{rmorphism D->T})
    (hConstants:forall x:T,E (embedT x) = x) (hVariable:E variableT = r)
    (hFR:E (N (A f)) = 0) (hGR:E (N (MF g)) = 0):r = psi b.
  have hE:is_commutative_polynomial_evaluation embedT variableT identity r E.
    constructor;[exact:hConstants|exact:hVariable].
  exact:(@primitive_pair_common_root_unique K L F T phi inclusion scalar psi hTriangle
    a b t z hZ B C O D embedK variableK source hB embedF variableF middle hC
    embedL variableL original hO embedT variableT target hD MF hMF N hN M0 hM0 A hA
    f g n c roots hSplit hSeparation r E hE hFR hGR).
have hLinear:=@polynomial_unique_simple_common_root_gcd_linear L O embedL variableL (M0 (f*g))
  original n hO T psi c roots hSplit D embedT variableT target hD M1 hM1
  (N (A f)) (N (MF g)) (N H) (N (MF dg)) (psi b) Et
  (polynomial_evaluation_constants hEt) (polynomial_evaluation_variable hEt)
  hTargetGCD hNonzero hDivides hTargetDerivative hTargetSimple hTargetF hTargetG hUnique.
have hOriginalLinear:=@polynomial_coefficient_map_degree_reflect F T C D middle target rho N hN
  (fmorph_inj rho) H 1%N hLinear.
pose EH:{rmorphism C->T}:=GRing.RMorphism.clone C T (Et \o N) _.
have hComposite:=@polynomial_evaluation_through_coefficient_map F C T D T embedF variableF middle
  embedT variableT target hC hD rho N hN identity (psi b) Et hEt.
have hEH:is_commutative_polynomial_evaluation embedF variableF rho (psi b) EH.
  apply:(polynomial_evaluation_change_parameters hComposite);by [].
have hHRoot:EH H = 0.
  exact:(commutative_bezout_gcd_kernel Et hTargetGCD).2 (conj hTargetF hTargetG).
have hDescent:=@polynomial_linear_root_coefficient_descent F C T embedF variableF middle hC
  rho (psi b) EH H hEH hOriginalLinear hHRoot.
apply:(fmorph_inj psi);exact:esym hDescent.
Qed.
End Descent.
