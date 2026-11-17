(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: an original separating slope leaves
    just the original beta as a common
    root. Apply the complete root list and
    the original evaluation diagrams. The slope
    condition is discharged by finite exclusions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativeFactorizationUP CommutativePolynomialUP
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialCoefficientMapUP PolynomialLinearSplitUP PolynomialMappedSplitRoots
  PrimitivePairEvaluationDiagrams PrimitivePairRootValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CommonRoots.
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
Variable A:{rmorphism B->C}.
Hypothesis hA:is_commutative_polynomial_evaluation embedK variableK
  (GRing.RMorphism.clone K C (embedF \o scalar) _)
  (embedF z-embedF (scalar t)*variableF) A.
Variables f g:B.
Variable n:nat.
Variable c:T.
Variable roots:seq T.
Hypothesis hSplit:is_linear_polynomial_split embedL variableL (M0 (f*g)) n psi c roots.
Hypothesis hSeparation:forall u:T,u \in roots ->forall v:T,v \in roots ->
  psi a+kappa t*psi b = u+kappa t*v ->u = psi a /\v = psi b.

(** Source for [primitive_pair_common_root_unique]: both
    conjugates lie in the original complete
    root list. Their equal original pair sums
    force the original beta, the classical
    primitive-element step invoked in 3.4.8(8), p. 330. *)
Theorem primitive_pair_common_root_unique (r:T) (E:{rmorphism D->T}):
  is_commutative_polynomial_evaluation embedT variableT identity r E ->
  E (N (A f)) = 0 ->E (N (MF g)) = 0 ->r = psi b.
Proof.
move=>hE hFRoot hGRoot.
have hGValues:=@primitive_pair_coefficient_evaluation K L F T phi inclusion scalar psi hTriangle
  B C D embedK variableK source hB embedF variableF middle hC
  embedT variableT target hD MF hMF N hN r E hE.
have hGFactor:commutative_divides g (f*g) by exists f.
have hR:=@mapped_split_original_factor_root K L T B O embedK variableK source hB
  embedL variableL original hO phi M0 hM0 (f*g) g n psi c roots hSplit r
  (GRing.RMorphism.clone B T ((E \o N) \o MF) _) hGValues hGFactor hGRoot.
pose u:=psi (inclusion z)-kappa t*r.
pose Eu:=@CommutativePolynomialEvaluation.map K B T embedK variableK source hB kappa u.
have hEu:=@CommutativePolynomialEvaluation.laws K B T embedK variableK source hB kappa u.
have hValue:=@primitive_pair_substitution_value K L F T phi inclusion scalar psi hTriangle
  t z B C D embedK variableK source hB embedF variableF middle hC
  embedT variableT target hD N hN A hA r E Eu hE hEu f.
have hURoot:Eu f = 0 by rewrite -hValue.
have hFFactor:commutative_divides f (f*g) by exists g;rewrite mulrC.
have hU:=@mapped_split_original_factor_root K L T B O embedK variableK source hB
  embedL variableL original hO phi M0 hM0 (f*g) f n psi c roots hSplit u Eu hEu hFFactor hURoot.
have hEquality:=@primitive_pair_common_root_identity K L F T phi inclusion psi a b t z hZ r.
have hSeparated:=@hSeparation u hU r hR hEquality.
exact:hSeparated.2.
Qed.
End CommonRoots.
