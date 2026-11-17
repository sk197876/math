(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: outside finitely many slopes,
    a linear combination generates both original
    elements of a finite characteristic-zero extension.
    Reuse finite-module algebraicity, minimal-polynomial
    separability, containing fields and gcd descent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeDomainUP RingScalarRestriction RingSubmoduleUP
  CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialDegree
  CommutativePolynomialDegreeBounds CommutativePolynomialProductDegree
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialCoefficientMapSealed PolynomialCoefficientMapLaws
  FiniteFieldModuleAlgebraic FieldPolynomialMinimumUP FieldPolynomialMinimumExistence
  FormalPolynomialDerivativeExistence MinimalPolynomialSeparable
  PolynomialLinearSplitExistence PrimitiveElementSlopeSeparation
  AlgebraicSimpleFieldWitness PrimitivePairSimpleFieldMembership.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_field_primitive_pair_except_finite_slopes]:
    the classical primitive-element argument invoked
    in 3.4.8(8), p. 330; compare Bourbaki,
    Algebra II (1990), Chapter V, section 7,
    no. 4, Theorem 1, pp. V.40–41.
    For the original two elements, one finite
    containing field supplies a finite excluded
    slope list. Every other original slope
    gives actual polynomial expressions for both
    elements in their original pair sum. *)
Theorem finite_field_primitive_pair_except_finite_slopes (K L:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism K->L}):
  [pchar K] =i pred0 ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  forall a b:L,exists (T:fieldType) (psi:{rmorphism L->T}) (bad:seq T),
    forall t:K,psi (phi t) \notin bad ->forall Ez:{rmorphism B->L},
      is_commutative_polynomial_evaluation embed variable phi (a+phi t*b) Ez ->
      exists PA PB:B,a = Ez PA /\b = Ez PB.
Proof.
move=>hCharacteristic hFinite a b.
pose Ea:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hP phi a.
have hEa:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hP phi a.
pose Eb:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hP phi b.
have hEb:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hP phi b.
have [f [hFNonzero hFRoot]]:=@finite_field_module_annihilating_polynomial K B L
  embed variable coefficient hP phi hFinite a Ea hEa.
have hBAlgebraic:=@finite_field_module_annihilating_polynomial K B L
  embed variable coefficient hP phi hFinite b Eb hEb.
have [g [ng hMinimal]]:=@minimal_field_polynomial_exists K B L embed variable coefficient hP Eb hBAlgebraic.
have hDegreeG:=(minimal_field_polynomial_monic hMinimal).1.
have hGNonzero:=@polynomial_degree_implies_nonzero K B embed variable coefficient hP g ng hDegreeG.
have hGRoot:=minimal_field_polynomial_vanishes hMinimal.
have [dg hDerivative]:=@formal_polynomial_derivative_exists K B embed variable coefficient hP g.
have hSimple:=@minimal_field_polynomial_derivative_nonzero K B L embed variable coefficient hP Eb
  g ng hMinimal hCharacteristic dg hDerivative.
have [nf hDegreeF]:=@polynomial_degree_exists K B embed variable coefficient hP f hFNonzero.
have hDomain:is_commutative_integral_domain K.
  move=>x y /eqP;rewrite mulf_eq0;move/orP=>[/eqP hX|/eqP hY];[by left|by right].
have hProductDegree:=@polynomial_product_degree K B embed variable coefficient hP hDomain f g nf ng hDegreeF hDegreeG.
pose O:=CommutativePolynomial.space L.
pose embedL:=CommutativePolynomial.embed L.
pose variableL:=CommutativePolynomial.variable L.
pose original:=@CommutativePolynomial.coefficient L.
have hO:=CommutativePolynomial.laws L.
pose M0:=@PolynomialCoefficientMap.map K B L O embed variable coefficient embedL variableL original hP hO phi.
have hM0:=@PolynomialCoefficientMap.laws K B L O embed variable coefficient embedL variableL original hP hO phi.
have hMappedDegree:=@polynomial_coefficient_map_degree K B L O coefficient original phi M0 (f*g)
  (nf+ng)%N hM0 (fmorph_inj phi) hProductDegree.
have [T [psi [c [roots hSplit]]]]:=@polynomial_linear_split_exists (nf+ng)%N L O
  embedL variableL original hO (M0 (f*g)) hMappedDegree.
pose kappa:{rmorphism K->T}:=GRing.RMorphism.clone K T (psi \o phi) _.
have [bad hBad]:=@primitive_pair_finite_slope_exclusions K T kappa (psi a) (psi b) roots roots.
exists T,psi,bad=>t hGood Ez hEz.
have hZAlgebraic:=@finite_field_module_annihilating_polynomial K B L embed variable coefficient hP
  phi hFinite (a+phi t*b) Ez hEz.
have [F [inclusion [scalar [z [hImage [hTriangle hZ]]]]]]:=
  @algebraic_simple_field_witness K B L embed variable coefficient hP phi (a+phi t*b) Ez hEz hZAlgebraic.
have hSeparation:=hBad t hGood.
exact:(@primitive_pair_simple_field_membership K L F T phi inclusion scalar psi hTriangle a b t z hZ
  B O embed variable coefficient hP embedL variableL original hO M0 hM0 f g dg (nf+ng)%N c roots hSplit
  hSeparation Ea Eb Ez hEa hEb hEz hImage hFRoot hGRoot hGNonzero hDerivative hSimple).
Qed.

(** Source for [finite_field_primitive_pair]: an
    original characteristic-zero slope avoids the
    finite excluded list, the existence part
    of the cited primitive-element theorem. *)
Theorem finite_field_primitive_pair (K L:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism K->L}):
  [pchar K] =i pred0 ->
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  forall a b:L,exists (t:K) (Ez:{rmorphism B->L}) (PA PB:B),
    is_commutative_polynomial_evaluation embed variable phi (a+phi t*b) Ez /\
    a = Ez PA /\b = Ez PB.
Proof.
move=>hCharacteristic hFinite a b.
have [T [psi [bad hGood]]]:=@finite_field_primitive_pair_except_finite_slopes K L B
  embed variable coefficient hP phi hCharacteristic hFinite a b.
pose kappa:{rmorphism K->T}:=GRing.RMorphism.clone K T (psi \o phi) _.
have [t hT]:=@characteristic_zero_scalar_avoids_list K T kappa bad hCharacteristic.
pose Ez:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hP phi (a+phi t*b).
have hEz:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hP phi (a+phi t*b).
have [PA [PB hValues]]:=hGood t hT Ez hEz.
exists t,Ez,PA,PB;by split.
Qed.
