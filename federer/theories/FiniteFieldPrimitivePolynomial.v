(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: all failing real coefficient
    directions satisfy one nonzero real polynomial.
    The binary primitive-element argument supplies a
    generating direction. The existing determinant
    and scalar separation results supply the equation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals fingroup perm.
From Federer Require Import Hom GrassmannAbbreviations LinearBasis FiniteDualDimension InversionCount
  RingScalarRestriction ScalarRestriction
  RingSubmoduleUP CommutativeSubringUP CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativePolynomialEvaluationSealed FieldPolynomialMinimumExistence FiniteFieldModuleAlgebraic
  FiniteFieldPrimitiveGenerator MinimalPolynomialPowerBasis PowerFamilyGenerationCriterion
  PowerFamilyDeterminantPolynomial PolynomialNonzeroScalarComponent PolynomialPrimitiveGenerator
  PolynomialFunctions ComplexCharacteristic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_field_primitive_exceptional_polynomial]:
    the almost-everywhere simplicity assertion invoked
    in 3.4.8(8), p. 330. The power
    determinant and a separating real functional
    give a nonzero scalar polynomial containing
    every failing direction. This expands the
    printed appeal to finite separable extensions;
    all field and generator hypotheses precede
    the polynomial witness. *)
Theorem finite_field_primitive_exceptional_polynomial (R:realType) (K L:fieldType) (B:comNzRingType)
  (eta:{rmorphism R->K}) (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (phi:{rmorphism K->L}) n (x:'I_n->L):
  is_finitely_generated_ring_submodule
    (setT:set [the lmodType K of ring_restricted_space phi L^o]) ->
  is_generated_commutative_subring
    (fun y:L=>(exists i:'I_n,y = x i) \/exists a:K,y = phi a) setT ->
  exists (Q:PolynomialFunction (R_n R n) R^o) (w:R_n R n),
    Q w = 1 /\forall v:R_n R n,Q v<>0 ->
      is_generated_commutative_subring
        (fun y:L=>y = \sum_i phi (eta (v i))*x i \/exists a:K,y = phi a) setT.
Proof.
move=>hFinite hGenerated.
have [c [E0 [hE0 hOnto]]]:=@finite_field_primitive_subfield_generator R K L B eta embed variable coefficient hP phi
  n x (@pchar_num R) hFinite hGenerated.
pose z0:=\sum_i phi (eta (c i))*x i.
have hAlgebraic:=@finite_field_module_annihilating_polynomial K B L embed variable coefficient hP phi
  hFinite z0 E0 hE0.
have [H [d hH]]:=@minimal_field_polynomial_exists K B L embed variable coefficient hP E0 hAlgebraic.
pose basis:=fun i:'I_d=>(z0^+(i:nat):[the lmodType K of ring_restricted_space phi L^o]).
have hBasis:=@minimal_polynomial_power_basis K L B embed variable coefficient hP phi z0 E0 H d hE0 hH hOnto.
have hTwo:(1+1:K)!=0.
  have hReal:eta (1+1)!=0 by rewrite fmorph_eq0;exact:real_two_nonzero R.
  by rewrite rmorphD rmorph1 in hReal.
have [P hValues]:=@power_family_determinant_polynomial R K L eta phi d n basis hBasis x.
pose w:R_n R n:=[ffun i=>c i].
have hW:(\sum_i phi (eta (w i))*x i) = z0.
  apply:eq_bigr=>i _;by rewrite /w ffunE.
have hAtW:P w = 1.
  rewrite hValues hW.
  exact:(@power_family_basis_determinant_one K L phi d basis hBasis hTwo z0 (fun i=>erefl _)).
have hNonzero:P w<>0.
  rewrite hAtW;by apply/eqP;exact:oner_neq0.
have [Q [hQAt hZeros]]:=@polynomial_nonzero_scalar_component R (R_n R n)
  [the lmodType R of restricted_space eta K^o] P w hNonzero.
exists Q,w;split;first exact:hQAt.
move=>v hQ.
have hPNonzero:P v<>0 by move=>hZero;exact:hQ (hZeros v hZero).
pose z:=\sum_i phi (eta (v i))*x i.
pose E:=@CommutativePolynomialEvaluation.map K B L embed variable coefficient hP phi z.
have hE:=@CommutativePolynomialEvaluation.laws K B L embed variable coefficient hP phi z.
have hDet:(\sum_(sigma:'S_d) InversionCount.FedererPermutation.index K sigma *
    \prod_(i<d) FiniteDualDimension.dual_basis hBasis (sigma i) (z^+(i:nat)))<>0.
  rewrite -hValues;exact:hPNonzero.
have hSurjective:=@power_family_nonzero_determinant_generates K L phi d basis hBasis hTwo B embed variable z E hE hDet.
exact:(@polynomial_surjection_primitive_generator K B L embed variable coefficient hP phi z E hE).1 hSurjective.
Qed.
