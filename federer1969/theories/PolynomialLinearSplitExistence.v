(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: repeated actual root adjunction
    supplies all linear factors. Reuse the project's
    prime factorisation, quotients, fraction fields,
    coefficient maps, division and evaluation uniqueness.
    Compare Bourbaki, Algebra II (1990), Chapter V,
    section 4, no. 2, Proposition 4, pp. V.21–22.
    Here finite degree induction suffices for one polynomial. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialSealed
  CommutativePolynomialDegreeUP CommutativePolynomialDegreeBounds
  CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  PolynomialCoefficientMapUP PolynomialCoefficientMapSealed PolynomialCoefficientMapLaws
  PolynomialEvaluationCoefficientExtension PolynomialRootExtension PolynomialLinearRootFactor
  PolynomialLinearSplitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [polynomial_linear_split_exists]: the
    containing-field consequence of Bourbaki (1990),
    Chapter V, section 4, no. 2,
    Proposition 4, pp. V.21–22; supporting
    the finite-separable argument in 3.4.8(8),
    pp. 329–330. Each degree step applies
    the existing prime-factor and division proofs. *)
Theorem polynomial_linear_split_exists:forall d (K:fieldType) (B:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient) (P:B),
  is_polynomial_degree coefficient P d ->
  exists (L:fieldType) (phi:{rmorphism K->L}) (c:L) (roots:seq L),
    is_linear_polynomial_split embed variable P d phi c roots.
Proof.
elim=>[|d ih] K B embed variable coefficient hP P hDegree.
- pose identity:{rmorphism K->K}:=GRing.RMorphism.clone K K idfun _.
  exists K,identity,(coefficient P 0%N),[::];constructor.
  + exact:hDegree.1.
  + by [].
  + move=>Z psi chi z E hChi hE.
    rewrite {1}(@polynomial_degree_zero_constant K B embed variable coefficient hP P hDegree)
      (polynomial_evaluation_constants hE) big_nil mulr1.
    exact:hChi (coefficient P 0%N).
- have [L1 [phi1 [x1 [E1 [hE1 hRoot]]]]]:=
    @polynomial_root_extension_exists K B embed variable coefficient hP P d.+1 hDegree (ltn0Sn d).
  pose D:=CommutativePolynomial.space L1.
  pose embedD:=CommutativePolynomial.embed L1.
  pose variableD:=CommutativePolynomial.variable L1.
  pose coefficientD:=@CommutativePolynomial.coefficient L1.
  have hD:=CommutativePolynomial.laws L1.
  pose M:=@PolynomialCoefficientMap.map K B L1 D embed variable coefficient
    embedD variableD coefficientD hP hD phi1.
  have hM:=@PolynomialCoefficientMap.laws K B L1 D embed variable coefficient
    embedD variableD coefficientD hP hD phi1.
  have hDegreeM:=@polynomial_coefficient_map_degree K B L1 D coefficient coefficientD phi1
    M P d.+1 hM (fmorph_inj phi1) hDegree.
  pose identity:{rmorphism L1->L1}:=GRing.RMorphism.clone L1 L1 idfun _.
  pose F:=@CommutativePolynomialEvaluation.map L1 D L1 embedD variableD coefficientD hD identity x1.
  have hF:=@CommutativePolynomialEvaluation.laws L1 D L1 embedD variableD coefficientD hD identity x1.
  have hCompare:=@polynomial_evaluation_coefficient_extension K B L1 D L1 embed variable coefficient
    embedD variableD coefficientD hP hD phi1 M hM phi1 identity x1 E1 F
    (fun a=>erefl (phi1 a)) hE1 hF P.
  have hMappedRoot:F (M P) = 0 by rewrite -hCompare.
  have [Q hFactor]:=@polynomial_linear_factor_from_root L1 D embedD variableD coefficientD hD
    x1 F (polynomial_evaluation_constants hF) (polynomial_evaluation_variable hF) (M P) hMappedRoot.
  have hDegreeQ:=@polynomial_linear_root_factor_quotient_degree L1 D embedD variableD coefficientD hD
    x1 (M P) Q d hDegreeM hFactor.
  have [L2 [phi2 [c [roots hSplit]]]]:=ih L1 D embedD variableD coefficientD hD Q hDegreeQ.
  pose phi:{rmorphism K->L2}:=GRing.RMorphism.clone K L2 (phi2 \o phi1) _.
  exists L2,phi,c,(phi2 x1::roots);constructor.
  + exact:linear_split_scalar_nonzero hSplit.
  + by rewrite /= (linear_split_root_count hSplit).
  + move=>Z psi chi z E hChi hE.
    pose sigma:{rmorphism L1->Z}:=GRing.RMorphism.clone L1 Z (psi \o phi2) _.
    pose FZ:=@CommutativePolynomialEvaluation.map L1 D Z embedD variableD coefficientD hD sigma z.
    have hFZ:=@CommutativePolynomialEvaluation.laws L1 D Z embedD variableD coefficientD hD sigma z.
    have hChiSigma a:chi a = sigma (phi1 a):=hChi a.
    have hConvert:=@polynomial_evaluation_coefficient_extension K B L1 D Z embed variable coefficient
      embedD variableD coefficientD hP hD phi1 M hM chi sigma z E FZ hChiSigma hE hFZ P.
    have hLower:=@linear_split_evaluation L1 D embedD variableD Q d L2 phi2 c roots hSplit
      Z psi sigma z FZ (fun a=>erefl (sigma a)) hFZ.
    rewrite hConvert hFactor rmorphM rmorphB (polynomial_evaluation_variable hFZ)
      (polynomial_evaluation_constants hFZ) hLower big_cons.
    change ((psi c*\prod_(r<-roots) (z-psi r))*(z-psi (phi2 x1)) =
      psi c*((z-psi (phi2 x1))*\prod_(r<-roots) (z-psi r))).
    by rewrite mulrAC -mulrA.
Qed.
