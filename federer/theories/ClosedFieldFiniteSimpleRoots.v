(** Federer (1969), 3.4.12, p. 339: the original simple
    degree-k polynomial has exactly k roots over an algebraically
    closed field. Connect its finite original coefficient vector to
    the existing abstract polynomial and simple-root counting theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialSealed CommutativePolynomialFiniteSums
  CommutativePolynomialDegreeUP CommutativePolynomialEvaluationUP CommutativePolynomialEvaluationSealed
  CommutativePolynomialEvaluationLaws FormalPolynomialDerivativeUP FormalPolynomialDerivativeSealed
  FormalDerivativeEvaluationExpression ClosedFieldSimpleRootCount.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
(** Source for [closed_field_finite_simple_roots]: Y_nu is
    empty unless nu=k in the complex version of 3.4.8(10),
    as stated in 3.4.12, p. 339. The original finite
    coefficients and their actual formal derivative remain. The
    proof applies the existing abstract polynomial result directly. *)
Theorem closed_field_finite_simple_roots (K:fieldType)
    (hClosed:GRing.closed_field_axiom [the pzRingType of (K:Type)]) k (b:'I_k.+1->K):
  b ord_max = 1 ->
  (forall z:K,(\sum_(i<k.+1) b i*z^+(i:nat))=0 ->
    (\sum_(i<k.+1) (i:nat)%:R*b i*z^+(i:nat).-1)<>0) ->
  exists roots:seq K,uniq roots /\size roots=k /\
    forall z:K,(\sum_(i<k.+1) b i*z^+(i:nat))=0 <->z \in roots.
Proof.
move=>hLeading hSimple.
pose B:=CommutativePolynomial.space [the comNzRingType of (K:Type)].
pose embed:=@CommutativePolynomial.embed [the comNzRingType of (K:Type)].
pose variable:=@CommutativePolynomial.variable [the comNzRingType of (K:Type)].
pose coefficient:=@CommutativePolynomial.coefficient [the comNzRingType of (K:Type)].
pose hP:=@CommutativePolynomial.laws [the comNzRingType of (K:Type)].
pose s:=map b (enum 'I_k.+1).
pose c:=fun i:nat=>nth 0 s i.
have hC i:(k.+1<=i)%N ->c i=0.
  move=>hI;apply:nth_default;by rewrite /s size_map size_enum_ord.
have hAt (i:'I_k.+1):c i=b i.
  by rewrite /c /s (nth_map i) ?size_enum_ord ?ltn_ord // nth_ord_enum.
have [P hCoefficients]:=@polynomial_interpolation_exists [the comNzRingType of (K:Type)]
  B embed variable coefficient hP c (ex_intro _ k.+1 hC).
have hSupport i:(k.+1<=i)%N ->coefficient P i=0 by rewrite hCoefficients;exact:hC.
have hDegree:is_polynomial_degree coefficient P k.
  split.
  - rewrite hCoefficients -[k]/(ord_max:nat) hAt hLeading.
    move=>hZero;have hNot:(1:K)!=0 by rewrite oner_eq0.
    by rewrite hZero eqxx in hNot.
  - move=>i hI;exact:hSupport i hI.
pose identity:=GRing.RMorphism.clone K K idfun _.
pose E:=fun z:K=>@CommutativePolynomialEvaluation.map K B K embed variable coefficient hP identity z.
have hE z:=@CommutativePolynomialEvaluation.laws K B K embed variable coefficient hP identity z.
pose DP:=@FormalPolynomialDerivative.value K B embed variable coefficient hP P.
have hDP:=@FormalPolynomialDerivative.laws K B embed variable coefficient hP P.
have hValue z:E z P=\sum_(i<k.+1) b i*z^+(i:nat).
  rewrite (@polynomial_evaluation_finite_expression K B K embed variable coefficient hP
    identity z (E z) (hE z) P k.+1 hSupport).
  apply:eq_bigr=>i _;by rewrite hCoefficients hAt.
have hDerivativeValue z:E z DP=\sum_(i<k.+1) (i:nat)%:R*b i*z^+(i:nat).-1.
  rewrite (@formal_derivative_evaluation_finite_expression K B K embed variable coefficient hP
    identity z (E z) P DP k.+1 (hE z) hDP hSupport).
  apply:eq_bigr=>i _;by rewrite hCoefficients hAt.
have hSimpleOriginal z:E z P=0 ->E z DP<>0.
  rewrite hValue hDerivativeValue;exact:hSimple.
have [roots [hUnique [hCount hRoots]]]:=@closed_field_original_simple_root_count K hClosed
  B embed variable coefficient hP k P DP hDegree hDP hSimpleOriginal.
exists roots;split;first exact:hUnique.
split;first exact:hCount.
move=>z;by rewrite -(hValue z);exact:hRoots z.
Qed.
