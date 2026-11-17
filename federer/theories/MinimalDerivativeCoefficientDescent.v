(** Federer (1969), 3.4.8(10), p. 330:
    the original polynomial derivative does
    not vanish in the quotient. Connect
    coefficient extension with the already proved
    characteristic-zero minimal-polynomial separability theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  PolynomialCoefficientMapUP PolynomialEvaluationCoefficientExtension FieldPolynomialMinimumUP
  FormalPolynomialDerivativeUP FormalPolynomialDerivativeExtension MinimalPolynomialSeparable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [original_minimal_derivative_nonzero]:
    the original derivative remains nonzero
    at the original next coordinate,
    3.4.8(10), p. 330. Existing coefficient
    differentiation and evaluation equations transfer
    the existing minimal-polynomial separability result. *)
Theorem original_minimal_derivative_nonzero (A B:comNzRingType) (K:fieldType) (D:comNzRingType) (L:fieldType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedK:{rmorphism K->D}) (variableK:D) (target:D->nat->K)
  (hA:is_commutative_polynomial_ring embedA variableA source)
  (hK:is_commutative_polynomial_ring embedK variableK target)
  (eta:{rmorphism A->K}) (map:{rmorphism B->D})
  (hMap:is_polynomial_coefficient_map source target eta map)
  (chi:{rmorphism A->L}) (phi:{rmorphism K->L}) (x:L)
  (E:{rmorphism B->L}) (F:{rmorphism D->L}) (W:B) k:
  (forall a:A,chi a = phi (eta a)) ->
  is_commutative_polynomial_evaluation embedA variableA chi x E ->
  is_commutative_polynomial_evaluation embedK variableK phi x F ->
  is_minimal_field_polynomial target F (map W) k ->[pchar K] =i pred0 ->
  forall derivative:B,is_formal_polynomial_derivative source W derivative ->E derivative<>0.
Proof.
move=>hTriangle hE hF hW hCharacteristic derivative hDerivative hZero.
have hMapped:=@formal_polynomial_derivative_coefficient_extension A K B D source target eta map
  hMap W derivative hDerivative.
have hNonzero:=@minimal_field_polynomial_derivative_nonzero K D L embedK variableK target hK F
  (map W) k hW hCharacteristic (map derivative) hMapped.
apply:hNonzero.
rewrite -(@polynomial_evaluation_coefficient_extension A B K D L embedA variableA source
  embedK variableK target hA hK eta map hMap chi phi x E F hTriangle hE hF derivative).
exact:hZero.
Qed.
