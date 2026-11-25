(** Federer (1969), 4.1.25, p. 383: scalar
    evaluations of the original vector fibre sum
    agree with numerical sums of any graph-preserving
    source representative. The full original fibre
    remains the indexing set. Undefined input summands
    are excluded by the original sum's own domain law. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingForms AlternatingPairing
  PartialFunctionUP PartialFunctionPostcomposition PartialFunctionExtensionUP
  PartialFibreNumericalSum NumericalSum CurrentAreaFibreSumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_area_fibre_sum_extension_evaluations]:
    the actual numerical evaluations of the full
    vector sum in Federer 4.1.25, p. 383.
    An auxiliary extension changes no input domain
    and supplies no original value at an undefined
    source point. *)
Theorem current_area_fibre_sum_extension_evaluations (R : realType)
    (X : choiceType) n m (f : X -> R_n R n)
    (u : partial_function X (exterior_power (R_n R n) m))
    (w : X -> exterior_power (R_n R n) m) y eta :
  is_partial_function_total_extension u w ->
  @is_current_area_fibre_sum R X n m f u y eta ->
  forall a : A_m (R_n R n) R^o m,
    numerical_sum [set x | f x = y] (fun x => (pairing (w x) a)%:E) =
      Some (pairing eta a)%:E.
Proof.
move=> hW hSum a.
have hDomain (x : X) : f x = y -> partial_function_domain u x :=
  @current_area_fibre_sum_input_domain R X n m f u y eta hSum x.
have hScalar : is_partial_function_total_extension
    (@current_area_fibre_pairing_integrand R X n m u a)
    (fun x => (pairing (w x) a)%:E).
  move=> x z [v [hValue <-]].
  by rewrite (hW x v hValue).
have hScalarDomain x : f x = y -> partial_function_domain
    (@current_area_fibre_pairing_integrand R X n m u a) x.
  rewrite /current_area_fibre_pairing_integrand partial_function_postcompose_domain.
  exact: hDomain x.
exact: (@partial_fibre_numerical_sum_extension_graph R X (R_n R n) f
  (@current_area_fibre_pairing_integrand R X n m u a)
  (fun x => (pairing (w x) a)%:E) y (pairing eta a)%:E hScalar hScalarDomain).1 (hSum a).
Qed.
