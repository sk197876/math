(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 330: if the old generator is
    polynomial in the new one, the old
    polynomial image is contained in the new
    image. Apply the existing least-subring theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativePolynomialUP CommutativePolynomialEvaluationUP
  CommutativeSubringUP PolynomialEvaluationImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [polynomial_evaluation_image_containment]:
    replacing two original generators by a
    primitive pair sum preserves all previous
    polynomial expressions, the induction underlying
    the simplicity assertion invoked in 3.4.8(8), p. 330. *)
Theorem polynomial_evaluation_image_containment (K B L:comNzRingType)
  (embed:{rmorphism K->B}) (variable:B) (coefficient:B->nat->K)
  (hP:is_commutative_polynomial_ring embed variable coefficient)
  (phi:{rmorphism K->L}) (x y:L) (Ex Ey:{rmorphism B->L}):
  is_commutative_polynomial_evaluation embed variable phi x Ex ->
  is_commutative_polynomial_evaluation embed variable phi y Ey ->
  (exists P:B,x = Ey P) ->forall P:B,exists Q:B,Ex P = Ey Q.
Proof.
move=>hEx hEy hX P.
have hOld:=@polynomial_evaluation_image_generated K B L embed variable coefficient hP phi x Ex hEx.
have hNew:=@polynomial_evaluation_image_generated K B L embed variable coefficient hP phi y Ey hEy.
have hGenerators:(fun a:L=>a = x \/exists c:K,a = phi c) `<=`
    (fun a:L=>exists Q:B,a = Ey Q).
  move=>a [->|[c ->]];first exact:hX.
  exists (embed c);exact:esym (polynomial_evaluation_constants hEy c).
exact:(generated_commutative_subring_minimal hOld
  (generated_commutative_subring_laws hNew) hGenerators (ex_intro _ P erefl)).
Qed.
