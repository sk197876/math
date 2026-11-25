(** Federer (1969), 3.4.12, p. 339: the original dual
    complex coordinates of an orthonormal basis equal its Hermitian
    coordinate functionals. Use the independent Hermitian laws and
    the existing basis uniqueness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom TensorUP Bilinear ScalarRestriction ComplexScalarSealed ComplexScalarLaws
  HermitianUP HermitianRealImaginary HermitianComplexLinearity OrthonormalFamilies LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Coordinates.
Variable R:realFieldType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family H e.
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.

(** Source for [hermitian_basis_coordinate]: each original
    complex coordinate is exactly H(e_i,x), with the printed
    second-slot linearity convention, 3.4.12, p. 339. *)
Lemma hermitian_basis_coordinate (i:'I_n) x:H (e i) x=omega i x.
Proof.
have hLinear:linear (fun x:X=>(H (e i) x:(ComplexScalars.C R)^o)).
  move=>c u v;rewrite (bilDr (hermitian_real_bilinear hH)) (hermitian_scale_right hH).
  by [].
pose F:=@HomMap (ComplexScalars.C R) X (ComplexScalars.C R)^o
  (fun x=>H (e i) x) (introT (asboolP _) hLinear).
have hEqual:forall x,F x=omega i x.
  apply:(@basis_linear_ext (ComplexScalars.C R) (Choice.clone 'I_n _) X e he
    (ComplexScalars.C R)^o (hom_as_linear F) (hom_as_linear (omega i)))=>j.
  rewrite !hom_as_linearE /F /= hON hDual;by [].
exact:hEqual.
Qed.

(** Source for [hermitian_orthogonal_coordinate_zero]: being
    Hermitian perpendicular to an original basis vector makes its
    dual coordinate zero, 3.4.12, p. 339. *)
Lemma hermitian_orthogonal_coordinate_zero (i:'I_n) x:
  H x (e i)=0 ->omega i x=0.
Proof.
move=>hZero;rewrite -hermitian_basis_coordinate (hermitian_conjugate_symmetric hH) hZero.
by rewrite -(rmorph0 (ComplexScalars.embed R)) conjugate_real.
Qed.
End Coordinates.
