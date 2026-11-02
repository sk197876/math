(** Federer (1969), 1.8.2, pp. 39-40: restriction of a
    Hermitian product to a complex subspace. More generally, an
    injective complex-linear map pulls a Hermitian product back to
    its domain, and its real imaginary two-form is the ordinary
    pullback. This supports the finite-dimensional associated-space
    argument without restricting the ambient dimension. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP ScalarRestriction ComplexScalarSealed
  HermitianUP HermitianRealImaginary HermitianRotation BilinearTwoForm
  BilinearPrecompose OrthogonalMaps AlternatingForms AlternatingDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Pullback.
Variable R : rcfType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Variables U V : lmodType C.
Variable H : V -> V -> C.
Hypothesis hH : is_hermitian_product H.
Variable f : {linear U -> V}.
Hypothesis hf : injective f.

(** Source for [hermitian_pullback]: Federer 1.8.2,
    pp. 39-40, the restricted Hermitian product, defined by the inclusion map. *)
Definition hermitian_pullback (x y : U) := H (f x) (f y).

(** Source for [hermitian_pullbackP]: Federer 1.8.2,
    pp. 39-40, supporting verification of all Hermitian laws
    after an injective complex-linear pullback. *)
Theorem hermitian_pullbackP : is_hermitian_product hermitian_pullback.
Proof.
constructor.
- exact: bilinear_linear_precompose (hermitian_real_bilinear hH)
    (restrict_linear embed f) (restrict_linear embed f).
- move=> x y; by rewrite /hermitian_pullback linearZ (hermitian_i_right hH).
- move=> x y; exact: (hermitian_conjugate_symmetric hH (f x) (f y)).
- move=> x hx; apply: (hermitian_positive hH).
  by rewrite -(linear0 f) (inj_eq hf).
Qed.

(** Source for [hermitian_pullback_orthogonal]: Federer 1.8.2,
    p. 40, inclusion preserves the real inner products. *)
Lemma hermitian_pullback_orthogonal : is_orthogonal_map
  (hermitian_real_part hermitian_pullback) (hermitian_real_part H) (restrict_linear embed f).
Proof. by move=> x y. Qed.

(** Source for [hermitian_pullback_two_form]: Federer 1.8.2,
    p. 40, the imaginary two-form of the restricted product is
    the real pullback of the ambient imaginary two-form. *)
Theorem hermitian_pullback_two_form :
  hermitian_two_form hermitian_pullbackP = A_m_dual (restrict_linear embed f) (hermitian_two_form hH).
Proof.
apply: form_ext => /tupleP [x t]; case/tupleP: t => y t; rewrite (tuple0 t).
rewrite A_m_dualE.
change (hermitian_two_form hermitian_pullbackP [tuple x; y] =
  hermitian_two_form hH [tuple f x; f y]).
by rewrite /hermitian_two_form !bilinear_two_formE.
Qed.
End Pullback.
