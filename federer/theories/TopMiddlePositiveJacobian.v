(** Federer (1969), 3.2.22(1), pp. 258–259:
    a positive mu-Jacobian through a mu-dimensional
    target chart forces the coordinate differential onto
    and preserves the exact differential image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanLinearJacobian
  TopMiddleJacobianComposition CoareaLinearDuality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [top_middle_positive_jacobian_image]:
    the positive-rank image alternative in Federer 3.2.22,
    p. 259. The exact top-middle product forces
    positive Jacobians for both factors. The coordinate
    map is onto R^mu and the target chart differential
    is injective, so the composite image is exactly
    the target differential image. Degree zero is included. *)
Lemma top_middle_positive_jacobian_image (R:realType) m mu n
    (L:Hom (R_n R m) (R_n R mu)) (D:Hom (R_n R mu) (R_n R n)):
  0<euclidean_linear_jacobian mu (hom_comp D L) ->
  (forall y,exists x,L x=y) /\ injective D /\ range (hom_comp D L)=range D.
Proof.
move=>hPositive.
have hProduct:0<euclidean_linear_jacobian mu D*euclidean_linear_jacobian mu L.
  by rewrite -euclidean_top_middle_jacobian_compose.
have hDPos:0<euclidean_linear_jacobian mu D.
  have [hp|hp]:=ltP 0 (euclidean_linear_jacobian mu D); first by [].
  have hZero:euclidean_linear_jacobian mu D=0.
    by apply/eqP; rewrite eq_le hp (euclidean_linear_jacobian_nonnegative mu D).
  by rewrite hZero mul0r ltxx in hProduct.
have hLPos:0<euclidean_linear_jacobian mu L.
  have [hp|hp]:=ltP 0 (euclidean_linear_jacobian mu L); first by [].
  have hZero:euclidean_linear_jacobian mu L=0.
    by apply/eqP; rewrite eq_le hp (euclidean_linear_jacobian_nonnegative mu L).
  by rewrite hZero mulr0 ltxx in hProduct.
have hSurj:forall y,exists x,L x=y:=(euclidean_target_jacobian_positive_iff_surjective L).1 hLPos.
split; first exact hSurj; split; first exact:(euclidean_linear_jacobian_top_positive D).1 hDPos.
apply/seteqP; split=>z.
- move=>[x _ hx]; exists (L x); first exact:Logic.I; exact hx.
- move=>[y _ hy]; have [x hx]:=hSurj y; exists x; first exact:Logic.I.
  by rewrite hom_compE hx.
Qed.
