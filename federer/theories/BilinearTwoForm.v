(** Federer (1969), 1.8.2, p. 39: supporting passage from the alternating
    imaginary bilinear function to an alternating two-form. The tuple
    definition is that of 1.4.1, pp. 16-17 Source context: HermitianUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp.
From Federer Require Import TensorUP Bilinear AlternatingForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section TwoForm.
Variable K : fieldType.
Variables V W : lmodType K.
Variable F : V -> V -> W.
Hypothesis hF : bilinear F.
Hypothesis hz : forall v, F v v = 0.

(** Source for [bilinear_two_evaluate]: Federer 1.8.2,
    p. 39, supporting evaluation of a two-form on its ordered pair. *)
Definition bilinear_two_evaluate (t : 2.-tuple V) := F (tnth t ord0) (tnth t ord_max).

(** Source for [bilinear_two_multilinear]: Federer 1.8.2,
    p. 39, the two tuple positions inherit the two bilinear laws. *)
Lemma bilinear_two_multilinear : m_linear bilinear_two_evaluate.
Proof.
move=> s t; case: s => [|x [|y s]]; case: t => [|z [|w t]] h;
  try by exfalso; move: h; rewrite /= ?size_cat ?addnS.
- move=> a v w; change (F (a *: v+w) z = a *: F v z + F w z).
  exact: (proj1 hF).
- move=> a v w; change (F x (a *: v+w) = a *: F x v + F x w).
  exact: (proj2 hF).
Qed.

(** Source for [bilinear_two_alternating]: Federer 1.8.2,
    p. 39, vanishing on repeated arguments is alternation in degree two. *)
Lemma bilinear_two_alternating : alternating bilinear_two_evaluate.
Proof.
move=> /tupleP [x t]; case/tupleP: t => y t; rewrite (tuple0 t).
rewrite /= !inE /= andbT negbK => /eqP hxy.
change (F x y = 0); by rewrite hxy.
Qed.

(** Source for [bilinear_two_form]: Federer 1.8.2, p. 39,
    the alternating bilinear map considered as an element of A^2(V,W). *)
Definition bilinear_two_form : A_m V W 2 :=
  @AlternatingForm K V W 2 bilinear_two_evaluate
    (asboolT (conj bilinear_two_multilinear bilinear_two_alternating)).

(** Source for [bilinear_two_formE]: Federer 1.8.2,
    p. 39, the resulting form retains the original evaluation. *)
Lemma bilinear_two_formE v w : bilinear_two_form [tuple v; w] = F v w.
Proof. by []. Qed.
End TwoForm.
