(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP FreeVector ModuleQuotient FamilyUpdate
  TensorFamilyUP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.1.1: existence of the tensor product of V_1, …, V_m. The
    construction is used only through [tensor_family_exists]. *)
Section Construction.
Variable K : fieldType.
Variable m : nat.
Variable V : 'I_m -> lmodType K.
Local Notation A := (Choice.clone {dffun forall i, V i} _).
Local Notation F := (free_vector K A).

(** Source for [family_delta]: Federer (1969), 1.1.1, p. 9, existence proof,
    from the definition of F to the quotient F/G. In words: Take finitely
    supported functions on the Cartesian product and quotient by the
    linearity relations in every argument. Definition or construction used
    to formalise this passage. *)
Definition family_delta (x : {dffun forall i, V i}) : F := @delta K A x.

(** Source for [family_relation]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Inductive family_relation : F -> Prop :=
| frel_zero : family_relation 0
| frel_add y z : family_relation y -> family_relation z -> family_relation (y + z)
| frel_scale a y : family_relation y -> family_relation (a *: y)
| frel_component_add x i (v w : V i) :
    family_relation (family_delta (family_with x (v + w)) -
      (family_delta (family_with x v) + family_delta (family_with x w)))
| frel_component_scale x i a (v : V i) :
    family_relation (family_delta (family_with x (a *: v)) -
      a *: family_delta (family_with x v)).

(** Source for [family_subspace]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition family_subspace : subspace F :=
  @Subspace K F family_relation frel_zero frel_add frel_scale.

(** Source for [family_tensor_space]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition family_tensor_space := module_quotient family_subspace.
HB.instance Definition _ := GRing.Lmodule.copy family_tensor_space
  (module_quotient family_subspace).
(** Source for [family_tensor_inj]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition family_tensor_inj (x : {dffun forall i, V i}) : family_tensor_space :=
  quotient_projection family_subspace (family_delta x).

(** Source for [family_tensor_inj_multilinear]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_tensor_inj_multilinear : multilinear family_tensor_inj.
Proof.
move=> x i a v w; rewrite /family_tensor_inj -linearZ -linearD /=.
apply/quotient_projection_eq.
have e : family_delta (family_with x (a *: v + w)) -
    (a *: family_delta (family_with x v) + family_delta (family_with x w)) =
  (family_delta (family_with x (a *: v + w)) -
    (family_delta (family_with x (a *: v)) + family_delta (family_with x w))) +
  (family_delta (family_with x (a *: v)) - a *: family_delta (family_with x v)).
  by rewrite [in RHS]addrA [_ + family_delta (family_with x w)]addrC
    [in RHS]opprD [in RHS]addrA subrK [in LHS]opprD addrA addrAC.
rewrite e; apply: frel_add.
  exact: frel_component_add.
exact: frel_component_scale.
Qed.

Section Lift.
Variable Z : lmodType K.
Variable beta : {dffun forall i, V i} -> Z.
Hypothesis beta_multilinear : multilinear beta.

(** Source for [family_beta_free]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition family_beta_free : {linear F -> Z} := GRing.Linear.clone _ _ _ _
  (free_extend (fun x : A => beta x)) _.

(** Source for [family_beta_free_delta]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_beta_free_delta x : family_beta_free (family_delta x) = beta x.
Proof. exact: free_extend_delta. Qed.

(** Source for [family_relation_killed]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_relation_killed y : family_relation y -> family_beta_free y = 0.
Proof.
elim=> [|y' z hy ihy hz ihz|a y' hy ihy|x i v w|x i a v].
- exact: linear0.
- by rewrite linearD /= ihy ihz add0r.
- by rewrite linearZ /= ihy scaler0.
- rewrite linearB linearD /= !family_beta_free_delta.
  have e := @beta_multilinear x i 1 v w; rewrite !scale1r in e.
  by rewrite e subrr.
- rewrite linearB linearZ /= !family_beta_free_delta.
  by rewrite (GRing.scalable_linear (@beta_multilinear x i)) subrr.
Qed.

(** Source for [family_tensor_lift]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Definition or construction
    used to formalise this passage. *)
Definition family_tensor_lift : family_tensor_space -> Z :=
  quotient_lift (S := family_subspace) (f := family_beta_free)
    family_relation_killed.
HB.instance Definition _ := GRing.Linear.copy family_tensor_lift
  (quotient_lift (S := family_subspace) (f := family_beta_free)
    family_relation_killed).

(** Source for [family_tensor_liftE]: Federer (1969), 1.1.1, p. 9, existence
    proof, from the definition of F to the quotient F/G. In words: Take
    finitely supported functions on the Cartesian product and quotient by
    the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_tensor_liftE x : family_tensor_lift (family_tensor_inj x) = beta x.
Proof.
by rewrite /family_tensor_lift /family_tensor_inj quotient_liftE
  family_beta_free_delta.
Qed.

(** Source for [family_tensor_lift_unique]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma family_tensor_lift_unique (g : {linear family_tensor_space -> Z}) :
  (forall x, g (family_tensor_inj x) = beta x) ->
  forall t, g t = family_tensor_lift t.
Proof.
move=> e; apply: quotient_lift_unique => y.
apply: (free_linear_ext (linear_comp g
  (GRing.Linear.clone _ _ _ _ (quotient_projection family_subspace) _))
  family_beta_free) y.
move=> x /=.
by rewrite -/(family_delta x) -/(family_tensor_inj x) e family_beta_free_delta.
Qed.
End Lift.

(** Source for [tensor_family_exists]: Federer (1969), 1.1.1, p. 9,
    existence proof, from the definition of F to the quotient F/G. In words:
    Take finitely supported functions on the Cartesian product and quotient
    by the linearity relations in every argument. Formalises the indicated
    part of the passage under the hypotheses in the statement below. *)
Theorem tensor_family_exists : is_tensor_product_family family_tensor_inj.
Proof.
constructor; first exact: family_tensor_inj_multilinear.
move=> Z beta hb.
exists (GRing.Linear.clone _ _ _ _ (family_tensor_lift hb) _); split.
  exact: family_tensor_liftE.
exact: family_tensor_lift_unique.
Qed.
End Construction.
