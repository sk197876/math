(** Federer (1969), 1.9.1, p. 41: each symmetric power is the tensor power
    modulo its intersection with the commutator ideal. Private verification
    of the component-quotient display. The construction is valid over any
    field and in every degree. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg generic_quotient.
From Federer Require Import TensorUP ModuleQuotient Bilinear AlgebraUP
  GradedAlgebra GradedComponents TensorAlgebra TensorGrading
  AlgebraQuotient SymmetricIdeal SymmetricQuotient SymmetricQuotientGrading.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section PowerQuotient.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Local Notation T := (tensor_algebra_space V).
Local Notation E := (symmetric_space V).
Local Notation Tn := (graded_component (tensor_grading V) n).
Local Notation En := (symmetric_power V n).
Local Notation pi := (symmetric_projection V).

(** Source for [symmetric_power_rel]: Federer 1.9.1, p. 41,
    component-quotient display. Supporting construction for this passage, in
    words: The intersection of the commutator ideal with the degree-n tensor
    power. *)
Definition symmetric_power_rel (x : Tn) := commutator_ideal V (component_val x).

(** Source for [symmetric_power_rel0]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The component relation contains zero. *)
Lemma symmetric_power_rel0 : symmetric_power_rel 0.
Proof. rewrite /symmetric_power_rel linear0; exact: subspace_zero. Qed.

(** Source for [symmetric_power_relD]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The component relation is closed under addition. *)
Lemma symmetric_power_relD x y :
  symmetric_power_rel x -> symmetric_power_rel y -> symmetric_power_rel (x + y).
Proof. by move=> hx hy; rewrite /symmetric_power_rel linearD; exact: subspace_add hx hy. Qed.

(** Source for [symmetric_power_relZ]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The component relation is closed under scalar multiplication. *)
Lemma symmetric_power_relZ a x : symmetric_power_rel x -> symmetric_power_rel (a *: x).
Proof. by move=> hx; rewrite /symmetric_power_rel linearZ; exact: subspace_scale hx. Qed.

(** Source for [symmetric_power_subspace]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The component relation packaged as the subspace by which the tensor
    power is divided. *)
Definition symmetric_power_subspace : subspace Tn :=
  @Subspace K Tn symmetric_power_rel symmetric_power_rel0
    symmetric_power_relD symmetric_power_relZ.
Local Notation Qn := (module_quotient symmetric_power_subspace).
Local Notation pin := (quotient_projection symmetric_power_subspace).

(** Source for [symmetric_power_projection]: Federer 1.9.1, p. 41,
    component- quotient display. Supporting construction for this passage,
    in words: The restriction of tensor projection to the degree-n
    components. *)
Definition symmetric_power_projection : {linear Tn -> En} :=
  GRing.Linear.clone _ _ _ _ (component_map (n := n) (@symmetric_projection_graded K V)) _.

(** Source for [symmetric_power_projectionE]: Federer 1.9.1, p. 41,
    component- quotient display. Supporting construction for this passage,
    in words: The component projection agrees with the full tensor
    projection on representatives. *)
Lemma symmetric_power_projectionE x :
  component_val (symmetric_power_projection x) = pi (component_val x).
Proof. by []. Qed.

(** Source for [symmetric_power_projection_killed]: Federer 1.9.1, p. 41,
    component-quotient display. Supporting construction for this passage, in
    words: The component projection vanishes on the component relation. *)
Lemma symmetric_power_projection_killed x :
  symmetric_power_subspace x -> symmetric_power_projection x = 0.
Proof.
move=> hx; apply/val_inj.
change (pi (component_val x) = component_val (0 : En)).
rewrite linear0; apply/ideal_projection_zero; exact: hx.
Qed.

(** Source for [symmetric_power_quotient]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The induced linear map from the component quotient to the quotient
    algebra component. *)
Definition symmetric_power_quotient : {linear Qn -> En} := GRing.Linear.clone _ _ _ _
  (quotient_lift (f := symmetric_power_projection) symmetric_power_projection_killed) _.

(** Source for [symmetric_power_quotientE]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The induced component-quotient map agrees with projection on
    representatives. *)
Lemma symmetric_power_quotientE x :
  symmetric_power_quotient (pin x) = symmetric_power_projection x.
Proof. exact: quotient_liftE. Qed.

(** Source for [symmetric_power_representative]: Federer 1.9.1, p. 41,
    component-quotient display. Supporting construction for this passage, in
    words: A tensor is sent to the quotient class of its degree-n component. *)
Definition symmetric_power_representative : {linear T -> Qn} :=
  linear_comp (GRing.Linear.clone _ _ _ _ pin _)
    (GRing.Linear.clone _ _ _ _ (component (tensor_grading V) n) _).

(** Source for [symmetric_power_representative_killed]: Federer 1.9.1, p.
    41, component-quotient display. Supporting construction for this
    passage, in words: The representative map kills the commutator ideal by
    homogeneity. *)
Lemma symmetric_power_representative_killed x :
  commutator_ideal V x -> symmetric_power_representative x = 0.
Proof.
move=> hx; rewrite /symmetric_power_representative /= -(linear0 pin).
apply/quotient_projection_eq; rewrite subr0.
change (commutator_ideal V (component_val (component (tensor_grading V) n x))).
rewrite componentE; exact: commutator_ideal_homogeneous hx.
Qed.

(** Source for [symmetric_power_inverse_aux]: Federer 1.9.1, p. 41,
    component- quotient display. Supporting construction for this passage,
    in words: The representative map descends to a map from the whole
    quotient algebra. *)
Definition symmetric_power_inverse_aux : {linear E -> Qn} :=
  GRing.Linear.clone _ _ _ _
    (quotient_lift (f := symmetric_power_representative)
      symmetric_power_representative_killed) _.

(** Source for [symmetric_power_inverse_auxE]: Federer 1.9.1, p. 41,
    component-quotient display. Supporting construction for this passage, in
    words: Evaluation of the descended representative map on a tensor
    quotient class. *)
Lemma symmetric_power_inverse_auxE x :
  symmetric_power_inverse_aux (pi x) = pin (component (tensor_grading V) n x).
Proof. exact: quotient_liftE. Qed.

(** Source for [symmetric_power_inverse]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The inverse component-quotient map, restricted to the degree-n
    component. *)
Definition symmetric_power_inverse : {linear En -> Qn} :=
  linear_comp symmetric_power_inverse_aux
    (GRing.Linear.clone _ _ _ _ (@component_val K E (symmetric_grading V) n) _).

(** Source for [symmetric_power_quotientK]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    Projecting a component quotient class and then applying the inverse
    recovers that class. *)
Lemma symmetric_power_quotientK : cancel symmetric_power_quotient symmetric_power_inverse.
Proof.
move=> x; rewrite -[x]quotient_projection_surjective symmetric_power_quotientE.
change (symmetric_power_inverse_aux (pi (component_val (repr x))) = pin (repr x)).
by rewrite symmetric_power_inverse_auxE componentK.
Qed.

(** Source for [symmetric_power_inverse_degree]: Federer 1.9.1, p. 41,
    component-quotient display. Supporting construction for this passage, in
    words: The composite on the whole algebra is the degree-n projection. *)
Lemma symmetric_power_inverse_degree y :
  component_val (symmetric_power_quotient (symmetric_power_inverse_aux y)) =
  symmetric_degree n y.
Proof.
rewrite -[y]quotient_projection_surjective.
change (component_val (symmetric_power_quotient
  (symmetric_power_inverse_aux (pi (repr y)))) = symmetric_degree n (pi (repr y))).
rewrite symmetric_power_inverse_auxE symmetric_power_quotientE
  symmetric_power_projectionE componentE.
exact: esym (symmetric_degree_projection n (repr y)).
Qed.

(** Source for [symmetric_power_inverseK]: Federer 1.9.1, p. 41, component-
    quotient display. Supporting construction for this passage, in words:
    The inverse followed by projection fixes every degree-n element. *)
Lemma symmetric_power_inverseK : cancel symmetric_power_inverse symmetric_power_quotient.
Proof.
move=> x; apply/val_inj.
change (component_val (symmetric_power_quotient
  (symmetric_power_inverse_aux (component_val x))) = component_val x).
rewrite symmetric_power_inverse_degree.
exact: component_homogeneous.
Qed.

(** Source for [symmetric_power_is_quotient]: Federer 1.9.1, p. 41,
    component- quotient display. Supporting construction for this passage,
    in words: The quotient of the tensor power by its ideal intersection is
    linearly isomorphic to the corresponding symmetric power. *)
Theorem symmetric_power_is_quotient :
  exists (f : {linear Qn -> En}) (g : {linear En -> Qn}),
    cancel f g /\ cancel g f /\
    (forall x, component_val (f (pin x)) = pi (component_val x)).
Proof.
exists symmetric_power_quotient, symmetric_power_inverse; split.
  exact: symmetric_power_quotientK.
split; first exact: symmetric_power_inverseK.
by move=> x; rewrite symmetric_power_quotientE symmetric_power_projectionE.
Qed.
End PowerQuotient.
