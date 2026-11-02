(** Federer (1969), 2.7.16, example (3), printed p. 137: "For this purpose
    we choose a subspace Z of V so that V = W (+) Z and construct a left G
    action preserving isomorphism xi: X ~ Hom(W, W) x Hom(Z, V), xi(f) =
    (f|W, f|Z) whenever f in X." Here a base e of V adapted to W
    (SubspaceStabiliser.v) is given; Z is the subspace of the vectors x with
    e_i*(x) = 0 for i <= m (adapted_complement), spanned by e_{m+1}, ...,
    e_{m+q}, and V = W (+) Z through the projections x |-> sum_{i <= m}
    e_i*(x) e_i and x |-> sum_{j} e_{m+j}*(x) e_{m+j} (projection_split).
    The map xi of X = subspace_preserving_maps into Hom(W, W) x Hom(Z, V) is
    linear (subspace_decomposition_linear), bijective, with inverse (A, C)
    |-> (x |-> A(x_W) + C(x_Z)) (subspace_decomposition_bijective), and
    carries g o f to ((g|W) o (f|W), g o (f|Z)) for g with g[W] c W
    (subspace_decomposition_equivariant): the action of G on Hom(W, W) x
    Hom(Z, V) is by the linear group of W on the first factor and by the
    linear group of V on the second, as used with (2). The determinant
    computations of StabiliserHomSpace.v use the base of X corresponding
    under xi to the base of Hom(W, W) x Hom(Z, V) *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import LinearBasis FiniteDualDimension Bilinear Annihilator Hom ModuleQuotient
  SubspaceCarrier SymmetricEndomorphisms InvariantRestriction TensorUP SubspaceStabiliser
  StabiliserHomSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Decomposition.
Variable R : realType.
Variable V : lmodType R.
Variable W : subspace V.
Variable m : nat.
Variable w : 'I_m -> subspace_space W.
Hypothesis hw : is_basis w.
Variable q : nat.
Variable e : 'I_(m + q) -> V.
Hypothesis heb : is_basis e.
Hypothesis hew : forall i, e (lshift q i) = subspace_val (w i).
Local Notation es := (dual_basis heb).
Local Notation Xs := (subspace_preserving_maps W).
Local Notation X := (subspace_space Xs).

(** Source for [complement_pred]: e_i*(x) = 0 for i <= m, the defining
    condition of the complement Z of "V = W (+) Z", Federer 2.7.16,
    p. 137. Definition. *)
Definition complement_pred (x : V) : Prop := forall i : 'I_m, es (lshift q i) x = 0.

(** Source for [complement_zero]: 0 belongs to Z, Federer 2.7.16,
    p. 137. Supporting lemma. *)
Lemma complement_zero : complement_pred 0.
Proof. by move=> i; rewrite (lin0 (hom_linear _)). Qed.

(** Source for [complement_add]: Z is closed under addition, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma complement_add x y : complement_pred x -> complement_pred y -> complement_pred (x + y).
Proof. by move=> hx hy i; rewrite (linD (hom_linear _)) hx hy addr0. Qed.

(** Source for [complement_scale]: Z is closed under multiplication by
    scalars, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma complement_scale a x : complement_pred x -> complement_pred (a *: x).
Proof. by move=> hx i; rewrite (linZ (hom_linear _)) hx scaler0. Qed.

(** Source for [adapted_complement]: "a subspace Z of V so that
    V = W (+) Z", Federer 2.7.16, p. 137. Definition. *)
Definition adapted_complement : subspace V :=
  @Subspace R V complement_pred complement_zero complement_add complement_scale.

Local Notation Z := adapted_complement.

(** Source for [projection_left]: the component x_W = sum_{i <= m}
    e_i*(x) e_i of x in W, Federer 2.7.16, p. 137. Definition. *)
Definition projection_left (x : V) : V := \sum_i (es (lshift q i) x : R) *: e (lshift q i).

(** Source for [projection_right]: the component x_Z =
    sum_j e_{m+j}*(x) e_{m+j} of x in Z, Federer 2.7.16, p. 137.
    Definition. *)
Definition projection_right (x : V) : V := \sum_j (es (rshift m j) x : R) *: e (rshift m j).

(** Source for [projection_split]: x = x_W + x_Z, "V = W (+) Z",
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma projection_split x : x = projection_left x + projection_right x.
Proof. by rewrite {1}(basis_vector_expansion heb x) big_split_ord. Qed.

(** Source for [projection_left_member]: x_W belongs to W, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma projection_left_member x : W (projection_left x).
Proof.
apply: big_ind; [exact: subspace_zero|move=> u v; exact: subspace_add|move=> i _].
by apply: subspace_scale; rewrite hew; exact: subspace_valP.
Qed.

(** Source for [projection_right_member]: x_Z belongs to Z, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma projection_right_member x : Z (projection_right x).
Proof.
move=> i; rewrite /projection_right.
rewrite (big_morph (es (lshift q i)) (linD (hom_linear _)) (lin0 (hom_linear _))).
apply: big1=> j _; rewrite (linZ (hom_linear _)) dual_basisE.
by rewrite eq_sym eq_lrshift scaler0.
Qed.

(** Source for [projection_right_subspace]: x_Z = 0 for x in W, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma projection_right_subspace x : W x -> projection_right x = 0.
Proof.
move=> hx; apply: big1=> j _.
by rewrite ((adapted_subspaceE hw heb hew x).1 hx j) scale0r.
Qed.

(** Source for [projection_left_complement]: x_W = 0 for x in Z,
    Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma projection_left_complement x : Z x -> projection_left x = 0.
Proof. by move=> hx; apply: big1=> i _; rewrite hx scale0r. Qed.

(** Source for [projection_left_linear]: x |-> x_W is linear, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma projection_left_linear : linear projection_left.
Proof.
move=> a x y; rewrite /projection_left scaler_sumr -big_split; apply: eq_bigr=> i _.
by rewrite (linD (hom_linear _)) (linZ (hom_linear _)) scalerDl scalerA.
Qed.

(** Source for [projection_right_linear]: x |-> x_Z is linear, Federer
    2.7.16, p. 137. Supporting lemma. *)
Lemma projection_right_linear : linear projection_right.
Proof.
move=> a x y; rewrite /projection_right scaler_sumr -big_split; apply: eq_bigr=> j _.
by rewrite (linD (hom_linear _)) (linZ (hom_linear _)) scalerDl scalerA.
Qed.

(** Source for [subspace_decomposition]: "xi(f) = (f|W, f|Z) whenever
    f in X", Federer 2.7.16, p. 137, with values in
    Hom(W, W) x Hom(Z, V). Definition. *)
Definition subspace_decomposition (f : X) :
    (Hom (subspace_space W) (subspace_space W) * Hom (subspace_space Z) V)%type :=
  (hom_of_linear (preserving_restriction (subspace_valP f)),
   hom_comp (subspace_val f) (hom_of_linear (subspace_inclusion Z))).

(** Source for [subspace_decomposition_linear]: xi is linear, Federer
    2.7.16, p. 137. Direct formalisation. *)
Theorem subspace_decomposition_linear : linear subspace_decomposition.
Proof.
move=> a f g; congr (_, _); apply: hom_ext=> x.
  apply: subspace_val_injective; rewrite hom_addE hom_scaleE.
  rewrite [RHS]linearP !hom_of_linearE !preserving_restrictionE.
  by rewrite linearP hom_addE hom_scaleE.
by rewrite hom_addE hom_scaleE !hom_compE linearP hom_addE hom_scaleE.
Qed.

(** Source for [decomposition_inverse_fun]: the map
    x |-> A(x_W) + C(x_Z) for (A, C) in Hom(W, W) x Hom(Z, V), the
    inverse of xi, Federer 2.7.16, p. 137. Definition of the
    function. *)
Definition decomposition_inverse_fun
    (p : (Hom (subspace_space W) (subspace_space W) * Hom (subspace_space Z) V)%type) (x : V) : V :=
  subspace_val (p.1 (subspace_lift (projection_left_member x))) + p.2 (subspace_lift (projection_right_member x)).

(** Source for [decomposition_inverse_linear]: the inverse of xi has
    linear values, Federer 2.7.16, p. 137. Supporting lemma. *)
Lemma decomposition_inverse_linear p : linear (decomposition_inverse_fun p).
Proof.
move=> a x y; rewrite /decomposition_inverse_fun.
have hl : subspace_lift (projection_left_member (a *: x + y)) =
    a *: subspace_lift (projection_left_member x) + subspace_lift (projection_left_member y).
  by apply: subspace_val_injective; rewrite [RHS]linearP !subspace_liftE projection_left_linear.
have hr : subspace_lift (projection_right_member (a *: x + y)) =
    a *: subspace_lift (projection_right_member x) + subspace_lift (projection_right_member y).
  by apply: subspace_val_injective; rewrite [RHS]linearP !subspace_liftE projection_right_linear.
rewrite hl hr !(linD (hom_linear _)) !(linZ (hom_linear _)) linearD linearZ.
by rewrite scalerDr addrACA.
Qed.

HB.instance Definition _ p := GRing.isLinear.Build R V V *:%R
  (decomposition_inverse_fun p) (decomposition_inverse_linear p).

(** Source for [decomposition_inverse_hom]: the inverse of xi, as a
    member of Hom(V, V), Federer 2.7.16, p. 137. Definition. *)
Definition decomposition_inverse_hom p : Hom V V :=
  hom_of_linear (GRing.Linear.clone _ _ _ _ (decomposition_inverse_fun p) _).

(** Source for [decomposition_inverse_member]: A(x_W) + C(x_Z) maps W
    into W, so that the inverse of xi takes values in X, Federer 2.7.16,
    p. 137. Supporting lemma. *)
Lemma decomposition_inverse_member p : preserving_pred W (decomposition_inverse_hom p).
Proof.
move=> x hx; rewrite hom_of_linearE /= /decomposition_inverse_fun.
have -> : subspace_lift (projection_right_member x) = 0.
  by apply: subspace_val_injective; rewrite subspace_liftE projection_right_subspace // linear0.
rewrite (linear0 (hom_as_linear p.2)) addr0; exact: subspace_valP.
Qed.

(** Source for [decomposition_inverse]: the inverse of xi with values
    in X, Federer 2.7.16, p. 137. Definition. *)
Definition decomposition_inverse p : X :=
  @subspace_lift R (Hom V V) Xs (decomposition_inverse_hom p) (decomposition_inverse_member p).

(** Source for [subspace_decomposition_bijective]: "xi: X ~
    Hom(W, W) x Hom(Z, V)" is an isomorphism, Federer 2.7.16, p. 137:
    f(x) = f(x_W) + f(x_Z), and A(x_W) + C(x_Z) restricts to A on W
    and to C on Z. Direct formalisation. *)
Theorem subspace_decomposition_bijective : bijective subspace_decomposition.
Proof.
exists decomposition_inverse.
  move=> f; apply: subspace_val_injective; apply: hom_ext=> x.
  change (subspace_val f (projection_left x) + subspace_val f (projection_right x) = subspace_val f x).
  by rewrite -(linearD (hom_as_linear (subspace_val f))) /= -projection_split.
move=> [A C]; congr (_, _); apply: hom_ext=> x.
  apply: subspace_val_injective.
  change (subspace_val (A (subspace_lift (projection_left_member (subspace_val x)))) +
    C (subspace_lift (projection_right_member (subspace_val x))) = subspace_val (A x)).
  have -> : subspace_lift (projection_left_member (subspace_val x)) = x.
    apply: subspace_val_injective; rewrite subspace_liftE.
    rewrite [RHS](projection_split (subspace_val x)) projection_right_subspace ?addr0 //.
    exact: subspace_valP.
  have -> : subspace_lift (projection_right_member (subspace_val x)) = 0.
    apply: subspace_val_injective; rewrite subspace_liftE linear0.
    by apply: projection_right_subspace; exact: subspace_valP.
  by rewrite (lin0 (hom_linear C)) addr0.
change (subspace_val (A (subspace_lift (projection_left_member (subspace_val x)))) +
  C (subspace_lift (projection_right_member (subspace_val x))) = C x).
have -> : subspace_lift (projection_left_member (subspace_val x)) = 0.
  apply: subspace_val_injective; rewrite subspace_liftE linear0.
  by apply: projection_left_complement; exact: subspace_valP.
have -> : subspace_lift (projection_right_member (subspace_val x)) = x.
  apply: subspace_val_injective; rewrite subspace_liftE.
  rewrite [RHS](projection_split (subspace_val x)) projection_left_complement ?add0r //.
  exact: subspace_valP.
by rewrite (lin0 (hom_linear A)) linear0 add0r.
Qed.

(** Source for [subspace_decomposition_equivariant]: xi is "left G
    action preserving", Federer 2.7.16, p. 137: xi(g o f) =
    ((g|W) o (f|W), g o (f|Z)) for g with g[W] c W, so that G acts on
    Hom(W, W) through the linear group of W and on Hom(Z, V) through the
    linear group of V. Direct formalisation. *)
Theorem subspace_decomposition_equivariant (g : Hom V V) (hg : preserving_pred W g) (f : X) :
  subspace_decomposition (preserving_left_composition hg f) =
    (hom_comp (hom_of_linear (preserving_restriction hg)) (subspace_decomposition f).1,
     hom_comp g (subspace_decomposition f).2).
Proof.
by congr (_, _); apply: hom_ext=> x; first apply: subspace_val_injective.
Qed.

End Decomposition.
