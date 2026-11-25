(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.classical Require Import boolp.
From Federer Require Import InteriorDuality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: the vector space carried by a subspace, including
    the associated space T and the finite-dimensional spaces used in
    the reduction. Membership remains the predicate already used for
    quotients; inclusion is a proved injective linear map. *)
Section Carrier.
Variable K : fieldType.
Variable V : lmodType K.
Variable S : subspace V.
(** Source for [subspace_pred]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition subspace_pred (v : V) := `[< S v >].
(** Source for [subspace_space]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Record subspace_space := SubspaceVector {
  subspace_val : V;
  subspace_proof : subspace_pred subspace_val
}.
(** Source for [subspace_rect]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition subspace_rect (P : subspace_space -> Type)
    (h : forall v hv, P (@SubspaceVector v hv)) (z : subspace_space) : P z :=
  match z as z' return P z' with @SubspaceVector v hv => h v hv end.
HB.instance Definition _ := [isSub for subspace_val by subspace_rect].
HB.instance Definition _ := [Choice of subspace_space by <:].
(** Source for [subspace_pred_closed]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma subspace_pred_closed : GRing.submod_closed subspace_pred.
Proof.
split; first by apply/asboolP; exact: subspace_zero.
move=> c x y /asboolP hx /asboolP hy; apply/asboolP.
exact: subspace_add (subspace_scale c hx) hy.
Qed.
HB.instance Definition _ := GRing.SubChoice_isSubLmodule.Build
  K V subspace_pred subspace_space subspace_pred_closed.
(** Source for [subspace_val_linear]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma subspace_val_linear : linear subspace_val.
Proof. move=> c x y; change (val (c *: x+y) = c *: val x+val y); exact: linearP. Qed.
HB.instance Definition _ := GRing.isLinear.Build K subspace_space V *:%R
  subspace_val subspace_val_linear.
(** Source for [subspace_valP]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma subspace_valP (x : subspace_space) : S (subspace_val x).
Proof. apply/asboolP; exact: subspace_proof. Qed.
(** Source for [subspace_val_injective]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma subspace_val_injective : injective subspace_val.
Proof. exact: val_inj. Qed.
(** Source for [subspace_lift]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition subspace_lift v (hv : S v) : subspace_space :=
  @SubspaceVector v (introT (asboolP _) hv).
(** Source for [subspace_liftE]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Supporting lemma for this passage; not separately stated in
    the book. *)
Lemma subspace_liftE v hv : subspace_val (@subspace_lift v hv) = v.
Proof. by []. Qed.
(** Source for [subspace_inclusion]: Federer (1969), 1.6.1, p. 23, dimension
    bound, factorisation assertion, and finite-dimensional reduction. In
    words: For a nonzero m-vector the associated space has dimension k<=m;
    the product of any basis of that space factors from the vector, leaving
    degree m-k. Definition or construction used to formalise this passage. *)
Definition subspace_inclusion : {linear subspace_space -> V} :=
  GRing.Linear.clone _ _ _ _ subspace_val _.
(** Source for [subspace_retraction]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Definition or construction used to formalise
    this passage. *)
Definition subspace_retraction : {linear V -> subspace_space} :=
  linear_retraction subspace_val_injective.
(** Source for [subspace_retractionK]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma subspace_retractionK : cancel subspace_inclusion subspace_retraction.
Proof. exact: linear_retractionK. Qed.
(** Source for [subspace_retraction_on]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma subspace_retraction_on v : S v -> subspace_inclusion (subspace_retraction v) = v.
Proof.
move=> hv; have h := subspace_retractionK (subspace_lift hv).
exact (congr1 subspace_inclusion h).
Qed.
End Carrier.
Arguments subspace_space {K V} S.
Arguments subspace_val {K V S} _.
