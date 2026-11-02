(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SubspaceCarrier AssociatedSubspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, reduction to a subspace. Inclusion of an arbitrary
    subspace induces injective maps on the exterior algebra and its
    homogeneous powers, since a linear retraction induces a retraction. *)
Section Inclusion.
Variable K : fieldType.
Variable V : lmodType K.
Variable S : subspace V.
Local Notation U := (GRing.Lmodule.clone K (subspace_space S) _).
Local Notation iota := (subspace_inclusion S).
Local Notation r := (subspace_retraction S).
(** Source for [exterior_subspace_injective]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem exterior_subspace_injective : injective (exterior_algebra_map iota).
Proof. exact (can_inj (@exterior_algebra_mapK K U V iota r (@subspace_retractionK K V S))). Qed.
(** Source for [exterior_power_subspace_injective]: Federer (1969), 1.6.1,
    p. 23, dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem exterior_power_subspace_injective m : injective (exterior_power_map iota m).
Proof. exact (can_inj (@exterior_power_mapK K U V iota r (@subspace_retractionK K V S) m)). Qed.
(** Source for [associated_subspace_preimage]: Federer (1969), 1.6.1, p. 23,
    dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem associated_subspace_preimage m (eta : exterior_power U m) (u : U) :
  FedererSimple.T (exterior_power_map iota m eta) (iota u) <-> FedererSimple.T eta u.
Proof.
change (wedge (exterior_algebra_map iota (component_val eta)) (exterior_generator (iota u)) = 0 <->
  wedge (component_val eta) (exterior_generator u) = 0).
have he : exterior_algebra_map iota (wedge (component_val eta) (exterior_generator u)) =
  wedge (exterior_algebra_map iota (component_val eta)) (exterior_generator (iota u)).
  rewrite algebra_map_mul exterior_algebra_mapE; by [].
split=> h.
- apply: exterior_subspace_injective; by rewrite he linear0.
- by rewrite -he h linear0.
Qed.
End Inclusion.

(** Federer 1.6.1: every m-vector is carried by every subspace containing
    one suitable finite family. This is the finite-support step in the
    sentence reducing the proof to finite dimension. *)
Section Support.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable xi : exterior_power V m.
(** Source for [exterior_subspace_finite_support]: Federer (1969), 1.6.1, p.
    23, dimension bound, factorisation assertion, and finite-dimensional
    reduction. In words: For a nonzero m-vector the associated space has
    dimension k<=m; the product of any basis of that space factors from the
    vector, leaving degree m-k. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem exterior_subspace_finite_support :
  exists s : seq V, forall S : subspace V,
    (forall v, v \in s -> S v) ->
    exists eta : exterior_power (GRing.Lmodule.clone K (subspace_space S) _) m,
      exterior_power_map (subspace_inclusion S) m eta = xi.
Proof.
have [s hs] := exterior_finite_support (component_val xi).
exists s => S hS.
pose f := linear_comp (subspace_inclusion S) (subspace_retraction S).
have hf v : v \in s -> f v = v.
  move=> hv; exact: subspace_retraction_on (hS v hv).
have hx := hs f hf.
exists (exterior_power_map (subspace_retraction S) m xi).
apply: val_inj; change
  (exterior_algebra_map (subspace_inclusion S)
    (exterior_algebra_map (subspace_retraction S) (component_val xi)) = component_val xi).
by rewrite exterior_algebra_map_comp.
Qed.
End Support.
