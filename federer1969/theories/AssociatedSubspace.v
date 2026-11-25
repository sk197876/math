(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import SubspaceCarrier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, opening definition: a simple m-vector is exactly
    an exterior product of m vectors. In particular the literal empty
    product in degree zero is the unit. *)
(** Source for [simple]: Federer (1969), 1.6.1, p. 23, opening definition
    and displayed associated subspace T. In words: A simple m-vector is a
    product of m vectors; its associated subspace consists of vectors v for
    which xi wedge v is zero. Definition or construction used to formalise
    this passage. *)
Definition simple (K : fieldType) (V : lmodType K) m (xi : exterior_power V m) :=
  exists t : m.-tuple V, xi = e_lambda idfun t.

(** Federer 1.6.1, associated subspace T=V intersect {v:xi wedge v=0}.
    The order xi wedge v is exactly the order used in the book. *)
Module FedererSimple.
Section Associated.
Variable K : fieldType.
Variable V : lmodType K.
Variable m : nat.
Variable xi : exterior_power V m.
(** Source for [associated]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Definition or construction used
    to formalise this passage. *)
Definition associated (v : V) := wedge (component_val xi) (exterior_generator v) = 0.
(** Source for [associated_zero]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma associated_zero : associated 0.
Proof. by rewrite /associated linear0 (bil0r (wedge_bilinear V)). Qed.
(** Source for [associated_add]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma associated_add v w : associated v -> associated w -> associated (v+w).
Proof.
move=> hv hw; rewrite /associated linearD (bilDr (wedge_bilinear V)).
by rewrite hv hw add0r.
Qed.
(** Source for [associated_scale]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma associated_scale c v : associated v -> associated (c *: v).
Proof.
move=> hv; rewrite /associated linearZ (bilZr (wedge_bilinear V)).
by rewrite hv scaler0.
Qed.
(** Source for [T]: Federer (1969), 1.6.1, p. 23, opening definition and
    displayed associated subspace T. In words: A simple m-vector is a
    product of m vectors; its associated subspace consists of vectors v for
    which xi wedge v is zero. Definition or construction used to formalise
    this passage. *)
Definition T : subspace V := @Subspace K V associated associated_zero associated_add associated_scale.
(** Source for [TE]: Federer (1969), 1.6.1, p. 23, opening definition and
    displayed associated subspace T. In words: A simple m-vector is a
    product of m vectors; its associated subspace consists of vectors v for
    which xi wedge v is zero. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma TE v : T v <-> wedge (component_val xi) (exterior_generator v) = 0.
Proof. by []. Qed.
(** Source for [associated_left]: Federer (1969), 1.6.1, p. 23, opening
    definition and displayed associated subspace T. In words: A simple
    m-vector is a product of m vectors; its associated subspace consists of
    vectors v for which xi wedge v is zero. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma associated_left v : T v <-> wedge (exterior_generator v) (component_val xi) = 0.
Proof.
have h := @exterior_anticommutative K V m 1 (component_val xi) (exterior_generator v)
  (component_homogeneous xi) (exterior_generator_homogeneous v).
have h' := @exterior_anticommutative K V 1 m (exterior_generator v) (component_val xi)
  (exterior_generator_homogeneous v) (component_homogeneous xi).
split=> hz.
- by rewrite h' hz scaler0.
- change (wedge (component_val xi) (exterior_generator v) = 0).
  by rewrite h hz scaler0.
Qed.
End Associated.
End FedererSimple.
