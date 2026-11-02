(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, fourth corollary, reverse implication: every vector
    annihilating a left factor also annihilates the full product. *)
(** Source for [associated_factor_inclusion]: Federer (1969), 1.6.1, p. 24,
    fourth corollary. In words: Inclusion of associated spaces of nonzero
    simple vectors is equivalent to factoring the larger-degree vector by
    the smaller-degree vector with a factor of the complementary degree.
    Supporting lemma for this passage; not separately stated in the book.
    Follow the stated factorisation eta = xi wedge zeta. *)
Lemma associated_factor_inclusion (K : fieldType) (V : lmodType K) m n r
  (xi : exterior_power V m) (eta : exterior_power V n) (zeta : exterior_power V r) :
  component_val eta = wedge (component_val xi) (component_val zeta) ->
  forall v, FedererSimple.T xi v -> FedererSimple.T eta v.
Proof.
move=> he v hv; apply: (proj2 (FedererSimple.associated_left eta v)).
have hx := proj1 (FedererSimple.associated_left xi v) hv.
by rewrite he wedge_assoc hx (bil0l (wedge_bilinear V)).
Qed.
