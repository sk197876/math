(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: a linear map taking one basis
    to another is a linear isomorphism. *)
Section BasisMap.
Variable K : fieldType.
Variable I : choiceType.
Variables V W : lmodType K.
Variable e : I -> V.
Hypothesis he : is_basis e.
Variable f : {linear V -> W}.
Hypothesis hf : is_basis (fun i => f (e i)).
(** Source for [basis_map_injective]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma basis_map_injective : injective f.
Proof.
move=> x y hxy.
have hc : basis_coordinates he x = basis_coordinates he y.
  apply: (basis_synthesis_injective hf).
  by rewrite !basis_synthesis_comp !basis_coordinatesK.
by rewrite -(basis_coordinatesK he x) -(basis_coordinatesK he y) hc.
Qed.
(** Source for [basis_map_surjective]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma basis_map_surjective : forall y, exists x, f x = y.
Proof.
move=> y; exists (basis_synthesis e (basis_coordinates hf y)).
by rewrite -basis_synthesis_comp basis_coordinatesK.
Qed.
End BasisMap.
