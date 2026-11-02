(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import OmegaNaturality FiniteEvaluation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: the finite-evaluation
    reconstruction factors through the dual of a finite-dimensional
    coordinate space. *)
Section Maps.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> Hom V K^o.
Local Notation C := (coordinate_space K n).
(** Source for [point_synthesis]: Federer (1969), 1.4.4, p. 19, monomorphism
    assertion and basis argument. In words: Omega is injective because it
    takes exterior products of independent covectors to their independent
    alternating products. Definition or construction used to formalise this
    passage. *)
Definition point_synthesis : {linear C -> V} :=
  linear_comp (basis_synthesis e) (GRing.Linear.clone _ _ _ _ (@coordinate_to_free K n) _).
(** Source for [point_synthesisE]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma point_synthesisE i : point_synthesis (coordinate_basis K i) = e i.
Proof.
change (basis_synthesis e (coordinate_to_free (coordinate_basis K i)) = e i).
by rewrite -(coordinate_from_free_delta K i) coordinate_from_freeK basis_synthesisE.
Qed.
(** Source for [covector_extension]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Definition or construction used to
    formalise this passage. *)
Definition covector_extension (a : Hom C K^o) : Hom V K^o :=
  \sum_i (a (coordinate_basis K i) : K) *: omega i.
(** Source for [covector_extension_linear]: Federer (1969), 1.4.4, p. 19,
    monomorphism assertion and basis argument. In words: Omega is injective
    because it takes exterior products of independent covectors to their
    independent alternating products. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma covector_extension_linear : linear covector_extension.
Proof.
move=> c a b; rewrite /covector_extension scaler_sumr -big_split /=.
apply: eq_bigr => i _.
change ((c*a (coordinate_basis K i)+b (coordinate_basis K i)) *: omega i =
  c *: ((a (coordinate_basis K i) : K) *: omega i) + (b (coordinate_basis K i) : K) *: omega i).
by rewrite scalerDl scalerA.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K (Hom C K^o) (Hom V K^o)
  *:%R covector_extension covector_extension_linear.
(** Source for [finite_evaluation_factorisation]: Federer (1969), 1.4.4, p.
    19, monomorphism assertion and basis argument. In words: Omega is
    injective because it takes exterior products of independent covectors to
    their independent alternating products. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma finite_evaluation_factorisation (a : Hom V K^o) :
  covector_extension (@Hom_dual K C V (scalar_algebra K) point_synthesis a) =
  evaluation_reconstruction e omega a.
Proof.
rewrite /covector_extension /evaluation_reconstruction.
apply: eq_bigr => i _; by rewrite Hom_dualE point_synthesisE.
Qed.
End Maps.
