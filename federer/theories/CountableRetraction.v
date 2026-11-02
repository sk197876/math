(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingCoordinates.
From Federer Require Import InfiniteSequence LinearRetraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Infrastructure for Federer 1.4.4: every infinite-dimensional
    vector space contains a countable free space as a linear retract. *)
Section CountableIndependence.
Variable K : fieldType.
Variable V : lmodType K.
Variable e : nat -> V.
Hypothesis he : forall n, finite_independent (fun i : 'I_n => e (val i)).
Local Notation N := (Choice.clone nat _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K N) _).
Local Notation d := (@delta K N).
(** Source for [independent_synthesis_prefix]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma independent_synthesis_prefix n (z : coordinate_space K n) :
  basis_synthesis e (prefix_inclusion d n z) = prefix_inclusion e n z.
Proof.
apply: (basis_linear_ext (coordinate_basisP K n)
  (linear_comp (basis_synthesis e) (prefix_inclusion d n)) (prefix_inclusion e n)) z => i.
change (basis_synthesis e (prefix_inclusion d n (coordinate_basis K i)) =
  prefix_inclusion e n (coordinate_basis K i)).
by rewrite !prefix_inclusionE basis_synthesisE.
Qed.
(** Source for [countable_synthesis_injective]: Federer (1969), 1.4.4, p.
    20, infinite-dimensional assertion immediately before the parenthesis.
    In words: In infinite dimension, for every degree m at least two there
    are m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Theorem countable_synthesis_injective : injective (basis_synthesis e).
Proof.
have hker x : basis_synthesis e x = 0 -> x = 0.
  move=> hx; have [n hn] := prefix_eventually (free_basis K N) x.
  pose z := prefix_retraction (free_basis K N) n x.
  have hz : prefix_inclusion d n z = x := hn n (leqnn n).
  have hez : prefix_inclusion e n z = 0 by rewrite -independent_synthesis_prefix hz hx.
  have hz0 : coordinate_to_free z = 0.
    apply (@finite_synthesis_injective K (Finite.clone ('I_n) _) V (fun i => e (val i)) (@he n)).
    rewrite linear0; exact: hez.
  have hz' : z = 0.
    rewrite -(coordinate_to_freeK z) hz0 linear0; by [].
  by rewrite -hz hz' linear0.
move=> x y hxy; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: hker.
by rewrite linearB hxy subrr.
Qed.
End CountableIndependence.
Section CountableRetract.
Variable K : fieldType.
Variable V : lmodType K.
Hypothesis hinf : infinite_dimensional V.
Local Notation N := (Choice.clone nat _).
Local Notation F := (GRing.Lmodule.clone K (free_vector K N) _).
(** Source for [countable_inclusion]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition countable_inclusion : {linear F -> V} := basis_synthesis (independent_sequence hinf).
(** Source for [countable_inclusion_injective]: Federer (1969), 1.4.4, p.
    20, infinite-dimensional assertion immediately before the parenthesis.
    In words: In infinite dimension, for every degree m at least two there
    are m-covectors outside the image of Omega. Supporting lemma for this
    passage; not separately stated in the book. *)
Lemma countable_inclusion_injective : injective countable_inclusion.
Proof. apply: countable_synthesis_injective => n; exact: independent_sequence_prefix. Qed.
(** Source for [countable_retraction]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Definition or construction used
    to formalise this passage. *)
Definition countable_retraction : {linear V -> F} := linear_retraction countable_inclusion_injective.
(** Source for [countable_retractionK]: Federer (1969), 1.4.4, p. 20,
    infinite-dimensional assertion immediately before the parenthesis. In
    words: In infinite dimension, for every degree m at least two there are
    m-covectors outside the image of Omega. Formalises the indicated part of
    the passage under the hypotheses in the statement below. *)
Theorem countable_retractionK : cancel countable_inclusion countable_retraction.
Proof. exact: linear_retractionK. Qed.
End CountableRetract.
