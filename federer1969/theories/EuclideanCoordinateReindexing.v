(** Coordinate support for Federer (1969), 3.2.45, p. 279:
    move a chosen scalar row to the first coordinate using the
    already proved orthogonal and Lebesgue laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  OrthogonalMaps EuclideanLinearMaps EuclideanLebesgueDimensions EuclideanLebesgueDeterminant.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_euclidean_coordinate_reindexing]: independent
    coordinate laws for a helper in Federer 3.2.45, p. 279.
    The finite coordinate maps of 1.7.1, p. 28, specify the
    action; neither existence nor orthogonality is assumed by
    this predicate. Empty coordinate families are retained. *)
Definition is_euclidean_coordinate_reindexing (R : realType) m
    (sigma : 'I_m -> 'I_m) (T : {linear R_n R m -> R_n R m}) : Prop :=
  forall x i, T x i = x (sigma i).

(** Source for [euclidean_coordinate_reindexing_exists]: local
    existence for the preceding independent laws, supporting
    Federer 3.2.45, p. 279, from the finite coordinate laws
    of 1.7.1, p. 28. The construction proves existence only;
    no global coordinate change is selected. *)
Lemma euclidean_coordinate_reindexing_exists (R : realType) m (sigma : 'I_m -> 'I_m) :
  exists T : {linear R_n R m -> R_n R m}, is_euclidean_coordinate_reindexing sigma T.
Proof.
pose t (x : R_n R m) : R_n R m := [ffun i => x (sigma i)].
have hLinear : linear t.
  by move=> c x y; apply/ffunP=> i; rewrite /t !ffunE.
pose L := @HomMap R (R_n R m) (R_n R m) t (introT (asboolP _) hLinear).
exists (hom_as_linear L)=> x i.
by rewrite hom_as_linearE /L /= /t ffunE.
Qed.

(** Source for [euclidean_coordinate_reindexing_orthogonal]: finite
    coordinate permutations preserve the original dot product,
    Federer 1.7.2, p. 28, supporting 3.2.45, p. 279.
    Finite injectivity suffices; no inverse is an extra premise. *)
Lemma euclidean_coordinate_reindexing_orthogonal (R : realType) m
    (sigma : 'I_m -> 'I_m) (T : {linear R_n R m -> R_n R m}) :
  injective sigma -> is_euclidean_coordinate_reindexing sigma T ->
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) T.
Proof.
move=> hInjective hT x y.
rewrite /euclidean_inner_product.
under eq_bigr do rewrite !hT.
symmetry; exact: reindex_inj hInjective.
Qed.

(** Source for [euclidean_coordinate_reindexing_volume]: the
    reindexing preserves actual Lebesgue outer volume, by 2.7.16,
    p. 135, supporting Federer 3.2.45, p. 279. The determinant
    and image laws already include arbitrary source sets and zero
    dimension; no new invariance assumption is introduced. *)
Lemma euclidean_coordinate_reindexing_volume (R : realType) m
    (sigma : 'I_m -> 'I_m) (T : {linear R_n R m -> R_n R m}) :
  injective sigma -> is_euclidean_coordinate_reindexing sigma T ->
  forall S, @euclidean_lebesgue_measure R m (T @` S) = euclidean_lebesgue_measure m S.
Proof.
move=> hInjective hT S.
rewrite euclidean_lebesgue_linear_image.
by rewrite (euclidean_orthogonal_det (euclidean_coordinate_reindexing_orthogonal hInjective hT)) mul1e.
Qed.
