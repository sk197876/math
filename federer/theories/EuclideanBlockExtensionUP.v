(** Supporting Federer (1969), 2.10.46, p. 204: the orthogonal changes of
    transverse coordinates in Freilich (1950), Theorem 4.5, Parts 6–7, pp.
    247–250. Specify an extension by its commuting block-coordinate law: it
    fixes the first block and acts by h on the second. Existence and opaque
    selection are separate. Freilich puts the fixed scalar coordinate last;
    our first-block convention is the orthogonal reordering of 2.6.5, p.
    120. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinear OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_euclidean_block_extension]: supporting abstract
    block-action law for 2.10.46, p. 204; Freilich
    (1950), Theorem 4.5, Part 6, pp. 247–249.
    A linear extension is specified before any implementation. *)
Definition is_euclidean_block_extension (R : realType) m n
    (h : {linear R_n R n -> R_n R n})
    (H : {linear R_n R (m+n) -> R_n R (m+n)}) : Prop :=
  forall u y, H (@euclidean_block_join R m n (u,y))=@euclidean_block_join R m n (u,h y).

(** Source for [euclidean_block_extension_coordinate_law]: supporting
    coordinate consequence of the abstract extension for 2.10.46,
    p. 204; Freilich (1950), Part 6, pp. 247–249. *)
Lemma euclidean_block_extension_coordinate_law (R : realType) m n
    (h : {linear R_n R n -> R_n R n})
    (H : {linear R_n R (m+n) -> R_n R (m+n)}) :
  is_euclidean_block_extension h H -> forall z,
    H z=@euclidean_block_join R m n
      ((@euclidean_block_split R m n z).1,h (@euclidean_block_split R m n z).2).
Proof.
move=> hh z; have he := hh (@euclidean_block_split R m n z).1 (@euclidean_block_split R m n z).2.
by rewrite -surjective_pairing euclidean_block_splitK in he.
Qed.

(** Source for [euclidean_block_extension_unique]: supporting
    uniqueness from the block law for 2.10.46, p. 204.
    This justifies treating the abstract extension as the named
    coordinate operation of Freilich (1950), Part 6, pp. 247–249. *)
Lemma euclidean_block_extension_unique (R : realType) m n
    (h : {linear R_n R n -> R_n R n})
    (H G : {linear R_n R (m+n) -> R_n R (m+n)}) :
  is_euclidean_block_extension h H -> is_euclidean_block_extension h G -> forall z, H z=G z.
Proof.
move=> hH hG z.
by rewrite (euclidean_block_extension_coordinate_law hH) (euclidean_block_extension_coordinate_law hG).
Qed.

(** Source for [euclidean_block_extension_preserves_inner]: supporting
    orthogonality of the transverse extension in 2.10.46,
    p. 204; Freilich (1950), Part 6, pp. 247–249.
    This follows from the defining law and the Euclidean product
    inner product, rather than being an assumed construction property. *)
Lemma euclidean_block_extension_preserves_inner (R : realType) m n
    (h : {linear R_n R n -> R_n R n})
    (H : {linear R_n R (m+n) -> R_n R (m+n)}) :
  is_euclidean_block_extension h H ->
  is_orthogonal_map (@euclidean_inner_product R n) (@euclidean_inner_product R n) h ->
  is_orthogonal_map (@euclidean_inner_product R (m+n)) (@euclidean_inner_product R (m+n)) H.
Proof.
move=> hH hh x y.
rewrite !(euclidean_block_extension_coordinate_law hH) euclidean_block_join_inner hh.
have he := @euclidean_block_join_inner R m n (euclidean_block_split x) (euclidean_block_split y).
by rewrite !euclidean_block_splitK in he; exact: esym he.
Qed.

(** Source for [euclidean_block_extension_cancel]: supporting
    inverse action law in Freilich (1950), Part 6,
    pp. 247–249, for 2.10.46, p. 204.
    Inverse transverse maps give inverse extensions by uniqueness
    of their block coordinates. *)
Lemma euclidean_block_extension_cancel (R : realType) m n
    (h g : {linear R_n R n -> R_n R n})
    (H G : {linear R_n R (m+n) -> R_n R (m+n)}) :
  is_euclidean_block_extension h H -> is_euclidean_block_extension g G ->
  cancel h g -> cancel H G.
Proof.
move=> hH hG hh z.
rewrite (euclidean_block_extension_coordinate_law hH) hG hh -surjective_pairing.
exact: euclidean_block_splitK.
Qed.
