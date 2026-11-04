(** Federer (1969), 3.2.46, p. 282: frozen
    source and target linear coordinates preserve the
    whole original fibres. This exact set identity
    precedes all changes of integration variables. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets.
From Federer Require Import GrassmannAbbreviations MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_frozen_coarea_fibre_image]:
    the whole fibre of M composed F composed L^{-1}
    over M(y), with source L(S), equals L applied
    to the whole original fibre F|S over y.
    This is the actual coordinate procedure supporting
    3.2.46, p. 282; S need not be measurable. *)
Lemma euclidean_frozen_coarea_fibre_image (R : realType) m n
    (L I : {linear R_n R m -> R_n R m})
    (M : {linear R_n R n -> R_n R n})
    (F : R_n R m -> R_n R n) (S : set (R_n R m)) y :
  cancel L I -> injective M ->
  mapping_fibre (fun z=>M (F (I z))) (L @` S) (M y)=
    L @` mapping_fibre F S y.
Proof.
move=> hLI hM; apply/seteqP; split=> z.
- move=> [[x hx <-] hValue].
  exists x; last by []; split; first exact hx.
  apply:hM; by rewrite hLI in hValue.
- move=> [x [hx hValue] <-]; split.
  + by exists x.
  + by rewrite hLI hValue.
Qed.
