(** Federer (1969), 3.2.19, p. 256: the image of an
    injective differential from R^m is an m-dimensional vector subspace.
    Use the project's basis specification of dimension and Grassmann space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier SubspaceSums LinearBasis LinearRankUP LinearInjectiveRank
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_injective_range_plane]: the m-dimensional
    vector-space assertion in Federer 3.2.19, p. 256, from the
    injective chart differential supplied by 3.2.18 and used in 3.2.17.
    Dimension zero and arbitrary natural target dimension are retained. *)
Lemma euclidean_injective_range_plane (R : realType) m n
    (D : Hom (R_n R m) (R_n R n)) :
  injective D -> exists P : GrassmannSubspaces.G (R_n R n) m,
    range D=[set v | grassmann_val P v].
Proof.
move=> hInj.
have hRank := @linear_injective_rank R (R_n R m) (R_n R n) m
  (@coordinate_basis R m) (@coordinate_basisP R m) n
  (@coordinate_basis R n) (@coordinate_basisP R n) D hInj.
pose P := @GrassmannSubspace R (R_n R n) m (range_subspace (hom_as_linear D)) hRank.
exists P; apply/seteqP; split=> y.
- by move=> [x _ <-]; exists x.
- move=> [x hx]; exists x=> //.
Qed.
