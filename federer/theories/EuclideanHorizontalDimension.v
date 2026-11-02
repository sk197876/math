(** Federer (1969), 3.2.28(2), printed p. 264:
    dim Z(g)=m(n-m). The dimension belongs to the actual
    horizontal subspace and follows from its exact Hom
    coordinate isomorphism, not from a dimension premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct OrthogonalMaps LinearBasis FiniteOrdinalBasis
  HomCompositionDeterminant SubspaceCarrier EuclideanStiefelSubspaces
  EuclideanFrameComplementExistence EuclideanHorizontalHomCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_hom_ordinal_basis_exists]: Hom(R^m,R^k)
    has a basis of size mk, by 1.1.2 and 1.4.5,
    pp. 10 and 20–21. Supporting dim Z(g) in Federer
    3.2.28(2), p. 264, including all zero dimensions. *)
Lemma euclidean_hom_ordinal_basis_exists (R:realType) m k:
  exists b:'I_(m*k)->Hom (R_n R m) (R_n R k),is_basis b.
Proof.
have hCard:#|{: 'I_m*'I_k}|=(m*k)%N by rewrite card_prod !card_ord.
rewrite -hCard.
exists (@hom_rank_one_base R (R_n R m) (R_n R k) m k
  (@coordinate_basis R m) (@coordinate_basisP R m) (@coordinate_basis R k)).
exact:(@hom_rank_one_baseP R (R_n R m) (R_n R k) m k
  (@coordinate_basis R m) (@coordinate_basisP R m)
  (@coordinate_basis R k) (@coordinate_basisP R k)).
Qed.

(** Source for [euclidean_stiefel_horizontal_dimension]: the
    exact printed equality dim Z(g)=m(n-m), Federer
    3.2.28(2), p. 264. The independently specified
    normal coordinates are proved to exist. *)
Theorem euclidean_stiefel_horizontal_dimension (R:realType) m n
    (g:Hom (R_n R m) (R_n R n)):
  (m<=n)%N ->is_orthogonal_map (@euclidean_inner_product R m)
    (@euclidean_inner_product R n) (hom_as_linear g) ->
  exists e:'I_(m*(n-m))->subspace_space (euclidean_stiefel_horizontal_subspace g),
    is_basis e.
Proof.
move=>hm hg.
have [a [p hC]]:=euclidean_frame_complement_exists hm hg.
have [f [q [hf [hq [hFe hQe]]]]]:=euclidean_horizontal_hom_coordinates_exist hC.
have [b hb]:=@euclidean_hom_ordinal_basis_exists R m (n-m).
exists (fun i=>f (b i)).
exact:(@basis_transport R (Choice.clone 'I_(m*(n-m)) _)
  (Hom (R_n R m) (R_n R (n-m)))
  (subspace_space (euclidean_stiefel_horizontal_subspace g)) b
  (hom_as_linear f) (hom_as_linear q) hf hq hb).
Qed.
