(** Supporting the double rotation average in Federer (1969), 2.10.46, p.
    204; Freilich (1950), Theorem 4.5, Parts 6–7, pp. 247–250. A continuous
    family of transverse evaluations gives a continuous family of block
    extensions. The proof uses only the abstract block law and the existing
    Euclidean product topology, without opening the sealed implementation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBlockCoordinates EuclideanBlockExtensionUP EuclideanBlockExtension TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_block_extension_family_continuous]: supporting
    parameter continuity for the source rotations of 2.10.46,
    p. 204; Freilich (1950), Part 7, pp. 249–250.
    Continuity is derived from the coordinate law rather than
    assumed as part of the chosen block extension. *)
Theorem euclidean_block_extension_family_continuous (R : realType) m n (S : topologicalType)
    (h : S -> {linear R_n R n -> R_n R n}) :
  continuous (fun z : S * inner_metric_space (@euclidean_inner_productP R n)=>
    (h z.1 z.2 : inner_metric_space (@euclidean_inner_productP R n))) ->
  continuous (fun z : S * inner_metric_space (@euclidean_inner_productP R (m+n))=>
    (@euclidean_block_extension R m n (h z.1) z.2 : inner_metric_space (@euclidean_inner_productP R (m+n)))).
Proof.
move=> hh.
pose X := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose L := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose left (z : S*X) : L := (@euclidean_block_split R m n z.2).1.
pose right (z : S*X) : Y := (@euclidean_block_split R m n z.2).2.
have hs : continuous (fun z : S*X=>@euclidean_block_split R m n z.2).
  move=> z; exact (continuous_comp (@second_projection_continuous S X z)
    (@euclidean_block_split_continuous R m n z.2)).
have hl : continuous left.
  move=> z; exact (continuous_comp (hs z) (@first_projection_continuous L Y (euclidean_block_split z.2))).
have hr : continuous right.
  move=> z; exact (continuous_comp (hs z) (@second_projection_continuous L Y (euclidean_block_split z.2))).
have hi : continuous (fun z : S*X=>(z.1,right z)).
  apply: topological_pair_continuous; [exact: first_projection_continuous | exact hr].
have ho : continuous (fun z : S*X=>(h z.1 (right z) : Y)).
  move=> z; exact (continuous_comp (hi z) (hh (z.1,right z))).
have hp : continuous (fun z : S*X=>((left z,h z.1 (right z)) : L*Y)).
  exact: topological_pair_continuous hl ho.
have he : (fun z : S*X=>(@euclidean_block_extension R m n (h z.1) z.2 : X))=
    (fun z=>@euclidean_block_join R m n (left z,h z.1 (right z))).
  apply: funext=> z; exact (@euclidean_block_extension_coordinate_law R m n (h z.1)
    (@euclidean_block_extension R m n (h z.1))
    (@euclidean_block_extension_specification R m n (h z.1)) z.2).
rewrite he=> z; exact (continuous_comp (hp z)
  (@euclidean_block_join_continuous R m n (left z,h z.1 (right z)))).
Qed.
