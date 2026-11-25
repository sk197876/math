(** Supporting Federer (1969), 2.10.46, p. 204, and Freilich (1950), Theorem
    4.5, Parts 6–7, pp. 247–250: extend a transverse orthogonal map by the
    identity on the first block. The underlying linear map is the previously
    sealed block extension. Its membership and continuity in the orthogonal
    group follow from the abstract block law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  Hom HomInner HomSpaceTopology EuclideanHomParameterContinuity EuclideanBlockCoordinates
  EuclideanBlockExtensionUP EuclideanBlockExtension EuclideanBlockExtensionTopology
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_orthogonal_block_extension]: supporting
    group-valued version of the transverse coordinate rotation
    in Freilich (1950), Part 6, pp. 247–249, for
    2.10.46, p. 204. This only packages the sealed
    extension with its proved orthogonality law. *)
Definition euclidean_orthogonal_block_extension (R : realType) m n
    (g : euclidean_orthogonal_group R n) : euclidean_orthogonal_group R (m+n) :=
  orthogonal_element_of (@euclidean_inner_productP R (m+n)) (@coordinate_basisP R (m+n))
    (@euclidean_block_extension_orthogonal R m n
      (hom_as_linear (orthogonal_element_map g)) (orthogonal_element_orthogonal g)).

(** Source for [euclidean_orthogonal_block_extensionE]: supporting
    evaluation of the transverse rotation in Freilich (1950),
    Part 6, pp. 247–249, for 2.10.46, p. 204. *)
Lemma euclidean_orthogonal_block_extensionE (R : realType) m n
    (g : euclidean_orthogonal_group R n) u y :
  orthogonal_element_map (@euclidean_orthogonal_block_extension R m n g)
    (@euclidean_block_join R m n (u,y)) =
    @euclidean_block_join R m n (u,orthogonal_element_map g y).
Proof.
rewrite orthogonal_element_ofE.
exact: euclidean_block_extension_specification.
Qed.

(** Source for [euclidean_orthogonal_evaluation_continuous]: supporting
    joint evaluation continuity for the rotation average in
    2.10.46, p. 204; Freilich (1950), Part 7,
    pp. 249–250. This is the relative Hom evaluation
    topology of 2.7.16, p. 139. *)
Lemma euclidean_orthogonal_evaluation_continuous (R : realType) n :
  continuous (fun z : euclidean_orthogonal_group R n *
    inner_metric_space (@euclidean_inner_productP R n)=>
    (orthogonal_element_map z.1 z.2 : inner_metric_space (@euclidean_inner_productP R n))).
Proof.
pose O := euclidean_orthogonal_group R n.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose H := inner_metric_space (hom_inner_productP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n)).
have hp : continuous (fun z : O*X=>((orthogonal_element_map z.1,z.2) : H*X)).
  apply: topological_pair_continuous; last exact: second_projection_continuous.
  move=> z; exact (continuous_comp (@first_projection_continuous O X z)
    (@orthogonal_element_continuous R (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n) z.1)).
move=> z; exact (continuous_comp (hp z)
  (@hom_evaluation_continuous R (R_n R n) (R_n R n)
    (@euclidean_inner_product R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) (@euclidean_inner_productP R n)
    n (@coordinate_basis R n) (@coordinate_basisP R n) (orthogonal_element_map z.1,z.2))).
Qed.

(** Source for [euclidean_orthogonal_block_extension_continuous]:
    supporting continuous rotation parameter in Freilich (1950),
    Part 7, pp. 249–250, for 2.10.46, p. 204.
    Continuity is proved using only the sealed extension law
    and the relative topology of the orthogonal group. *)
Theorem euclidean_orthogonal_block_extension_continuous (R : realType) m n :
  continuous (@euclidean_orthogonal_block_extension R m n).
Proof.
pose O := euclidean_orthogonal_group R n.
pose X := inner_metric_space (@euclidean_inner_productP R (m+n)).
pose H := inner_metric_space (hom_inner_productP (@euclidean_inner_productP R (m+n))
  (@euclidean_inner_productP R (m+n)) (@coordinate_basisP R (m+n))).
pose L := set_type (linear_group (@euclidean_inner_productP R (m+n)) (@coordinate_basisP R (m+n))).
apply: (@set_type_continuous_into L _ O).
apply: (@set_type_continuous_into H _ O).
change (continuous (fun g : O=>
  (hom_of_linear (@euclidean_block_extension R m n (hom_as_linear (orthogonal_element_map g))) : H))).
apply: euclidean_linear_family_continuous=> i.
have he := @euclidean_block_extension_family_continuous R m n O
  (fun g=>hom_as_linear (orthogonal_element_map g)) (@euclidean_orthogonal_evaluation_continuous R n).
have hp : continuous (fun g : O=>((g,@coordinate_basis R (m+n) i) : O*X)).
  apply: topological_pair_continuous; last exact: cst_continuous.
  by move=> g; exact: cvg_id.
move=> g; exact (continuous_comp (hp g) (he (g,@coordinate_basis R (m+n) i))).
Qed.
