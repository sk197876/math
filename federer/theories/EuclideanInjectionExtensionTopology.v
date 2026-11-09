(** Federer (1969), 3.3.4, pp. 289–290:
    the actual active orthogonal subgroup
    parameter is continuous in the original
    ambient group topology. No implementation
    of the opaque extension is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom HomInner HomSpaceTopology GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerMetric InnerNormedTopology OrthogonalMaps
  EuclideanRectangularAdjoint EuclideanInjectionRetraction EuclideanRectangularMapContinuity
  InjectionExtensionUP InjectionExtension EuclideanInjectionExtension
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure EuclideanOrthogonalBlockExtension
  EuclideanHomParameterContinuity TopologicalProductMaps IsotropyGroupTopology LinearGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [euclidean_injection_orthogonal_extension_continuous]:
    continuous identification of the active
    group with its actual ambient subgroup,
    supporting the Haar coset integral in
    Federer 3.3.4, pp. 289–290. The
    prior decomposition law and original group
    evaluation prove continuity on each ambient
    coordinate basis vector. *)
Theorem euclidean_injection_orthogonal_extension_continuous (R:realType) d n
    (w:Hom (R_n R d) (R_n R n))
    (hW:is_orthogonal_map (@euclidean_inner_product R d)
      (@euclidean_inner_product R n) (hom_as_linear w)):
  continuous (@euclidean_injection_orthogonal_extension R d n w hW).
Proof.
pose O:=[the topologicalType of set_type (euclidean_orthogonal_group R d)].
pose U:=inner_metric_space (@euclidean_inner_productP R d).
pose V:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=inner_metric_space (hom_inner_productP (@euclidean_inner_productP R n)
  (@euclidean_inner_productP R n) (@coordinate_basisP R n)).
pose L:=set_type (linear_group (@euclidean_inner_productP R n) (@coordinate_basisP R n)).
pose q:=euclidean_rectangular_adjoint w.
pose hCancel:=euclidean_orthogonal_injection_adjoint_cancel hW.
apply:(@set_type_continuous_into L _ O).
apply:(@set_type_continuous_into H _ O).
change (continuous (fun h:O=>(hom_of_linear (hom_as_linear
  (injection_extension hCancel (orthogonal_element_map h))):H))).
apply:euclidean_linear_family_continuous=>i.
pose x:=@coordinate_basis R n i.
have hPair:continuous (fun h:O=>(h,q x):O*U).
  apply:topological_pair_continuous; last exact:cst_continuous.
  by move=>h; exact:cvg_id.
have hEvaluation:continuous (fun h:O=>(orthogonal_element_map h (q x):U)).
  move=>h; exact:(continuous_comp (hPair h)
    (@euclidean_orthogonal_evaluation_continuous R d (h,q x))).
have hActive:continuous (fun h:O=>(w (orthogonal_element_map h (q x)):V)).
  move=>h; exact:(continuous_comp (hEvaluation h)
    (@euclidean_rectangular_map_continuous R d n w (orthogonal_element_map h (q x)))).
have hEqual:(fun h:O=>(hom_as_linear (injection_extension hCancel (orthogonal_element_map h)) x:V))=
    (fun h:O=>(x-w (q x)+w (orthogonal_element_map h (q x)):V)).
  apply:funext=>h; change (injection_extension hCancel (orthogonal_element_map h) x=
    x-w (q x)+w (orthogonal_element_map h (q x))).
  exact:(@injection_extension_decomposition R (R_n R d) (R_n R n)
    w q (orthogonal_element_map h) (injection_extension hCancel (orthogonal_element_map h))
    hCancel (injection_extension_specification hCancel (orthogonal_element_map h)) x).
rewrite hEqual; move=>h; apply:continuousD; first exact:cst_continuous.
exact:hActive h.
Qed.
