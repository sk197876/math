(** Federer (1969), 3.3.4, pp. 290–291: actual inverse coordinates
    on a coset of the active orthogonal subgroup. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanRectangularAdjointComposition EuclideanOrthogonalElementAdjoint
  InjectionExtension EuclideanInjectionRetraction EuclideanInjectionExtension EuclideanInjectionExtensionAdjoint
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [structure_active_coset_projection]: Federer 3.3.4,
    pp. 290–291. The projection of the actual inverse coset frame is
    h adjoint applied to the original projected inverse-frame vector.
    Both the ambient group operations and active inclusion stay local. *)
Theorem structure_active_coset_projection (R:realType) d n
    (w:Hom (R_n R d) (R_n R n))
    (hW:is_orthogonal_map (@euclidean_inner_product R d)
      (@euclidean_inner_product R n) (hom_as_linear w))
    (mulS:euclidean_orthogonal_group R n->euclidean_orthogonal_group R n->euclidean_orthogonal_group R n)
    (invS:euclidean_orthogonal_group R n->euclidean_orthogonal_group R n)
    (eS:euclidean_orthogonal_group R n)
    (hS:is_subgroup_restriction
      (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
      (euclidean_orthogonal_group R n) mulS invS eS)
    (g:euclidean_orthogonal_group R n) (h:euclidean_orthogonal_group R d) x:
  euclidean_rectangular_adjoint w
    (orthogonal_element_map (invS (mulS g (euclidean_injection_orthogonal_extension hW h))) x)=
  euclidean_rectangular_adjoint (orthogonal_element_map h)
    (euclidean_rectangular_adjoint w (orthogonal_element_map (invS g) x)).
Proof.
rewrite (euclidean_orthogonal_element_inverse_adjoint hS)
  (orthogonal_element_mul hS) euclidean_rectangular_adjoint_composition hom_compE
  (euclidean_orthogonal_element_inverse_adjoint hS).
have hExt:orthogonal_element_map (euclidean_injection_orthogonal_extension hW h)=
    injection_extension (euclidean_orthogonal_injection_adjoint_cancel hW) (orthogonal_element_map h).
  apply:hom_ext=>u; exact:euclidean_injection_orthogonal_extensionE.
rewrite hExt.
exact:euclidean_injection_extension_adjoint_projection.
Qed.
