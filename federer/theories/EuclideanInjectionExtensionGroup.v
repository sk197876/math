(** Federer (1969), 3.3.4, pp. 289–290:
    the active orthogonal group is identified
    with its actual ambient subgroup. Prove
    multiplication, identity and injectivity for
    the existing opaque extension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  OrthogonalMaps EuclideanRectangularAdjoint EuclideanInjectionRetraction
  InjectionExtensionUP InjectionExtension EuclideanInjectionExtension
  EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section Group.
Variable R:realType.
Variables d n:nat.
Variable w:Hom (R_n R d) (R_n R n).
Hypothesis hW:is_orthogonal_map (@euclidean_inner_product R d)
  (@euclidean_inner_product R n) (hom_as_linear w).
Local Notation OD:=(euclidean_orthogonal_group R d).
Local Notation ON:=(euclidean_orthogonal_group R n).
Local Notation Ext:=(@euclidean_injection_orthogonal_extension R d n w hW).
Local Notation hCancel:=(euclidean_orthogonal_injection_adjoint_cancel hW).
Variables (mulD:OD->OD->OD) (invD:OD->OD) (eD:OD).
Variables (mulN:ON->ON->ON) (invN:ON->ON) (eN:ON).
Hypothesis hD:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R d) (@coordinate_basisP R d))
  (linear_group_inv (@euclidean_inner_productP R d) (@coordinate_basisP R d))
  (linear_group_unit (@euclidean_inner_productP R d) (@coordinate_basisP R d))
  OD mulD invD eD.
Hypothesis hN:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_inv (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  (linear_group_unit (@euclidean_inner_productP R n) (@coordinate_basisP R n))
  ON mulN invN eN.

(** Source for [euclidean_injection_extension_multiplication]:
    the active orthogonal identification is
    an actual group homomorphism, supporting
    the subgroups H and K in Federer
    3.3.4, pp. 289–290. Original restricted
    group operations remain local parameters. *)
Theorem euclidean_injection_extension_multiplication (h g:OD):
  Ext (mulD h g)=mulN (Ext h) (Ext g).
Proof.
apply:orthogonal_element_ext=>x.
rewrite (orthogonal_element_mulE hN) !euclidean_injection_orthogonal_extensionE
  (orthogonal_element_mul hD).
have he:=congr1 (fun H:Hom (R_n R n) (R_n R n)=>H x)
  (injection_extension_composition hCancel (orthogonal_element_map h) (orthogonal_element_map g)).
exact:esym he.
Qed.

(** Source for [euclidean_injection_extension_unit]: the
    actual active identity maps to the
    actual ambient identity, supporting the
    subgroup identification in Federer 3.3.4,
    pp. 289–290. *)
Theorem euclidean_injection_extension_unit:Ext eD=eN.
Proof.
have hIdentity:orthogonal_element_map eD=hom_of_linear (@linear_id R (R_n R d)).
  apply:hom_ext=>u; exact:orthogonal_element_unit hD u.
apply:orthogonal_element_ext=>x.
by rewrite euclidean_injection_orthogonal_extensionE hIdentity
  injection_extension_identity (orthogonal_element_unit hN).
Qed.

(** Source for [euclidean_injection_extension_injective]:
    the active group identification loses no
    original operator, supporting H and K
    in Federer 3.3.4, pp. 289–290.
    Its exact action on every w(u),
    followed by the actual adjoint retraction,
    recovers h on its whole original space. *)
Theorem euclidean_injection_extension_injective:injective Ext.
Proof.
move=>h g hEqual; apply:orthogonal_element_ext=>u.
have hPoint:=congr1 (fun H:ON=>orthogonal_element_map H (w u)) hEqual.
rewrite !euclidean_injection_orthogonal_extension_active in hPoint.
exact:(can_inj hCancel hPoint).
Qed.
End Group.
