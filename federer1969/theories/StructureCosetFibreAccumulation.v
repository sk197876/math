(** Federer (1969), 3.3.4, p. 292: original radial image intersections
    imply accumulation in the actual original coset kernel plane. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanBlockLinearMaps CoordinateProjection StructureActiveCoordinatesUP
  StructureActiveCoordinatesOrthogonal StructureActiveCosetCoordinates StructureActiveDirectionFibre
  StructureDirectionMapUP StructureProjectiveSpace StructureCoordinateCones
  EuclideanInjectionExtension EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed SymmetricSquareGeometry
  EuclideanProjectionSpace StructureProjectionKernel StructurePlaneGrowth StructureRadialFibreAccumulation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Coset.
Variable R:realType.
Variables m k:nat.
Variable j:'I_k.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R (m+k))).
Local Notation O:=(euclidean_orthogonal_group R (m+k)).
Variable w:Hom (R_n R (1+m)) (R_n R (m+k)).
Hypothesis hW:is_structure_active_inclusion j w.
Local Notation hOrth:=(structure_active_inclusion_orthogonal hW).
Variables (mulS:O->O->O) (invS:O->O) (eS:O).
Hypothesis hS:is_subgroup_restriction
  (linear_group_mul (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  (linear_group_inv (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  (linear_group_unit (@euclidean_inner_productP R (m+k)) (@coordinate_basisP R (m+k)))
  O mulS invS eS.
Variables (A:set E) (a:E) (g:O).
Local Notation qg:=(fun x:E=>euclidean_rectangular_adjoint w (orthogonal_element_map (invS g) (x-a))).
Local Notation D:=[set x:E|0<inner_norm (@euclidean_inner_productP R m.+1) (qg x)].
Variable f:E->structure_projective_space R m.
Hypothesis hF:is_structure_projective_direction_map qg f.

(** Source for [structure_coset_original_image_accumulation]: Federer
    3.3.4, p. 292, the inclusion F inverse R contained in D.
    The actual direction domain excludes the original centre and both
    projective signs lie in the original affine kernel. Each source
    point comes from the original radial image, without a hull. *)
Theorem structure_coset_original_image_accumulation
    (hmn:(m<=m+k)%N)
    (h:euclidean_orthogonal_group R m.+1) (z:structure_projective_space R m)
    (p:euclidean_projection_space R (m+k) m):
  val z=inner_projective_square (orthogonal_element_map h
    (@coordinate_basis R m.+1 (lshift m (ord0:'I_1)))) ->
  (forall y,euclidean_projection_linear p y=
    @euclidean_first_block R m k
      (orthogonal_element_map (invS (mulS g (euclidean_injection_orthogonal_extension hOrth h))) y)) ->
  (\bigcap_i (f @` [set x:E|A x /\ mdist a x<((i.+1)%:R:R)^-1 /\ D x])) z ->
  structure_plane_accumulation A a (structure_projection_kernel hmn p).
Proof.
move=>hz hP hImages.
apply:(@structure_original_radial_fibre_accumulation R (m+k) ((m+k)-m)
  (structure_projective_space R m) A D a (structure_projection_kernel hmn p) f z)=>//.
- move=>x hx; apply/eqP=>hEqual.
  have hZero:qg a=0.
    rewrite subrr.
    have hG0:orthogonal_element_map (invS g) 0=0:=linear0 (hom_as_linear (orthogonal_element_map (invS g))).
    have hQ0:euclidean_rectangular_adjoint w 0=0:=linear0 (hom_as_linear (euclidean_rectangular_adjoint w)).
    by rewrite hG0 hQ0.
  change (is_true (0<inner_norm (@euclidean_inner_productP R m.+1) (qg x))) in hx.
  by move:hx; rewrite hEqual hZero inner_norm0 ltxx.
- move=>x hA hx hValue; apply/(structure_projection_kernelE hmn p (x-a)); rewrite hP.
  apply:(@structure_active_direction_fibre_kernel R E m k j w qg f
    (orthogonal_element_map h) z x
    (orthogonal_element_map (invS (mulS g (euclidean_injection_orthogonal_extension hOrth h))) (x-a))
    hW hF (orthogonal_element_orthogonal h) hz _ hx hValue).
  exact:(@structure_active_coset_projection R (1+m) (m+k) w hOrth mulS invS eS hS g h (x-a)).
Qed.
End Coset.
