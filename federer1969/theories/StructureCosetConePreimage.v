(** Federer (1969), 3.3.4, p. 291: identify the original I_j
    on the actual active-subgroup coset, with its original strict radius. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanBlockLinearMaps CoordinateProjection StructureActiveCoordinatesUP
  StructureActiveCoordinatesOrthogonal StructureActiveCosetCoordinates StructureActiveDirectionCone
  StructureDirectionMapUP StructureProjectiveSpace StructureCoordinateCones
  EuclideanInjectionExtension EuclideanOrthogonalInvariantMeasures OrthogonalGroupHaarMeasure
  IsotropyGroupTopology LinearGroupTopology LinearGroupSealed SymmetricSquareGeometry.
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

(** Source for [structure_coset_coordinate_cone_preimage]: Federer
    3.3.4, p. 291, the displayed identification of I_j with the
    original radial source restricted to the projective-ball preimage.
    The actual orthogonal coset, the original set and every positive
    real aperture are retained. Zero projected vectors are excluded
    by the strict original cone inequality itself. *)
Theorem structure_coset_coordinate_cone_preimage
    (h:euclidean_orthogonal_group R m.+1) (z:structure_projective_space R m) (r t:R):
  val z=inner_projective_square (orthogonal_element_map h
    (@coordinate_basis R m.+1 (lshift m (ord0:'I_1)))) ->0<t ->
  structure_coordinate_cone A a
    (hom_as_linear (orthogonal_element_map (invS (mulS g (euclidean_injection_orthogonal_extension hOrth h))))) j r%:E t=
  [set x:E|A x /\ mdist a x<r /\ D x /\ mdist z (f x)<t].
Proof.
move=>hz ht; apply/seteqP; split=>x.
all: have hProj:=@structure_active_coset_projection R (1+m) (m+k) w hOrth
    mulS invS eS hS g h (x-a).
all: have hAngle:=@structure_active_direction_ball_cone R E m k j w qg f
    (orthogonal_element_map h) z x
    (orthogonal_element_map (invS (mulS g (euclidean_injection_orthogonal_extension hOrth h))) (x-a)) t
    hW hF (orthogonal_element_orthogonal h) hz hProj ht.
- move=>[hA [hR hCone]]; split=>//; split.
  + by rewrite inner_metric_distanceE -[a-x]opprB inner_normN; move:hR; rewrite lte_fin.
  + exact:hAngle.2 hCone.
- move=>[hA [hR hBall]]; split=>//; split.
  + by move:hR; rewrite inner_metric_distanceE -[a-x]opprB inner_normN -lte_fin.
  + exact:hAngle.1 hBall.
Qed.
End Coset.
