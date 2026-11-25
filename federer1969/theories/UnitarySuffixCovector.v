(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(8),
    p. 330: the original inverse unitary coordinate is the
    conjugated coordinate combination. Preserve the original Hermitian
    convention, linearity in the second argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicGermFormsSealed HolomorphicReductionLociUP HolomorphicReductionActual
  HolomorphicRotatedGermIdeal HolomorphicUnitaryPullbackComposition PointedHolomorphicLinearPullbackForms
  HolomorphicCoordinateSubringFamilySealed UnitaryCoordinateFixing HolomorphicUnitaryPrefixInvariance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
From Federer Require Import TopologicalGroupLaws UnitaryGroupClosed.
From Federer Require Import OrthonormalFamilies Bilinear TensorUP ComplexScalarLaws HermitianComplexLinearity HermitianBasisCoordinates UnitaryHermitianPreservation OrdinalCoordinateTail OrdinalCoordinateTailSum Annihilator FiniteDualDimension DualityAnnihilator.
Import ComplexScalarTheory.
Section Coordinates.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation B:=(hermitian_real_part H).
Local Notation hB:=(hermitian_real_inner_product hH).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(hermitian_complex_norm hH).
Local Notation hNXR:=(complex_norm_real hNX).
Local Notation eR:=(ordered_real_basis e).
Local Notation heR:=(ordered_real_basisP he).
Local Notation O:=(@orthogonal_group R XR B hB (n+n) eR heR).
Local Notation U:=(@unitary_group R X H hH (n+n) eR heR).
Local Notation M:=(@holomorphic_germ_metric R X NX hNXR 0).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNXR 0)].
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH (n+n) eR heR g).
Local Notation P:=(fun g:U=>@holomorphic_unitary_germ_map R X H hH (n+n) eR heR g).
Variable omega:'I_n->Hom X (ComplexScalars.C R)^o.
Variable hDual:forall i k,omega i (e k)=if i==k then 1 else 0.
Variable hON:orthonormal_family H e.
Variables q h:U.
Variable hInverse:forall x:X,mapg q (mapg h x)=x.
(** Source for [unitary_fixed_prefix_covector]: fixing the original
    first m basis vectors fixes their dual coordinates,
    3.4.12, p. 339. *)
Lemma unitary_fixed_prefix_covector m:
  @holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m q ->
  forall i:'I_n,(i<m)%N ->forall x,omega i (mapg q x)=omega i x.
Proof.
move=>hQ i hi x.
have hFixed:=((@unitary_coordinate_fixing_membership R X H hH (n+n) eR heR n e
  [set j:'I_n|(j<m)%N] q).1 hQ) i hi.
have hFixedC:mapg q (e i)=e i by rewrite (@UnitaryComplexMap.laws R X H hH (n+n) eR heR q).
rewrite -!(@hermitian_basis_coordinate R X H hH n e he hON omega hDual i).
rewrite -{1}hFixedC;exact:(@unitary_element_hermitian R X H hH (n+n) eR heR q).
Qed.
(** Source for [unitary_inverse_covector_coordinates]: the exact
    full inverse-coordinate identity, with conjugated original
    coefficients, supporting 3.4.12, p. 339. *)
Theorem unitary_inverse_covector_coordinates (i:'I_n) x:
  omega i (mapg h x)=\sum_(j<n) conjugate (omega j (mapg q (e i)))*omega j x.
Proof.
have hExpand:x=\sum_(j<n) omega j x*:e j.
  rewrite {1}(@basis_vector_expansion (ComplexScalars.C R) X n e he x).
  apply:eq_bigr=>j _;by rewrite (biorthogonal_basis_unique he hDual j).
rewrite -(@hermitian_basis_coordinate R X H hH n e he hON omega hDual i).
have hPreserve:=@unitary_element_hermitian R X H hH (n+n) eR heR q (e i) (mapg h x).
rewrite hInverse in hPreserve;rewrite -hPreserve.
have hLinear:linear (fun y:X=>(H (mapg q (e i)) y:(ComplexScalars.C R)^o)).
  move=>c u v;rewrite (bilDr (hermitian_real_bilinear hH)) (hermitian_scale_right hH);by [].
pose F:=@HomMap (ComplexScalars.C R) X (ComplexScalars.C R)^o
  (fun y=>H (mapg q (e i)) y) (introT (asboolP _) hLinear).
rewrite {1}hExpand.
transitivity (\sum_(j<n) F (omega j x*:e j)).
- exact:(big_morph F (linD (hom_linear F)) (lin0 (hom_linear F))).
- apply:eq_bigr=>j _.
  transitivity (omega j x*H (mapg q (e i)) (e j)).
  + exact:(linZ (hom_linear F) (omega j x) (e j)).
  + rewrite mulrC (hermitian_conjugate_symmetric hH)
      (@hermitian_basis_coordinate R X H hH n e he hON omega hDual j);by [].
Qed.
(** Source for [unitary_primitive_suffix_covector]: remove precisely
    the fixed prefix from the original inverse-coordinate sum,
    3.4.12, p. 339. *)
Theorem unitary_primitive_suffix_covector (m:'I_n) (hMN:((m:nat)<=n)%N):
  @holomorphic_suffix_rotation_group R X H hH (n+n) eR heR n e m q ->forall x,
  omega m (mapg h x)=\sum_(i<n-m)
    conjugate (omega (ordinal_coordinate_tail_index hMN i) (mapg q (e m)))*
      omega (ordinal_coordinate_tail_index hMN i) x.
Proof.
move=>hQ x;rewrite unitary_inverse_covector_coordinates.
apply:ordinal_coordinate_tail_sum=>j hJM.
have hFixed:=unitary_fixed_prefix_covector hQ hJM (e m).
rewrite hFixed hDual.
have hDifferent:j!=m by apply/eqP=>hEqual;by rewrite hEqual ltnn in hJM.
by rewrite (negbTE hDifferent) -(rmorph0 (ComplexScalars.embed R)) conjugate_real rmorph0 mul0r.
Qed.
End Coordinates.
