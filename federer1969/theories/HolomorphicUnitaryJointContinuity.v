(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: actual unitary pullback is jointly continuous in
    the germ and original unitary transformation. Reuse the proved
    finite linear-family theorem and relative evaluation topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology UnitaryGroup UnitaryComplexMapSealed UnitaryCoordinateFixing
  HolomorphicGermUP HolomorphicGermMetric HolomorphicUnitaryPullback HolomorphicLinearFamilyJointContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Joint.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Variable hH:is_hermitian_product H.
Variable N:nat.
Variable e:'I_N->restricted_space (ComplexScalars.embed R) X.
Variable he:is_basis e.
Local Notation U:=(@unitary_group R X H hH N e he).
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation mapg:=(fun g:U=>@UnitaryComplexMap.value R X H hH N e he g).

(** Source for [unitary_complex_fixed_vector_continuous]: actual
    unitary evaluation in the original relative group topology,
    supporting 3.4.12, p. 339. *)
Lemma unitary_complex_fixed_vector_continuous x:
  continuous (fun g:U=>(mapg g x:real_norm_metric_space hNX)).
Proof.
have hSame:(fun g:U=>mapg g x)=(fun g:U=>
  @orthogonal_element_map R (restricted_space (ComplexScalars.embed R) X)
    (hermitian_real_part H) (hermitian_real_inner_product hH) N e he (set_val g) x).
  apply:funext=>g;exact:(@UnitaryComplexMap.laws R X H hH N e he g x).
rewrite hSame;exact:(@unitary_fixed_vector_continuous R X H hH N e he x).
Qed.

(** Source for [holomorphic_unitary_germ_map_jointly_continuous]:
    the original joint unitary/germ continuity in the compact
    projection argument of 3.4.12, p. 339. *)
Theorem holomorphic_unitary_germ_map_jointly_continuous:
  continuous (fun p:(@holomorphic_germ_metric R X NX hNX 0)*U=>
    (@holomorphic_unitary_germ_map R X H hH N e he p.2 p.1:
      @holomorphic_germ_metric R X NX hNX 0)).
Proof.
exact:(@holomorphic_linear_family_pullback_jointly_continuous R X X NX NX hNX hNX 0 0
  N e he U mapg (fun g=>@holomorphic_unitary_germ_map R X H hH N e he g)
  (fun g=>@holomorphic_unitary_germ_map_specification R X H hH N e he g)
  (fun g=>linear0 (mapg g)) unitary_complex_fixed_vector_continuous).
Qed.
End Joint.
