(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: the original coordinate residual and denominator vary continuously under inverse unitary pullback. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicGermParameterArithmetic TopologicalProductMaps ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Relation.
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
Variable inv:U->U.
Variable gamma:G.
(** Source for [holomorphic_coordinate_relation_map_continuous]:
    the actual joint coordinate-incidence map, 3.4.12, p. 339. *)
Lemma holomorphic_coordinate_relation_map_continuous:
  continuous (fun p:M*
      U=>
    (@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv p.2) p.1:
      M)) ->
  continuous (fun p:(M*
      M)*
      U=>
    ((p.1.1,p.1.2),
      ((@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv p.2)
        ((p.1.1:G)*gamma-
          (p.1.2:G)):
        M),
       (@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv p.2) p.1.1:
        M)))).
Proof.
move=>hInverse.
pose T:=((M*M)*U)%type.
pose d:=fun p:T=>p.1.1.
pose l:=fun p:T=>p.1.2.
pose g:=fun p:T=>p.2.
have hD:continuous d.
  move=>p;exact:(continuous_comp (@first_projection_continuous (M*M)%type U p)
    (@first_projection_continuous M M p.1)).
have hL:continuous l.
  move=>p;exact:(continuous_comp (@first_projection_continuous (M*M)%type U p)
    (@second_projection_continuous M M p.1)).
have hG:continuous g:=@second_projection_continuous (M*M)%type U.
have hProduct:continuous (fun p:T=>((d p:G)*gamma:M)).
  exact:(@holomorphic_germ_parameter_multiply_continuous R X NX hNXR 0 T d (fun _=>gamma)
    hD (@cst_continuous T M gamma)).
pose residual:=fun p:T=>((d p:G)*gamma-(l p:G):M).
have hResidual:continuous residual.
  exact:(@holomorphic_germ_parameter_subtract_continuous R X NX hNXR 0 T
    (fun p:T=>((d p:G)*gamma:M)) l hProduct hL).
have hRPair:=@continuous_common_domain_pair T M U residual g hResidual hG.
have hDPair:=@continuous_common_domain_pair T M U d g hD hG.
pose r:=fun p:T=>(@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv (g p)) (residual p):M).
pose v:=fun p:T=>(@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv (g p)) (d p):M).
have hR:continuous r.
  move=>p;exact:(continuous_comp (hRPair p) (hInverse (residual p,g p))).
have hV:continuous v.
  move=>p;exact:(continuous_comp (hDPair p) (hInverse (d p,g p))).
have hFirst:=@continuous_common_domain_pair T M M d l hD hL.
have hSecond:=@continuous_common_domain_pair T M M r v hR hV.
exact:(@continuous_common_domain_pair T (M*M)%type (M*M)%type
  (fun p:T=>(d p,l p)) (fun p:T=>(r p,v p)) hFirst hSecond).
Qed.
End Relation.
