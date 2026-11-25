(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: actual unitary inversion gives a jointly continuous
    family of inverse germ pullbacks. The group operations and
    both inverse equations are proved internally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import HolomorphicUnitaryJointContinuity PointedHolomorphicPullbackRetraction
  TopologicalProductMaps ContinuousCommonPair.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Inverse.
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

(** Source for [holomorphic_unitary_continuous_inverse_exists]:
    actual inverse unitary pullback and its original cancellation
    laws, supporting 3.4.12, p. 339. *)
Theorem holomorphic_unitary_continuous_inverse_exists:
  exists inv:U->U,continuous inv /\
    (forall g alpha,P (inv g) (P g alpha)=alpha) /\
    (forall g alpha,P g (P (inv g) alpha)=alpha) /\
    continuous (fun p:M*U=>(P (inv p.2) p.1:M)).
Proof.
have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal hHaar]]]]]]]]]:=
  @unitary_group_haar_exists R X H hH (n+n) eR heR.
have hInv:continuous invU:=topological_group_inv_continuous (lch_group_topological hLocal).
have hMapLeft g x:mapg (invU g) (mapg g x)=x.
  rewrite !(@UnitaryComplexMap.laws R X H hH (n+n) eR heR)
    (subgroup_restriction_inv hU).
  exact:(@orthogonal_element_inv R XR B hB (n+n) eR heR mulO invO unitO hO (set_val g)).1.
have hMapRight g x:mapg g (mapg (invU g) x)=x.
  rewrite !(@UnitaryComplexMap.laws R X H hH (n+n) eR heR)
    (subgroup_restriction_inv hU).
  exact:(@orthogonal_element_inv R XR B hB (n+n) eR heR mulO invO unitO hO (set_val g)).2.
have hCancel g:(forall alpha,P (invU g) (P g alpha)=alpha) /\
    (forall alpha,P g (P (invU g) alpha)=alpha).
  split.
  - exact:(@pointed_holomorphic_germ_pullback_retraction R X X NX NX hNXR hNXR 0 0
      (mapg g) (mapg (invU g)) (P g) (P (invU g))
      (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR g)
      (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR (invU g)) (hMapRight g)).
  - exact:(@pointed_holomorphic_germ_pullback_retraction R X X NX NX hNXR hNXR 0 0
      (mapg (invU g)) (mapg g) (P (invU g)) (P g)
      (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR (invU g))
      (@holomorphic_unitary_germ_map_specification R X H hH (n+n) eR heR g) (hMapLeft g)).
exists invU;split;first exact:hInv.
split;first by move=>g;exact:(hCancel g).1.
split;first by move=>g;exact:(hCancel g).2.
have hSecond:continuous (fun p:M*U=>invU p.2).
  move=>p;exact:(continuous_comp (@second_projection_continuous M U p) (hInv p.2)).
have hPair:=@continuous_common_domain_pair (M*U)%type M U fst (fun p=>invU p.2)
  (@first_projection_continuous M U) hSecond.
move=>p;exact:(continuous_comp (hPair p)
  (@holomorphic_unitary_germ_map_jointly_continuous R X H hH (n+n) eR heR (p.1,invU p.2))).
Qed.
End Inverse.
