(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: the original denominator relation is Borel by compact projection of the actual closed prefix and ideal conditions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import CommutativeIdealUP HolomorphicGermIdealClosed HolomorphicPrefixGermSubring
  HolomorphicRotatedGermIdeal HolomorphicUnitaryInverseJointContinuity HolomorphicCoordinateRelationContinuity
  HolomorphicGermCompactCover IncreasingCompactCoverPair QuadrupleIncidenceClosed CompactCoverIncidenceBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinate.
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
Variable I:set G.
Local Notation rotated:=(@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I).
Variable m:nat.
Variable hmn:(m<n)%N.
Variable gamma:G.
(** Source for [holomorphic_rotated_coordinate_relation_borel]:
    the literal original coordinate relation defining C_m,
    3.4.12, p. 339. No Borel or closedness conclusion is a premise. *)
Theorem holomorphic_rotated_coordinate_relation_borel:
  is_commutative_ideal I ->borel_set [set g:U|exists delta L,
    @holomorphic_prefix_germ_subring R X NX hNXR n e he omega m (ltnW hmn) delta /\
    ~rotated g delta /\
    @holomorphic_prefix_germ_subring R X NX hNXR n e he omega m.+1 hmn L /\
    rotated g (delta*gamma-L)].
Proof.
move=>hI.
pose T:=(M*M)%type.
pose Z:=[the pseudoMetricType R of ((M*M)*(M*M))%type].
pose Qm:=@holomorphic_prefix_germ_subring R X NX hNXR n e he omega m (ltnW hmn).
pose Qnext:=@holomorphic_prefix_germ_subring R X NX hNXR n e he omega m.+1 hmn.
have hClosedI:@closed M I:=@finite_holomorphic_germ_ideal_closed R X NX hNX n e he 0 I hI.
have hClosedM:@closed M Qm:=@holomorphic_prefix_germ_subring_closed R X NX hNXR n e he omega m (ltnW hmn) hDual.
have hClosedNext:@closed M Qnext:=@holomorphic_prefix_germ_subring_closed R X NX hNXR n e he omega m.+1 hmn hDual.
have [inv [hInv [hLeft [hRight hInverse]]]]:=@holomorphic_unitary_continuous_inverse_exists R X H hH n e he.
pose F:=fun p:T*U=>((p.1.1,p.1.2),
  ((@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv p.2)
    ((p.1.1:G)*gamma-(p.1.2:G)):M),
   (@holomorphic_unitary_germ_map R X H hH (n+n) eR heR (inv p.2) p.1.1:M))).
pose Q:set Z:=fun z=>Qm z.1.1 /\Qnext z.1.2 /\I z.2.1.
pose V:set Z:=fun z=>~I z.2.2.
have [hClosedQ hOpenV]:=@quadruple_incidence_closed_open M Qm Qnext I I
  hClosedM hClosedNext hClosedI hClosedI.
have hF:continuous F:=@holomorphic_coordinate_relation_map_continuous R X H hH n e he inv gamma hInverse.
have [K hK]:=@holomorphic_germ_increasing_compact_cover_exists R X NX hNX 0 n e he.
have hPairCover:=@increasing_compact_cover_pair M M setT setT K K hK hK.
have hCompact:@compact U setT:=@unitary_group_compact R X H hH (n+n) eR heR.
have hHausdorff:hausdorff_space U.
  have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal hHaar]]]]]]]]]:=
    @unitary_group_haar_exists R X H hH (n+n) eR heR.
  exact:(lch_group_hausdorff hLocal).
have hBorel:=@compact_cover_incidence_borel R T U Z (setT `*` setT)
  (fun k=>K k `*` K k) F Q V hPairCover hCompact hHausdorff hF hClosedQ hOpenV.
have hSame:[set g:U|exists delta L,Qm delta /\
    ~@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g delta /\Qnext L /\
    @holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I g (delta*gamma-L)] =
    [set g:U|exists p:T,(setT `*` setT) p /\Q (F (p,g)) /\V (F (p,g))].
  apply/seteqP;split.
  - move=>g [delta [L [hDelta [hNot [hL hRelation]]]]].
    exists (delta,L);split;first by split.
    split.
    + split=>//;split=>//.
      exact:(@holomorphic_rotated_germ_ideal_inverse_membership R X H hH (n+n) eR heR I g
        (inv g) (hLeft g) (hRight g) (delta*gamma-L)).1 hRelation.
    + move=>hMember;apply:hNot.
      exact:(@holomorphic_rotated_germ_ideal_inverse_membership R X H hH (n+n) eR heR I g
        (inv g) (hLeft g) (hRight g) delta).2 hMember.
  - move=>g [[delta L] [_ [[hDelta [hL hRelation]] hNot]]].
    exists delta,L;split=>//;split.
    + move=>hMember;apply:hNot.
      exact:(@holomorphic_rotated_germ_ideal_inverse_membership R X H hH (n+n) eR heR I g
        (inv g) (hLeft g) (hRight g) delta).1 hMember.
    + split=>//.
      refine ((@holomorphic_rotated_germ_ideal_inverse_membership R X H hH (n+n) eR heR I g
        (inv g) (hLeft g) (hRight g) ((delta:G)*gamma-(L:G))).2 _).
      exact:hRelation.
rewrite hSame;exact:hBorel.
Qed.
End Coordinate.
