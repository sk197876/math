(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: actual rotated ideals have Borel incidence with an
    original complex prefix and an open germ condition. Reuse
    the proved compact-cover incidence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import CommutativeIdealUP HolomorphicIdealCompactCover HolomorphicPrefixGermSubring
  HolomorphicUnitaryJointContinuity HolomorphicRotatedGermIdeal CompactCoverIncidenceBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Incidence.
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
Variable j:nat.
Variable hJN:(j<=n)%N.
Local Notation Q:=(@holomorphic_prefix_germ_subring R X NX hNXR n e he omega j hJN).
Local Notation rotated:=(@holomorphic_rotated_germ_ideal R X H hH (n+n) eR heR I).

(** Source for [holomorphic_rotated_prefix_open_incidence_borel]:
    the original compact-projection step for A_j and B_j,
    3.4.12, p. 339. Every compact-cover, closedness and
    joint-continuity premise is proved for the actual objects. *)
Theorem holomorphic_rotated_prefix_open_incidence_borel (V:set M):
  is_commutative_ideal I ->open V ->
  borel_set [set g:U|exists beta,rotated g beta /\Q beta /\V beta].
Proof.
move=>hI hV.
pose F:=fun p:M*U=>(P p.2 p.1:M).
have [K hK]:=@holomorphic_ideal_increasing_compact_cover_exists R X NX hNX 0 n e I he hI.
have hCompact:@compact U setT:=@unitary_group_compact R X H hH (n+n) eR heR.
have hHausdorff:hausdorff_space U.
  have [mulO [invO [unitO [hO [mulU [invU [unitU [hU [hLocal hHaar]]]]]]]]]:=
    @unitary_group_haar_exists R X H hH (n+n) eR heR.
  exact:(lch_group_hausdorff hLocal).
have hClosed:@closed M Q:=@holomorphic_prefix_germ_subring_closed R X NX hNXR n e he omega j hJN hDual.
have hF:continuous F:=@holomorphic_unitary_germ_map_jointly_continuous R X H hH (n+n) eR heR.
have hIncidence:=@compact_cover_incidence_borel R M U [the pseudoMetricType R of M]
  I K F Q V hK hCompact hHausdorff hF hClosed hV.
have hSame:[set g:U|exists beta,rotated g beta /\Q beta /\V beta]=
    [set g:U|exists alpha:M,I alpha /\Q (F (alpha,g)) /\V (F (alpha,g))].
  apply/seteqP;split.
  - move=>g [beta [hRotated [hQ hOpen]]].
    have [alpha [hAlpha hEqual]]:=(@holomorphic_rotated_germ_ideal_membership R X H hH
      (n+n) eR heR I g beta).1 hRotated.
    exists alpha;split;first exact:hAlpha.
    by rewrite /F hEqual.
  - move=>g [alpha [hAlpha [hQ hOpen]]].
    exists (F (alpha,g));split;last by split.
    apply/(@holomorphic_rotated_germ_ideal_membership R X H hH (n+n) eR heR I g (F (alpha,g))).
    exists alpha;by split.
rewrite hSame;exact:hIncidence.
Qed.
End Incidence.
