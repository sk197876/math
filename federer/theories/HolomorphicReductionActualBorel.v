(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5),
    p. 328: all original A_j, B_j, C_m and E_m sets are Borel. Actual compact witnesses and continuous incidence maps discharge the original hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions cardinality reals constructive_ereal topology subtype_topology.
From Federer Require Import Hom HomInner RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HermitianUP HermitianRealImaginary HermitianComplexNorm InnerNorm InnerMetric HilbertFormCompactness LinearBasis
  ComplexOrderedBases OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology LinearGroupSealed
  TopologicalGroupUP IsotropyGroupTopology UnitaryGroup UnitaryGroupHaar UnitaryComplexMapSealed
  HolomorphicGermUP HolomorphicGermRing HolomorphicGermMetric HolomorphicUnitaryPullback.
From Federer Require Import CommutativeIdealUP HolomorphicCoordinateGermsSealed HolomorphicCoordinateSubringFamilyUP
  HolomorphicCoordinateSubringFamilySealed HolomorphicReductionLociUP HolomorphicReductionActual HolomorphicRotatedGermIdeal
  HolomorphicPrefixGermSubring HolomorphicRotatedPrefixIncidenceBorel HolomorphicDirectionalJetOpen
  HolomorphicRotatedCoordinateRelationBorel HolomorphicReductionEBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Borel.
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
Variable hI:is_commutative_ideal I.
Local Notation gamma:=(@HolomorphicCoordinateGerms.value R X NX hNX n e he omega).
Local Notation Q:=(@HolomorphicCoordinateSubringFamily.value R X NX hNXR n e he omega).
Local Notation A:=(@holomorphic_reduction_actual_A R X H hH n e he omega I).
Local Notation Bj:=(@holomorphic_reduction_actual_B R X H hH n e he omega I).
Local Notation C:=(@holomorphic_reduction_actual_C R X H hH n e he omega I).
Local Notation E:=(@holomorphic_reduction_actual_E R X H hH n e he omega I).
(** Source for [holomorphic_reduction_actual_A_borel]: every
    original A_j, including A_0, is Borel,
    3.4.8(5), p. 328. *)
Lemma holomorphic_reduction_actual_A_borel j:borel_set (A j).
Proof.
have hLaws:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hQLaws:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hSame:A j = [set g:U|(0<j)%N /\exists alpha,rotated g alpha /\Q j alpha /\alpha<>0].
  apply/seteqP;split=>g.
  - exact:(holomorphic_reduction_A_membership hLaws j g).1.
  - exact:(holomorphic_reduction_A_membership hLaws j g).2.
rewrite hSame (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord j)).
case hPositive:(0<j)%N.
- have hNonzero:@open M (~` [set (0:G)]).
    apply:closed_openC;apply:accessible_closed_set1;apply:hausdorff_accessible;exact:metric_hausdorff.
  have hResult:=@holomorphic_rotated_prefix_open_incidence_borel R X H hH n e he omega hDual
    I j (ltn_ord j) (~` [set (0:G)]) hI hNonzero.
  have hPositiveSame:[set g:U|(0<j)%N /\exists alpha,rotated g alpha /\
      @holomorphic_prefix_germ_subring R X NX hNXR n e he omega j (ltn_ord j) alpha /\alpha<>0]=
    [set g:U|exists alpha,rotated g alpha /\
      @holomorphic_prefix_germ_subring R X NX hNXR n e he omega j (ltn_ord j) alpha /\alpha<>0].
    apply/seteqP;split=>g;first by move=>[_ h].
    move=>h;split;last exact:h;by rewrite hPositive.
  rewrite hPositive in hPositiveSame.
  rewrite hPositiveSame;exact:hResult.
- have hEmpty:[set g:U|(0<j)%N /\exists alpha,rotated g alpha /\
      @holomorphic_prefix_germ_subring R X NX hNXR n e he omega j (ltn_ord j) alpha /\alpha<>0]=set0.
    apply/seteqP;split=>g;last by [].
    by move=>[hj _];rewrite hPositive in hj.
  rewrite hPositive in hEmpty.
  rewrite hEmpty;apply:open_borel_set;exact:open0.
Qed.

(** Source for [holomorphic_reduction_actual_B_borel]: every
    original B_(j+1) is Borel, with its actual
    positive derivative test, 3.4.8(5), p. 328. *)
Lemma holomorphic_reduction_actual_B_borel j:borel_set (Bj j).
Proof.
have hLaws:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hQLaws:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hSame:Bj j = [set g:U|exists alpha,rotated g alpha /\Q (j:nat).+1 alpha /\
    has_nonzero_holomorphic_directional_jet hNX alpha (e j)].
  apply/seteqP;split=>g.
  - exact:(holomorphic_reduction_B_membership hLaws j g).1.
  - exact:(holomorphic_reduction_B_membership hLaws j g).2.
rewrite hSame (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord j)).
exact:(@holomorphic_rotated_prefix_open_incidence_borel R X H hH n e he omega hDual
  I (j:nat).+1 (ltn_ord j) [set alpha|has_nonzero_holomorphic_directional_jet hNX alpha (e j)] hI
  (@holomorphic_positive_directional_jet_open R X NX hNX (e j))).
Qed.

(** Source for [holomorphic_reduction_actual_C_borel]: every
    original C_m is Borel with the actual
    gamma_j, Q_j and I_g, 3.4.8(5), p. 328. *)
Lemma holomorphic_reduction_actual_C_borel m:borel_set (C m).
Proof.
have hLaws:=@holomorphic_reduction_actual_laws R X H hH n e he omega I.
have hQLaws:=@HolomorphicCoordinateSubringFamily.laws R X NX hNXR n e he omega.
have hSame:C m = [set g:U|forall j:'I_n,(m<=j)%N ->exists delta L,
    Q m delta /\~rotated g delta /\Q (m:nat).+1 L /\rotated g (delta*gamma j-L)].
  apply/seteqP;split=>g.
  - exact:(holomorphic_reduction_C_membership hLaws m g).1.
  - exact:(holomorphic_reduction_C_membership hLaws m g).2.
rewrite hSame (holomorphic_coordinate_subring_family_member hQLaws (ltnW (ltn_ord m)))
  (holomorphic_coordinate_subring_family_member hQLaws (ltn_ord m)).
pose D:set 'I_n:=fun j=>(m<=j)%N.
pose F:=fun j:'I_n=>[set g:U|exists delta L,
  @holomorphic_prefix_germ_subring R X NX hNXR n e he omega m (ltnW (ltn_ord m)) delta /\
  ~rotated g delta /\
  @holomorphic_prefix_germ_subring R X NX hNXR n e he omega (m:nat).+1 (ltn_ord m) L /\
  rotated g (delta*gamma j-L)].
change (borel_set (\bigcap_(j in D) F j)).
apply:(@borel_set_countable_intersection U (Choice.clone 'I_n _) D F).
- exact:(finite_set_countable (@finite_finset (Finite.clone 'I_n _) D)).
- exists m;exact:leqnn.
- move=>j _;exact:(@holomorphic_rotated_coordinate_relation_borel R X H hH n e he omega hDual
    I m (ltn_ord m) (gamma j) hI).
Qed.

(** Source for [holomorphic_reduction_actual_E_borel]: every
    original E_m, including E_n and the n=0
    case, is Borel, 3.4.8(5), p. 328. *)
Lemma holomorphic_reduction_actual_E_borel j:borel_set (E j).
Proof.
exact:(@holomorphic_reduction_E_borel_from_membership R X NX hNX n U e gamma Q rotated A Bj C E
  (@holomorphic_reduction_actual_laws R X H hH n e he omega I)
  holomorphic_reduction_actual_A_borel holomorphic_reduction_actual_B_borel holomorphic_reduction_actual_C_borel j).
Qed.

End Borel.
