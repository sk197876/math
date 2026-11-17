(** Federer (1969), 3.4.8(5), p. 328, auxiliary proof sentence:
    the original A_j, B_j and C_m are countable compact unions.
    Retain the compact witnesses of their existing Borel proofs
    and use the original finite-intersection membership laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure TopologicalGroupUP
  AnalyticGermUP AnalyticGermRing AnalyticGermMetric CommutativeIdealUP AnalyticCoordinateGermsSealed
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilySealed AnalyticReductionLociUP
  AnalyticReductionActual AnalyticRotatedGermIdeal AnalyticPrefixGermSubring AnalyticDirectionalJetOpen
  IncreasingCompactCoverUP IncreasingCompactCoverIntersections AnalyticRotatedPrefixIncidenceCompactCover
  AnalyticRotatedCoordinateRelationCompactCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Covers.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Local Notation gamma:=(@AnalyticCoordinateGerms.value R X NX hNX n e he omega).
Local Notation A:=(@analytic_reduction_actual_A R X B hB n e he omega I).
Local Notation Bj:=(@analytic_reduction_actual_B R X B hB n e he omega I).
Local Notation C:=(@analytic_reduction_actual_C R X B hB n e he omega I).
Local Notation rotated:=(@analytic_rotated_germ_ideal R X B hB n e he I).
Local Notation hLoci:=(@analytic_reduction_actual_laws R X B hB n e he omega I).
Local Notation hQ:=(@AnalyticCoordinateSubringFamily.laws R X NX hNX n e he omega).

(** Source for [analytic_reduction_actual_A_compact_cover]: every
    original A_j is a countable compact union, as stated in the
    proof of Federer 3.4.8(5), p. 328. The original A_0 remains empty. *)
Theorem analytic_reduction_actual_A_compact_cover j:
  exists K:nat->set O,is_increasing_compact_cover (A j) K.
Proof.
case hPositive:(0<j)%N.
- pose M:=@analytic_germ_metric R X NX hNX 0.
  have hOpen:@open M (~` [set (0:G)]).
    apply:closed_openC;apply:accessible_closed_set1;apply:hausdorff_accessible;exact:metric_hausdorff.
  have hSame:A j = [set g:O|exists beta,rotated g beta /\
      @analytic_prefix_germ_subring R X NX hNX n e he omega j (ltn_ord j) beta /\beta<>0].
    rewrite -(analytic_coordinate_subring_family_member hQ (ltn_ord j)).
    apply/seteqP;split=>g.
    + move/(analytic_reduction_A_membership hLoci j g)=>[_ h];exact:h.
    + move=>h;apply/(analytic_reduction_A_membership hLoci j g);split=>//;by rewrite hPositive.
  rewrite hSame.
  exact:(@analytic_rotated_prefix_open_incidence_compact_cover R X B hB n e he omega hDual
    I j (ltn_ord j) (~` [set (0:G)]) hI hOpen).
- have hEmpty:A j = set0.
    apply/seteqP;split=>g;last by [].
    move/(analytic_reduction_A_membership hLoci j g)=>[h _];by rewrite hPositive in h.
  rewrite hEmpty;exists (fun _=>set0);constructor.
  + move=>_;exact:compact0.
  + by move=>i x [].
  + by move=>i k hIK x [].
  + by move=>x [].
Qed.

(** Source for [analytic_reduction_actual_B_compact_cover]: every
    original B_j is a countable compact union, as stated in the
    proof of Federer 3.4.8(5), p. 328. Its positive directional-jet
    condition remains exactly the original open condition. *)
Theorem analytic_reduction_actual_B_compact_cover j:
  exists K:nat->set O,is_increasing_compact_cover (Bj j) K.
Proof.
have hSame:Bj j = [set g:O|exists beta,rotated g beta /\
    @analytic_prefix_germ_subring R X NX hNX n e he omega (j:nat).+1 (ltn_ord j) beta /\
    has_nonzero_analytic_directional_jet beta (e j)].
  rewrite -(analytic_coordinate_subring_family_member hQ (ltn_ord j)).
  apply/seteqP;split=>g.
  - exact:(analytic_reduction_B_membership hLoci j g).1.
  - exact:(analytic_reduction_B_membership hLoci j g).2.
rewrite hSame.
exact:(@analytic_rotated_prefix_open_incidence_compact_cover R X B hB n e he omega hDual
  I (j:nat).+1 (ltn_ord j) [set beta|has_nonzero_analytic_directional_jet beta (e j)] hI
  (@analytic_positive_directional_jet_open R X NX hNX (e j))).
Qed.

(** Source for [analytic_reduction_actual_C_compact_cover]: every
    original C_m is a countable compact union, as stated in the
    proof of Federer 3.4.8(5), p. 328. Keep each original coordinate
    denominator and relation, and combine their covers at one finite index. *)
Theorem analytic_reduction_actual_C_compact_cover m:
  exists K:nat->set O,is_increasing_compact_cover (C m) K.
Proof.
pose F:=fun j:'I_n=>[set g:O|exists delta L,
  @analytic_prefix_germ_subring R X NX hNX n e he omega m (ltnW (ltn_ord m)) delta /\
  ~rotated g delta /\
  @analytic_prefix_germ_subring R X NX hNX n e he omega (m:nat).+1 (ltn_ord m) L /\
  rotated g (delta*gamma j-L)].
have hEach j:exists K:nat->set O,is_increasing_compact_cover (F j) K.
  exact:(@analytic_rotated_coordinate_relation_compact_cover R X B hB n e he omega hDual
    I m (ltn_ord m) (gamma j) hI).
have [K hK]:=choice hEach.
have hCompact:@compact O setT:=@orthogonal_group_compact_space R X B hB n e he.
have hHausdorff:hausdorff_space O.
  have [mul [inv [unit hGroup]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
  exact:(lch_group_hausdorff (@orthogonal_group_lch R X B hB n e he mul inv unit hGroup)).
have hSame:C m = [set g:O|forall j:'I_n,(m<=j)%N ->F j g].
  apply/seteqP;split=>g.
  - move/(analytic_reduction_C_membership hLoci m g)=>h j hJ.
    have hh:=h j hJ.
    by rewrite (analytic_coordinate_subring_family_member hQ (ltnW (ltn_ord m)))
      (analytic_coordinate_subring_family_member hQ (ltn_ord m)) in hh.
  - move=>h;apply/(analytic_reduction_C_membership hLoci m g)=>j hJ.
    have hh:=h j hJ.
    by rewrite (analytic_coordinate_subring_family_member hQ (ltnW (ltn_ord m)))
      (analytic_coordinate_subring_family_member hQ (ltn_ord m)).
rewrite hSame.
exists (fun k=>[set g:O|forall j:'I_n,(m<=j)%N ->K j k g]).
exact:(@increasing_compact_cover_finite_intersection O (Finite.clone 'I_n _)
  [set j|(m<=j)%N] F K hCompact hHausdorff hK).
Qed.
End Covers.
