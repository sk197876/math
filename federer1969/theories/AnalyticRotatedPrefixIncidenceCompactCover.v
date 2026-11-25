(** Strengthening the existing Borel proof by retaining its actual
    countable compact cover; the original incidence conditions are unchanged. *)
(** Federer (1969), 3.4.8(5), p. 328:
    an original rotated ideal has sigma-compact incidence with
    a coordinate subring and an open germ condition.
    Actual compact ideal covers, joint orthogonal pullback
    continuity and closed coordinate images prove the result. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure TopologicalGroupUP
  AnalyticGermUP AnalyticGermRing AnalyticGermMetric CommutativeIdealUP
  AnalyticIdealCompactCover AnalyticPrefixGermSubring AnalyticOrthogonalPullback
  AnalyticOrthogonalJointContinuity AnalyticRotatedGermIdeal CompactCoverIncidenceCompactCover TopologicalBorel IncreasingCompactCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_prefix_open_incidence_compact_cover]:
    retain the actual compact covers of the existing incidence
    projection for the original A_j
    and B_j of 3.4.8(5), p. 328. Compactness
    of the ideal witnesses and closedness of Q_j are
    proved for the original objects, rather than supplied
    as extra hypotheses. *)
Theorem analytic_rotated_prefix_open_incidence_compact_cover
    (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
    n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
    (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
    (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
    j (hjn:(j<=n)%N)
    (V:set (@analytic_germ_metric R X (inner_norm hB) (inner_norm_real_norm hB) 0)):
  is_commutative_ideal I ->open V ->
  exists L:nat->set (@orthogonal_group R X B hB n e he),
    is_increasing_compact_cover [set g:@orthogonal_group R X B hB n e he|exists beta,
    @analytic_rotated_germ_ideal R X B hB n e he I g beta /\
    @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
      n e he omega j hjn beta /\V beta] L.
Proof.
move=>hI hV.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose M:=@analytic_germ_metric R X NX hNX 0.
pose O:=@orthogonal_group R X B hB n e he.
pose Q:=@analytic_prefix_germ_subring R X NX hNX n e he omega j hjn.
pose F:=fun p:M*O=>(@analytic_orthogonal_germ_map R X B hB n e he p.2 p.1:M).
have [K hK]:=@analytic_ideal_increasing_compact_cover_exists R X NX hNX 0 n e I he hI.
have hCompact:@compact O setT:=@orthogonal_group_compact_space R X B hB n e he.
have hHausdorff:hausdorff_space O.
  have [mulS [invS [eS hS]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
  exact:(lch_group_hausdorff (@orthogonal_group_lch R X B hB n e he mulS invS eS hS)).
have hClosed:@closed M Q:=@analytic_prefix_germ_subring_closed R X NX hNX n e he omega j hjn hDual.
have hF:continuous F:=@analytic_orthogonal_germ_map_jointly_continuous R X B hB n e he.
have hIncidence:=@compact_cover_incidence_compact_cover R M O [the pseudoMetricType R of M]
  I K F Q V hK hCompact hF hClosed hV.
have hSame:
  [set g:O|exists beta,@analytic_rotated_germ_ideal R X B hB n e he I g beta /\Q beta /\V beta]=
  [set g:O|exists alpha:M,I alpha /\Q (F (alpha,g)) /\V (F (alpha,g))].
  apply/seteqP;split.
  - move=>g [beta [hRotated [hQ hOpen]]].
    have [alpha [hAlpha hEqual]]:=(
      @analytic_rotated_germ_ideal_membership R X B hB n e he I g beta).1 hRotated.
    exists alpha;split;first exact:hAlpha.
    by rewrite /F hEqual.
  - move=>g [alpha [hAlpha [hQ hOpen]]].
    exists (F (alpha,g));split;last by split.
    apply/(@analytic_rotated_germ_ideal_membership R X B hB n e he I g (F (alpha,g))).
    exists alpha;by split.
rewrite hSame;exact:hIncidence.
Qed.
