(** Federer (1969), 3.4.8(5), p. 328:
    the denominator and polynomial relation incidence
    used in C_m is Borel. The original prefix
    subrings and ideal are proved closed; actual
    inverse orthogonal pullback gives the continuous
    membership tests. Both germ witnesses retain
    their proved compact covers. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HomInner LinearGroupTopology
  HilbertFormCompactness LinearBasis OrthogonalGroupTopology OrthogonalGroupHaarMeasure TopologicalGroupUP
  AnalyticGermUP AnalyticGermRing AnalyticGermMetric CommutativeIdealUP AnalyticGermIdealClosed
  AnalyticPrefixGermSubring AnalyticRotatedGermIdeal AnalyticOrthogonalPullback
  AnalyticOrthogonalInverseJointContinuity AnalyticCoordinateRelationContinuity AnalyticGermCompactCover
  IncreasingCompactCoverPair QuadrupleIncidenceClosed CompactCoverIncidenceBorel TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_rotated_coordinate_relation_borel]:
    the original C_m relation for one coordinate
    is Borel in the original orthogonal group,
    as required in 3.4.8(5), p. 328. The
    fixed coordinate germ may be arbitrary for this
    supporting assertion; neither Borelness nor closedness
    of the original ideal is assumed. *)
Theorem analytic_rotated_coordinate_relation_borel
  (R:realType) (X:lmodType R) (B:X->X->R) (hB:is_inner_product B)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o)
  (hDual:forall i k,omega i (e k)=if i==k then 1 else 0)
  (I:set (@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0))
  m (hmn:(m<n)%N)
  (gamma:@analytic_germ_ring R X (inner_norm hB) (inner_norm_real_norm hB) 0):
  is_commutative_ideal I ->
  borel_set [set g:@orthogonal_group R X B hB n e he|exists delta L,
    @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
      n e he omega m (ltnW hmn) delta /\
    ~@analytic_rotated_germ_ideal R X B hB n e he I g delta /\
    @analytic_prefix_germ_subring R X (inner_norm hB) (inner_norm_real_norm hB)
      n e he omega m.+1 hmn L /\
    @analytic_rotated_germ_ideal R X B hB n e he I g (delta*gamma-L)].
Proof.
move=>hI.
pose NX:=inner_norm hB;pose hNX:=inner_norm_real_norm hB.
pose M:=@analytic_germ_metric R X NX hNX 0.
pose G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
pose O:=@orthogonal_group R X B hB n e he.
pose T:=(M*M)%type.
pose Z:=[the pseudoMetricType R of ((M*M)*(M*M))%type].
pose Qm:=@analytic_prefix_germ_subring R X NX hNX n e he omega m (ltnW hmn).
pose Qnext:=@analytic_prefix_germ_subring R X NX hNX n e he omega m.+1 hmn.
have hClosedI:@closed M I:=@finite_analytic_germ_ideal_closed R X NX hNX n e he 0 I hI.
have hClosedM:@closed M Qm:=@analytic_prefix_germ_subring_closed R X NX hNX n e he omega m (ltnW hmn) hDual.
have hClosedNext:@closed M Qnext:=@analytic_prefix_germ_subring_closed R X NX hNX n e he omega m.+1 hmn hDual.
have [inv [hInv [hLeft [hRight hInverse]]]]:=@analytic_orthogonal_continuous_inverse_exists R X B hB n e he.
pose F:=fun p:T*O=>((p.1.1,p.1.2),
  ((@analytic_orthogonal_germ_map R X B hB n e he (inv p.2)
    ((p.1.1:G)*gamma-(p.1.2:G)):M),
   (@analytic_orthogonal_germ_map R X B hB n e he (inv p.2) p.1.1:M))).
pose Q:set Z:=fun z=>Qm z.1.1 /\Qnext z.1.2 /\I z.2.1.
pose V:set Z:=fun z=>~I z.2.2.
have [hClosedQ hOpenV]:=@quadruple_incidence_closed_open M Qm Qnext I I
  hClosedM hClosedNext hClosedI hClosedI.
have hF:continuous F:=@analytic_coordinate_relation_map_continuous R X B hB n e he inv gamma hInverse.
have [K hK]:=@analytic_germ_increasing_compact_cover_exists R X NX hNX 0 n e he.
have hPairCover:=@increasing_compact_cover_pair M M setT setT K K hK hK.
have hCompact:@compact O setT:=@orthogonal_group_compact_space R X B hB n e he.
have hHausdorff:hausdorff_space O.
  have [mul [inverse [unit hGroup]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
  exact:(lch_group_hausdorff (@orthogonal_group_lch R X B hB n e he mul inverse unit hGroup)).
have hBorel:=@compact_cover_incidence_borel R T O Z (setT `*` setT)
  (fun k=>K k `*` K k) F Q V hPairCover hCompact hHausdorff hF hClosedQ hOpenV.
have hSame:[set g:O|exists delta L,Qm delta /\
    ~@analytic_rotated_germ_ideal R X B hB n e he I g delta /\Qnext L /\
    @analytic_rotated_germ_ideal R X B hB n e he I g (delta*gamma-L)] =
    [set g:O|exists p:T,(setT `*` setT) p /\Q (F (p,g)) /\V (F (p,g))].
  apply/seteqP;split.
  - move=>g [delta [L [hDelta [hNot [hL hRelation]]]]].
    exists (delta,L);split;first by split.
    split.
    + split=>//;split=>//.
      exact:(@analytic_rotated_germ_ideal_inverse_membership R X B hB n e he I g
        (inv g) (hLeft g) (hRight g) (delta*gamma-L)).1 hRelation.
    + move=>hMember;apply:hNot.
      exact:(@analytic_rotated_germ_ideal_inverse_membership R X B hB n e he I g
        (inv g) (hLeft g) (hRight g) delta).2 hMember.
  - move=>g [[delta L] [_ [[hDelta [hL hRelation]] hNot]]].
    exists delta,L;split=>//;split.
    + move=>hMember;apply:hNot.
      exact:(@analytic_rotated_germ_ideal_inverse_membership R X B hB n e he I g
        (inv g) (hLeft g) (hRight g) delta).1 hMember.
    + split=>//.
      refine ((@analytic_rotated_germ_ideal_inverse_membership R X B hB n e he I g
        (inv g) (hLeft g) (hRight g) ((delta:G)*gamma-(L:G))).2 _).
      exact:hRelation.
rewrite hSame;exact:hBorel.
Qed.
