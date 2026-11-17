(** Federer (1969), 3.4.11, p. 338:
    the dimension argument applies 3.4.8(7), p. 329,
    to two actual ideals. This connection retains the
    original A locus of the first ideal and B
    locus of the second. Its conditional fibre premise
    is proved separately for actual leading Taylor ideals. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  LinearBasis OrthonormalFamilies HomInner OrthogonalGroupTopology OrthogonalGroupHaarMeasure
  LinearGroupTopology LinearGroupSealed TopologicalGroupUP TopologicalGroupLaws IsotropyGroupTopology
  TopologicalProductMaps HaarIntegralUP HaarIntegralLaws CompactGroupHaarNormalisation
  GroupMultiplicationHomogeneous InvariantMeasureTranslates CompactSupportCountableRadon RadonBorelRegularity
  MeasureUP MeasureBasic MeasureSplit MeasureAlmostUP MeasureAlmostBasic MeasurePushforward
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages CountablyMeasurableBasic
  ProductMeasure ProductBorelRegularity StructureCosetNullAveraging AnalyticGermRing CommutativeIdealUP
  AnalyticReductionActual AnalyticReductionActualBorel AnalyticReductionACosets AnalyticReductionHaarFibre
  OrthogonalCoordinateFixing OrthogonalCoordinateFixingHaar OrthogonalCoordinateCountableBase.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Difference.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable hON:orthonormal_family B e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i k,omega i (e k) = if i==k then 1 else 0.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Variable I:set G.
Hypothesis hI:is_commutative_ideal I.
Variable J:set G.
Hypothesis hJ:is_commutative_ideal J.
Variable j:'I_n.
Local Notation p:=((j:nat).+1).
Local Notation aIndex:=(@Ordinal n.+1 p (ltn_ord j)).
Local Notation H:=(@analytic_prefix_rotation_group R X B hB n e he p).
Local Notation A:=(@analytic_reduction_actual_A R X B hB n e he omega I aIndex).
Local Notation Bj:=(@analytic_reduction_actual_B R X B hB n e he omega J j).
Variables (mulO:O->O->O) (invO:O->O) (unitO:O).
Hypothesis hO:is_subgroup_restriction (@linear_group_mul R X B hB n e he)
  (@linear_group_inv R X B hB n e he) (@linear_group_unit R X B hB n e he) O mulO invO unitO.

Hypothesis hFibre:forall (mulH:H->H->H) (invH:H->H) (unitH:H),
  is_subgroup_restriction mulO invO unitO H mulH invH unitH ->
  forall (mu:set H->\bar R) (g:O),is_left_haar_measure mulH mu ->A g ->
    measure_almost_everywhere mu [set h:H|Bj (mulO g (set_val h))].

(** Source for [analytic_reduction_cross_ideal_haar_null]:
    the Haar comparison implicit in the dimension argument
    of 3.4.11, p. 338, using 3.4.8(7),
    p. 329. Only the conditional fibre connection
    changes; the original Borel, coset and Fubini results
    apply directly to the two actual ideals. *)
Theorem analytic_reduction_cross_ideal_haar_null (theta:set O->\bar R):
  is_normalised_haar_measure mulO theta ->theta (A `\` Bj) = 0%E.
Proof.
move=>hTheta.
pose Bad:set O:=A `\` Bj.
have hSubgroup:=@orthogonal_coordinate_fixing_subgroup R X B hB n e he mulO invO unitO hO
  [set i:'I_n|(p<=i)%N].
have [mulH [invH [unitH hH]]]:=subgroup_restriction_exists hSubgroup.
have [beta hBeta]:=@orthogonal_coordinate_fixing_haar_exists R X B hB n e he
  [set i:'I_n|(p<=i)%N] mulO invO unitO hO mulH invH unitH hH.
have [lambda [hLambda hMu hRepMu hRegularMu]]:=hTheta.1.
have [eta [hEta hNu hRepNu hRegularNu]]:=hBeta.1.
have hLCH:=@orthogonal_group_lch R X B hB n e he mulO invO unitO hO.
have hHLCH:=@orthogonal_coordinate_fixing_lch R X B hB n e he [set i:'I_n|(p<=i)%N]
  mulO invO unitO hO mulH invH unitH hH.
have [U hU]:=@finite_orthogonal_group_countable_base R X B hB n e he.
have [V hV]:=@orthogonal_coordinate_fixing_countable_base R X B hB n e he [set i:'I_n|(p<=i)%N].
have hMuRadon:=@compact_support_regular_countable_base_radon R O theta lambda hMu hRepMu hRegularMu U
  (lch_group_hausdorff hLCH) (lch_group_locally_compact hLCH) hU.
have hNuRadon:=@compact_support_regular_countable_base_radon R H beta eta hNu hRepNu hRegularNu V
  (lch_group_hausdorff hHLCH) (lch_group_locally_compact hHLCH) hV.
have hMuBorel:=radon_borel_regular hMu hMuRadon.
have hNuBorel:=radon_borel_regular hNu hNuRadon.
have hProduct:=product_measure_is_measure hMu hNu.
have hProductBorel:=product_measure_borel_regular hMu hNu hU hV hMuBorel hNuBorel.
have hPair:continuous (fun z:O*H=>(z.1,set_val z.2):O*O).
  apply:topological_pair_continuous;first exact:first_projection_continuous.
  move=>z;exact:(continuous_comp (@second_projection_continuous O H z)
    (@set_type_val_continuous O H z.2)).
have hJoint:continuous (fun z:O*H=>mulO z.1 (set_val z.2)).
  have hMul:continuous (fun q:O*O=>mulO q.1 q.2):=topological_group_mul_continuous (lch_group_topological hLCH).
  move=>z;exact:(@continuous_comp (O*H)%type (O*O)%type O
    (fun z:O*H=>(z.1,set_val z.2)) (fun q:O*O=>mulO q.1 q.2) z
    (hPair z) (hMul (z.1,set_val z.2))).
have hBad:borel_set Bad.
  exact:(borel_set_difference
    (@analytic_reduction_actual_A_borel R X B hB n e he omega hDual I hI aIndex)
    (@analytic_reduction_actual_B_borel R X B hB n e he omega hDual J hJ j)).
pose Incidence:set (O*H):=[set z|Bad (mulO z.1 (set_val z.2))].
have hMeasurable:measure_measurable (product_measure hMu hNu) Incidence.
  exact:(borel_regular_borel_measurable hProduct hProductBorel (continuous_borel_preimage hJoint hBad)).
have hFinite:(product_measure hMu hNu Incidence< +oo)%E.
  have hCover:Incidence `<=` (@setT O) `*` (@setT H) by move=>z _;split.
  have hBound:=le_trans (measure_mono hProduct hCover)
    (@product_measure_rectangle_bound R O H theta beta hMu hNu setT setT
      (measure_measurable_whole hMu) (measure_measurable_whole hNu)).
  rewrite hTheta.2 hBeta.2 mul1e in hBound.
  exact:(le_lt_trans hBound (ltry 1%R)).
have hCount:=finite_measurable_set_countably_measurable hMeasurable hFinite.
have hPositive:(0<beta setT)%E by rewrite hBeta.2 lte_fin ltr01.
have hCosets (g:O):beta [set h:H|Bad (mulO g (set_val h))] = 0%E.
  case:(pselect (A g))=>hA.
  - have hAlmost:=@hFibre mulH invH unitH hH beta g hBeta.1 hA.
    apply:(@measure_null_subset R (Choice.clone H _) beta hNu _ _ _ hAlmost).
    by move=>h [hFirst hNotSecond].
  - have hEmpty:[set h:H|Bad (mulO g (set_val h))] = set0.
      apply/seteqP;split;last by [].
      move=>h [hFirst hNotSecond];exfalso;apply:hA.
      exact:((@analytic_reduction_A_prefix_coset R X B hB n e he omega hDual I
        mulO invO unitO hO aIndex g (set_val h) (set_valP h)).1 hFirst).
    rewrite hEmpty;exact:measure_empty.
have hRight:=normalised_haar_measure_right hLCH (@orthogonal_group_compact_space R X B hB n e he) hTheta.
have hInvariant:=nonzero_invariant_measure_invariant hRight.
have hTop:=lch_group_topological hLCH.
have hGroup:=topological_group_laws hTop.
have hOriginal (h:H):theta [set g:O|Bad (mulO g (set_val h))] = theta Bad.
  have hLaw:=invariant_measure_preimage hGroup (right_multiplication_homogeneous hTop)
    hInvariant (invO (set_val h)) Bad.
  change (theta ((fun g:O=>mulO g (invO (invO (set_val h)))) @^-1` Bad) = theta Bad) in hLaw.
  by rewrite (group_invK hGroup) in hLaw.
exact:(@structure_coset_null_average R (Choice.clone O _) (Choice.clone H _) theta beta hMu hNu
  (fun g h=>mulO g (set_val h)) Bad hPositive hCount hCosets hOriginal).
Qed.
End Difference.
