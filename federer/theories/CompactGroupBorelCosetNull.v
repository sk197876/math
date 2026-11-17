(** Federer (1969), 3.4.12, p. 339, extending the Haar/Fubini
    step of 3.4.8(7),(9), pp. 329–330: a Borel exceptional
    set with null translated sections has null Haar measure. Reuse
    the existing coset-null averaging theorem and its established
    Radon, product-measure and right-invariance connections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  constructive_ereal topology subtype_topology.
From Federer Require Import ContinuousCommonPair TopologicalGroupUP TopologicalGroupLaws TopologicalProductMaps
  HaarIntegralUP HaarIntegralLaws CompactGroupHaarNormalisation GroupMultiplicationHomogeneous
  InvariantMeasureTranslates CompactSupportCountableRadon RadonBorelRegularity CountableOpenBaseUP
  MeasureUP MeasureBasic MeasureSplit MeasurePushforward BorelRegularMeasureUP TopologicalBorel
  ContinuousBorelPreimages CountablyMeasurableBasic ProductMeasure ProductBorelRegularity StructureCosetNullAveraging.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Average.
Variable R:realType.
Variables G H:topologicalType.
Variables (mulG:G->G->G) (invG:G->G) (unitG:G).
Variables (mulH:H->H->H) (invH:H->H) (unitH:H).
Variable hG:is_locally_compact_hausdorff_group mulG invG unitG.
Variable hH:is_locally_compact_hausdorff_group mulH invH unitH.
Variable hCompactG:compact (@setT G).
Variables (U:nat->set G) (V:nat->set H).
Variables (hU:is_countable_open_base U) (hV:is_countable_open_base V).
Variable inclusion:H->G.
Variable hInclusion:continuous inclusion.
Variables (theta:set G->\bar R) (beta:set H->\bar R).

(** Source for [compact_group_borel_coset_null]: the actual
    compact-group Borel averaging connection used for the complex
    unitary reduction loci, 3.4.12, p. 339. *)
Theorem compact_group_borel_coset_null (Bad:set G):
  is_normalised_haar_measure mulG theta ->is_normalised_haar_measure mulH beta ->
  borel_set Bad ->(forall g:G,beta [set h:H|Bad (mulG g (inclusion h))]=0%:E) ->theta Bad=0%:E.
Proof.
move=>hTheta hBeta hBad hCosets.
have [lambda [hLambda hMu hRepMu hRegularMu]]:=hTheta.1.
have [eta [hEta hNu hRepNu hRegularNu]]:=hBeta.1.
have hMuRadon:=@compact_support_regular_countable_base_radon R G theta lambda hMu hRepMu hRegularMu U
  (lch_group_hausdorff hG) (lch_group_locally_compact hG) hU.
have hNuRadon:=@compact_support_regular_countable_base_radon R H beta eta hNu hRepNu hRegularNu V
  (lch_group_hausdorff hH) (lch_group_locally_compact hH) hV.
have hMuBorel:=radon_borel_regular hMu hMuRadon.
have hNuBorel:=radon_borel_regular hNu hNuRadon.
have hProduct:=product_measure_is_measure hMu hNu.
have hProductBorel:=product_measure_borel_regular hMu hNu hU hV hMuBorel hNuBorel.
have hSecond:continuous (fun z:G*H=>inclusion z.2).
  move=>z.
  have hTmp:=@continuous_comp (G*H)%type H G snd inclusion z
    (@second_projection_continuous G H z) (@hInclusion z.2).
  exact:hTmp.
have hPair:=@continuous_common_domain_pair (G*H)%type G G fst (fun z=>inclusion z.2)
  (@first_projection_continuous G H) hSecond.
have hJoint:continuous (fun z:G*H=>mulG z.1 (inclusion z.2)).
  have hMul:continuous (fun q:G*G=>mulG q.1 q.2):=topological_group_mul_continuous (lch_group_topological hG).
  move=>z;exact:(@continuous_comp (G*H)%type (G*G)%type G
    (fun z:G*H=>(z.1,inclusion z.2)) (fun q:G*G=>mulG q.1 q.2) z
    (hPair z) (hMul (z.1,inclusion z.2))).
pose Incidence:set (G*H):=[set z|Bad (mulG z.1 (inclusion z.2))].
have hMeasurable:measure_measurable (product_measure hMu hNu) Incidence.
  exact:(borel_regular_borel_measurable hProduct hProductBorel (continuous_borel_preimage hJoint hBad)).
have hFinite:(product_measure hMu hNu Incidence< +oo)%E.
  have hCover:Incidence `<=` (@setT G) `*` (@setT H) by move=>z _;split.
  have hBound:=le_trans (measure_mono hProduct hCover)
    (@product_measure_rectangle_bound R G H theta beta hMu hNu setT setT
      (measure_measurable_whole hMu) (measure_measurable_whole hNu)).
  rewrite hTheta.2 hBeta.2 mul1e in hBound.
  exact:(le_lt_trans hBound (ltry 1%R)).
have hCount:=finite_measurable_set_countably_measurable hMeasurable hFinite.
have hPositive:(0<beta setT)%E by rewrite hBeta.2 lte_fin ltr01.
have hRight:=normalised_haar_measure_right hG hCompactG hTheta.
have hInvariant:=nonzero_invariant_measure_invariant hRight.
have hTop:=lch_group_topological hG.
have hGroup:=topological_group_laws hTop.
have hOriginal (h:H):theta [set g:G|Bad (mulG g (inclusion h))] = theta Bad.
  have hLaw:=invariant_measure_preimage hGroup (right_multiplication_homogeneous hTop)
    hInvariant (invG (inclusion h)) Bad.
  change (theta ((fun g:G=>mulG g (invG (invG (inclusion h)))) @^-1` Bad) = theta Bad) in hLaw.
  by rewrite (group_invK hGroup) in hLaw.
exact:(@structure_coset_null_average R (Choice.clone G _) (Choice.clone H _) theta beta hMu hNu
  (fun g h=>mulG g (inclusion h)) Bad hPositive hCount hCosets hOriginal).
Qed.
End Average.
