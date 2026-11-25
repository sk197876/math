(** Federer (1969), 4.1.25, p. 383, first display:
    the Lipschitz image of Lebesgue wedge xi acts by
    integrating the actual exterior differential image of xi.
    Follow the printed proof: apply the smooth case to
    the bounded approximants of 4.1.2, then use 2.4.9.
    The formula uses the original partial differential domain.
    Normality, full rank and a nonzero Jacobian are not
    hypotheses. The general degree exposes the same proof;
    the printed top-source case is k=m. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading ExteriorMaps
  AlternatingForms AlternatingPairing CurrentSpaces CurrentCoefficientNorms
  CurrentMapDifferential LipschitzUP LipschitzBasic SmoothCompactSet
  SmoothTestSpaces SmoothTestEvaluation FlatCurrentsUP CurrentLipschitzCompactImage
  CurrentCompactPushforwardAlgebra CurrentSmoothApproximationUP
  CurrentFlatLipschitzPushforwardSealed CurrentWeakSequenceLimit
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CompactSummableMultivectorAmbient EuclideanLebesgueDimensions
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialAbsolutePartsGraph
  PartialExtendedOrderLoci SummableRealFunctionUP SummableRealArithmetic
  RealErrorOrderLimit CurrentLipschitzLebesgueActionDensity
  CurrentLipschitzLebesgueActionIntegrand CurrentLipschitzLebesgueActionApproximation
  CurrentLipschitzLebesgueActionSmooth CurrentLipschitzLebesgueActionFamilyUP
  CurrentLipschitzLebesgueActionFamilySealed CurrentLipschitzLebesgueActionBound
  CurrentLipschitzLebesgueActionPointwise CurrentLipschitzLebesgueActionTestBound
  CurrentLipschitzLebesgueActionDominatedLimit
  MeasureIntegralUP
  NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LipschitzLebesgueAction.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation FullX := (fun _ : X=>True).
Local Notation FullY := (fun _ : Y=>True).
Local Notation hFullX := (fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation hFullY := (fun (y:Y) (_:True)=>norm_full_domain_interior NY y).
Local Notation MX := (@current_vector_mass R h2 m k).
Local Notation QN := (@current_form_comass R h2 n k).
Local Notation hQN := (@current_form_comass_real_norm R h2 n k).
Local Notation mu := (@euclidean_lebesgue_measure R m).
Local Notation hm := (euclidean_lebesgue_is_measure R m).
Variable xi : @compact_summable_multivector_space R h2 m k FullX hFullX.
Local Notation raw := (@compact_summable_multivector_ambient_value R h2 m k FullX hFullX xi).
Local Notation T := (@compact_summable_multivector_current R h2 m k FullX hFullX xi).
Local Notation hFlat := (@current_lipschitz_lebesgue_action_density_flat
  R h2 m k FullX hFullX xi).
Variable f : X->Y.
Hypothesis hLip : @is_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) setT f.
Local Notation hLocal := (@metric_lipschitz_is_local R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) setT f hLip).
Local Notation hImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation Q := (@CurrentFlatLipschitzPushforward.value R h2 m n k
  FullX FullY hFullX hFullY f hImage hLocal T hFlat).
Local Notation testValue := (@current_test_value R h2 n FullY hFullY k).

(** Source for [current_lipschitz_lebesgue_action]: the first
    displayed action in 4.1.25, p. 383, with the
    printed top-source specialization k=m. The actual opaque
    Lipschitz image and actual original Lebesgue integral are
    identified; the original differentiability domain includes
    critical points and all zero-dimensional endpoints. *)
Theorem current_lipschitz_lebesgue_action
    (phi:@current_test_space R h2 n FullY hFullY k) :
  is_measure_integral mu
    (@current_lipschitz_lebesgue_action_integrand R m n k f raw (testValue phi))
    (@current_value R h2 n FullY hFullY k Q phi)%:E.
Proof.
have [L [hL hLipschitz]]:=hLip.
have hPair x y:NY (f x-f y)<=L*NX (x-y).
  exact:hLipschitz.2 x y Logic.I Logic.I.
pose g:=@CurrentLipschitzLebesgueActionFamily.value R m n f L hLipschitz.1 hPair.
have hFamily:=@CurrentLipschitzLebesgueActionFamily.laws R m n f L hLipschitz.1 hPair.
have [K hK]:=hFlat.
pose hCompact:=@flat_supported_current_compact R h2 m k FullX hFullX K T hK.
have hG:@is_current_smooth_approximation R m n FullX FullY K f g.
  constructor.
  - by move=>i x _.
  - exact:current_lipschitz_lebesgue_action_family_smooth hFamily.
  - exists L;split;first exact:hLipschitz.1.
    move=>i x _;exact:current_lipschitz_lebesgue_action_family_differential_bound hFamily i x.
  - move=>eta hEta.
    have [N hN]:=current_lipschitz_lebesgue_action_family_uniform hFamily hEta.
    exists N=>i hi x _;exact:hN i hi x.
have hWeak:=@current_lipschitz_lebesgue_action_image_approximation
  R h2 m n k xi f hLocal K hK g hG.
pose P i:=@current_compact_map_pushforward R h2 m n FullX FullY hFullX hFullY
  (g i) (current_smooth_approximation_image hG i)
  (current_smooth_approximation_class hG i) k T hCompact.
pose a i:=@current_value R h2 n FullY hFullY k (P i) phi.
pose F i:=real_total_integrand (fun x:X=>pairing
  (exterior_power_map
    (hom_as_linear (@current_map_differential R m n FullX (g i) x)) k (raw x))
  (testValue phi (g i x))).
have hActions i:is_measure_integral mu (F i) (a i)%:E.
  have h:=@current_lipschitz_lebesgue_action_smooth R h2 m n k xi (g i)
    (current_smooth_approximation_class hG i) phi.
  have hProof:@current_lipschitz_lebesgue_action_density_compact
      R h2 m k FullX hFullX xi=hCompact:=Prop_irrelevance _ _.
  have hImageProof:current_smooth_approximation_image hG i=hImage:=Prop_irrelevance _ _.
  rewrite hProof in h.
  rewrite /a /P hImageProof;exact:h.
have [B [hB hTestBound]]:=@current_lipschitz_lebesgue_action_test_bound R h2 n k phi.
pose H:=real_total_integrand (fun x:X=>(B*L^+k)*MX (raw x)).
have hH:is_measure_summable mu H.
  exists ((B*L^+k)*@compact_summable_multivector_size R h2 m k FullX hFullX xi).
  exact:(@real_total_integral_scale R X mu hm (fun x=>MX (raw x))
    (@compact_summable_multivector_size R h2 m k FullX hFullX xi) (B*L^+k)
    (@compact_summable_multivector_ambient_integral R h2 m k FullX hFullX xi)).
have hBound i:measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (F i)) H).
  apply:(@measure_almost_everywhere_mono R X mu hm setT _ _
    (measure_almost_everywhere_true hm))=>x _.
  pose v:=pairing
    (exterior_power_map
      (hom_as_linear (@current_map_differential R m n FullX (g i) x)) k (raw x))
    (testValue phi (g i x)).
  exists (`|v|)%:E,((B*L^+k)*MX (raw x))%:E.
  split.
  - exists v%:E;split;first by apply/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split;first by apply/real_total_integrand_graph.
    rewrite lee_fin mulrC.
    exact:(@current_lipschitz_lebesgue_action_family_pairing_bound
      R h2 m n k f L B g hFamily raw (testValue phi) hTestBound i x).
have hPhi:norm_class_zero NY QN FullY (testValue phi).
  exact:(norm_class_continuous
    (@smooth_test_value_smooth R Y (A_m Y R^o k) NY QN hNY hQN FullY
      (@current_smooth_space R h2 n FullY hFullY k)
      (@current_smooth_value R h2 n FullY hFullY k)
      (@current_smooth_space_laws R h2 n FullY hFullY k) phi 0%N)).
have hConvergence:=@current_lipschitz_lebesgue_action_integrands_ae_limit
  R h2 m n k f L g hLipschitz.1 hPair hFamily raw (testValue phi) hPhi.
have hValues:=real_error_extended_order_limit (hWeak phi).
exact:(@current_lipschitz_lebesgue_action_dominated_limit R X mu hm F
  (@current_lipschitz_lebesgue_action_integrand R m n k f raw (testValue phi))
  H a (@current_value R h2 n FullY hFullY k Q phi)
  hH hActions hBound hConvergence hValues).
Qed.
End LipschitzLebesgueAction.
