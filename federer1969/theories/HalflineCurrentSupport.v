(** Federer (1969), 4.1.7, p. 359:
    the original example has support exactly
    (0,b] in U=(0,infinity). Open restrictions
    below b are the already proved
    nonzero Euclidean current. The boundary point
    b belongs to the support by the
    original boundary-support inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology num_normedtype.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormDifferentialUP NormBoundedLinearTopology NormOpenTopology
  InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanOneCoordinate
  FiniteExteriorPowers AlternatingForms AlternatingPairing AlternatingIsomorphism CurrentSpaces CurrentCoefficientNorms CurrentSupportGeometry
  FunctionalSupportUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation CurrentOpenRestriction
  CurrentOpenRestrictionLocality CurrentOpenConstantDensity EuclideanFundamentalCurrentNonzero HalflineOpenRestriction
  HalflineCurrents HalflineCurrentBoundary CurrentBoundary CurrentBoundarySupport DiracCurrentBounds CurrentDirac
  EuclideanDistributionMeasureContext EuclideanLebesgueDimensions MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP LatticeL1ApproximationLaws RealSubsetIntegralGraph.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section HalflineCurrentSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X := (R_n R 1).
Local Notation NX := (inner_norm (@euclidean_inner_productP R 1)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R 1)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation U := (@current_halfline_domain R).
Local Notation hU := (@current_halfline_domain_open R).
Local Notation Y := (A_m X R^o 1).
Local Notation DT := (@current_test_space R h2 1 U hU 1%N).
Local Notation value := (@current_test_value R h2 1 U hU 1%N).
Local Notation mu := (@euclidean_lebesgue_measure R 1).
Local Notation hm := (euclidean_lebesgue_is_measure R 1).
Local Notation top := (e_lambda (@coordinate_basis R 1) (ord_tuple 1)).
Local Notation T := (fun b=>@halfline_current R h2 b).
Local Notation support := (fun b=>@current_support R h2 1 U hU 1%N (T b)).

(** Source for [halfline_support_coordinate_continuous]:
    the original Euclidean line coordinate is
    continuous in its actual source norm,
    supporting the open support regions in
    Federer 4.1.7, p. 359. *)
Lemma halfline_support_coordinate_continuous:
  continuous (fun x:XT=>(x ord0:real_line_metric R)).
Proof.
move=>x.
exact (@continuous_comp XT
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R 1)]
  [the topologicalType of real_line_metric R] (fun z=>z) (@euclidean_one_project R) x
  (@euclidean_distribution_norm_to_inner R 1 x) (@euclidean_one_project_continuous R x)).
Qed.

(** Source for [halfline_current_support_upper]:
    the actual current has no support
    above b or outside U, supporting
    Federer 4.1.7, p. 359. The
    original integral vanishes on tests supported
    in the upper open ray. *)
Theorem halfline_current_support_upper b:support b `<=` [set x:X|0<x ord0<=b].
Proof.
move=>x hx;apply/andP;split;first exact:hx.1.
apply:contrapT=>hNot.
have hAbove:b<x ord0 by rewrite ltNge;exact/negP.
pose W:set X:=[set z|b<z ord0].
have hW:@open XT W.
  change (@open XT ((fun z:XT=>(z ord0:real_line_metric R))
    @^-1` [set t:real_line_metric R|b<t])).
  apply:open_comp;last exact:(@open_gt R b).
  by move=>z _;exact:halfline_support_coordinate_continuous.
have hZero:forall phi:DT,@current_test_support R h2 1 1%N U hU phi `<=` W->
    @current_value R h2 1 U hU 1%N (T b) phi=0.
  move=>phi hPhi.
  have hZeroOn (z:X):(0<z ord0<=b)->pairing top (value phi z)=0.
    move=>/andP [hz0 hzb].
    have hValue:value phi z=0.
      apply:contrapT=>hNo.
      have hSupp:=@smooth_function_nonzero_in_support R X Y NX hNX U DT value phi z hz0 hNo.
      have hBound:b<z ord0:=hPhi z hSupp.
      by have:=lt_le_trans hBound hzb;rewrite ltxx.
    by rewrite hValue /pairing linear0 hom_zeroE.
  have hIntegral:=@halfline_current_action R h2 b phi.
  have hTotal:=(@real_subset_integral_total R X mu [set z:X|0<z ord0<=b]
    (fun z=>pairing top (value phi z)) (fun _=>0) _
    (fun z hz=>esym (@hZeroOn z hz)) (fun _ _=>erefl)).1 hIntegral.
  exact:(EFin_inj (measure_integral_unique hTotal (@real_total_zero_integral R X mu hm))).
apply:hx.2;exists W;split;last exact:hAbove.
by split.
Qed.

(** Source for [halfline_current_support_interior]:
    every point of (0,b) belongs to
    the actual current support, supporting
    Federer 4.1.7, p. 359. An
    annihilation neighbourhood would give zero open
    restriction, contradicting the already proved
    nonzero Euclidean current on that region. *)
Theorem halfline_current_support_interior b (x:X):0<x ord0->x ord0<b->support b x.
Proof.
move=>hx0 hxb;split;first exact:hx0.
move=>[W [[hW hAnnihilation] hWx]].
pose A:set X:=[set z|W z /\0<z ord0 /\z ord0<b].
have hAOpen:@open XT A.
  have hPositive:@open XT [set z:X|0<z ord0].
    change (@open XT ((fun z:XT=>(z ord0:real_line_metric R))
      @^-1` [set t:real_line_metric R|0<t])).
    apply:open_comp;last exact:(@open_gt R 0).
    by move=>z _;exact:halfline_support_coordinate_continuous.
  have hBelow:@open XT [set z:X|z ord0<b].
    change (@open XT ((fun z:XT=>(z ord0:real_line_metric R))
      @^-1` [set t:real_line_metric R|t<b])).
    apply:open_comp;last exact:(@open_lt R b).
    by move=>z _;exact:halfline_support_coordinate_continuous.
  exact:(openI hW (openI hPositive hBelow)).
have hA:forall z,A z->norm_domain_interior NX A z.
  move=>z hz;apply:(@norm_domain_interior_neighbourhood R X NX hNX A z).2.
  exact:open_nbhs_nbhs (conj hAOpen hz).
have hAU:forall z,A z->U z by move=>z hz;exact:hz.2.1.
have hAb:forall z,A z->z ord0<=b by move=>z hz;exact:ltW hz.2.2.
have hNonzero:=@euclidean_fundamental_current_open_nonzero R h2 1 A hA
  (ex_intro _ x (conj hWx (conj hx0 hxb))).
have hEquality:=@halfline_current_open_restriction R h2 b A hA hAU hAb.
have hZero:=@current_open_restriction_annihilation R h2 1 1%N A U hA hU hAU (T b) W
  (fun z hz=>hz.1) (conj hW hAnnihilation).
apply:hNonzero;rewrite -hEquality;exact:hZero.
Qed.

(** Source for [halfline_current_support_endpoint]:
    the original endpoint b belongs to
    spt T because boundary T=delta_b and
    boundary support lies in current support,
    supporting Federer 4.1.7, p. 359. *)
Theorem halfline_current_support_endpoint b:0<b->support b (euclidean_one_embed b).
Proof.
move=>hb.
have hPoint:U (euclidean_one_embed b) by change (is_true (0<euclidean_one_project (euclidean_one_embed b)));
  rewrite euclidean_one_embedK;exact:hb.
apply:(@current_boundary_support_subset R h2 1 0%N U hU (T b) (euclidean_one_embed b)).
rewrite halfline_current_boundary (@dirac_current_support R h2 1 U hU (euclidean_one_embed b) hPoint).
by [].
Qed.

(** Source for [halfline_current_support_exact]:
    the actual original example has support
    exactly (0,b], Federer 4.1.7, p. 359.
    The endpoint 0 remains outside the
    source domain and its support. *)
Theorem halfline_current_support_exact b:0<b->support b=[set x:X|0<x ord0<=b].
Proof.
move=>hb;apply/seteqP;split;first exact:halfline_current_support_upper.
move=>x /andP [hx0 hxb].
case:(ltP (x ord0) b)=>hStrict.
- exact:(@halfline_current_support_interior b x hx0 hStrict).
- have hEqual:x ord0=b by apply/eqP;rewrite eq_le hxb hStrict.
  have hX:x=euclidean_one_embed b.
    rewrite -[x](@euclidean_one_projectK R x) /euclidean_one_project hEqual;by [].
  rewrite hX;exact:(@halfline_current_support_endpoint b hb).
Qed.
End HalflineCurrentSupport.
