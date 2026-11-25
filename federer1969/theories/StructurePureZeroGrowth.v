(** Federer (1969), 3.3.8, p. 295: ordinary vanishing cone
    growth forces nullity of the original purely unrectifiable source. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureConeUP StructureProjectionKernel StructurePlaneGrowth StructureZeroApertureCutoffs
  StructureConeCostBounds StructureSmallZeroGrowthNull StructureConeDensityValues
  EuclideanMetricSeparability MetricClosedSmallCover RectifiableSetUP PureUnrectifiableLaws
  MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_3_8]: COMPLETE Federer 3.3.8, p. 295.
    For the original arbitrary purely (phi,m) unrectifiable B,
    original orthogonal projection and standing closed-measurable
    outer measure, an ordinary zero aperture limit of the original
    radius supremum at some positive cutoff for every original
    source point implies phi(B)=0. The cutoff may depend on the
    point. All natural 0<=m<=n remain; no measurability, finite-mass,
    uniform-cutoff or zero-mass premise is added. *)
Theorem federer_3_3_8 (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  is_structure_measure phi ->is_purely_measure_m_unrectifiable phi m B ->
  (forall x,B x ->structure_plane_zero_growth m phi B x (structure_projection_kernel hmn p)) ->
  phi B=0%E.
Proof.
move=>hStructure hPure hGrowth.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose B0 i:set X:=[set x|B x /\
  structure_zero_aperture_at hmn phi B p x (((i.+1)%:R:R)^-1)].
have hUnion:B=\bigcup_i B0 i.
  apply/seteqP; split=>x.
  - move=>hx; have [i hi]:=@structure_zero_growth_reciprocal_cutoff R n m hmn phi B p x
      (hGrowth x hx).
    exists i=>//; by split.
  - by move=>[i _ [hx _]].
rewrite hUnion; apply (@measure_null_countable_union R [the choiceType of X]
  [the choiceType of (nat : Type)] phi hStructure.1 setT B0 (countableP setT))=>i _.
pose delta:=(((i.+1)%:R:R)^-1).
have hDelta:0<delta by rewrite /delta invr_gt0 ltr0n.
have hHalf:=structure_density_positive_half_bounds hDelta.
have [D [hD hDense]]:=@euclidean_metric_separable R n.
have [F [hF hCover]]:=@separable_closed_small_cover_allow_empty R X D setT (delta/2)
  hD hDense closedT (andP hHalf).1.
pose E j:=B0 i `&` F j.
have hPieces:B0 i=\bigcup_j E j.
  apply/seteqP; split=>x.
  - move=>hx; have hWhole:(\bigcup_j F j) x by rewrite -hCover.
    have [j _ hj]:=hWhole; exists j=>//; by split.
  - by move=>[j _ [hx _]].
rewrite hPieces; apply (@measure_null_countable_union R [the choiceType of X]
  [the choiceType of (nat : Type)] phi hStructure.1 setT E (countableP setT))=>j _.
have hEB:E j `<=` B by move=>x [[hx _] _].
have hPureE:=pure_unrectifiable_subset hEB hPure.
have hDiameter x y:E j x ->E j y ->mdist x y<=delta/2.
  move=>[_ hx] [_ hy]; exact:(hF j).2.2 x y hx hy.
apply:(@structure_small_zero_aperture_null R n m hmn phi (E j) p (delta/2) delta
  hStructure hPureE (ltW (andP hHalf).1) (andP hHalf).2 hDiameter).
move=>x [[hx hZero] _] b hb; have [t [ht hTail]]:=hZero b hb.
exists t; split=>// r s hr /andP [hs hst].
have hstBoth:0<s<t by apply/andP; split.
have hER:0<r:=(andP hr).1.
exact:le_trans (@structure_cone_cost_subset R n m hmn phi (E j) B p x r s
  hStructure.1 hEB hER hs) (hTail r s hr hstBoth).
Qed.
