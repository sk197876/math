(** Federer (1969), 3.2.31, p. 269: combine the purely
    unrectifiable target rank theorem 3.2.21, p. 257, with
    the proved critical-fibre estimate. Null source errors are
    controlled independently by the rough Chapter 2 estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP LinearRankUP LinearRankAtLeast LipschitzUP LipschitzBasic RectifiableSetUP
  PureUnrectifiableRank LipschitzCriticalFibreNull CountableNullFibreCover
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue EuclideanClosedBallCompact
  HausdorffMeasure HausdorffFibreCutoffs NullFibresProperSource TopologicalBorel
  MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section PureTargetNull.
Variable R:realType.
Variables m v:nat.
Local Notation X:=(inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation Y:=(inner_metric_space (@euclidean_inner_productP R v)).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation Leb:=(@euclidean_lebesgue_measure R m.+1).

(** Source for [pure_target_fibres_almost_null]: supporting
    exclusion of the purely unrectifiable part in Federer
    3.2.31, p. 269. Every source subset mapped into that
    Borel part has null complementary fibres almost everywhere.
    Neither source measurability nor finite mass is assumed.
    The rank and critical-fibre obligations are proved earlier;
    no target rectifiability or coarea equality is assumed. *)
Theorem pure_target_fibres_almost_null (F:X->Y) (A:set X) (T:set Y) L k mu:
  (0<v)%N ->(0<mu)%N ->m.+1=(k+mu)%N ->
  is_metric_lipschitz_bound setT F L ->borel_set T ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R Y mu) mu T ->
  A `<=` F @^-1` T ->
  measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass F A k y=0].
Proof.
move=>hv hmu hDim hLip hT hPure hAT.
pose P:set X:=[set a|exists D r,has_norm_differential NX NY setT F a D /\
  has_linear_rank D r /\(r<mu)%N].
have hRankAE:measure_almost_everywhere_on Leb (F @^-1` T) P.
  exact (@federer_3_2_21 R m.+1 v mu F T hmu (metric_lipschitz_of_bound hLip) hT hPure).
pose B:=A `&` P.
pose N:=A `\` P.
have hCritical a:B a ->exists D:Hom (R_n R m.+1) (R_n R v),
    has_norm_differential NX NY setT F a D /\~linear_rank_at_least D mu.
  move=>[_ [D [r [hD [hR hr]]]]].
  exists D; split=>//; move=>hAtLeast.
  have hLe:=(linear_rank_at_leastP mu hR).1 hAtLeast.
  have hFalse:=leq_ltn_trans hLe hr; by rewrite ltnn in hFalse.
have hNullB:=@lipschitz_low_rank_fibres_almost_null R m v F B L k mu
  hv hmu hDim hLip hCritical.
have hLeb:=euclidean_lebesgue_is_measure R m.+1.
have hN:Leb N=0.
  apply:(measure_null_subset hLeb _ hRankAE)=>a [ha hNotP].
  split=>//; exact:hAT a ha.
have hNullN:measure_almost_everywhere (@hausdorff_measure R Y mu)
    [set y|hausdorff_fibre_mass F N k y=0].
  apply:(@null_hausdorff_fibres_proper_source R X Y F L N k mu _ hLip).
  - move=>a r hr; exact (@euclidean_closed_metric_ball_compact R m.+1 a r).
  - rewrite -hDim (euclidean_hausdorff_spherical_lebesgue N).1; exact hN.
pose Q j:=if j is i.+1 then B else N.
apply:(@almost_null_fibres_countable_cover R X Y (@hausdorff_measure R X k)
  (@hausdorff_measure R Y mu) (@hausdorff_measure_is_measure R X k)
  (@hausdorff_measure_is_measure R Y mu) F A Q).
- move=>a ha; case:(pselect (P a))=>hP.
  + exists 1%N=>//; by split.
  + exists 0%N=>//; by split.
- by move=>[|j]; [exact hNullN|exact hNullB].
Qed.
End PureTargetNull.
