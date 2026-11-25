(** Federer (1969), 3.2.32, pp. 269–270: proved
    disjoint Borel target cover of the positive fibre locus.
    The finite thresholds are supplied by 3.2.31. Borel
    hulls and first-hit differences preserve finite rectifiability. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals
  constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealReciprocalBounds MeasureUP MeasureAlmostBasic
  BorelRegularMeasureUP TopologicalBorel RectifiableSetUP MeasureRectifiableSubset
  FiniteRectifiableBorelCover SetSequenceDisjointification PositiveFibreTargetCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_fibre_target_cover_exists]: supporting the
    reciprocal-threshold limit in Federer 3.2.32, p. 270.
    Finite measurable rectifiable threshold sets yield disjoint
    finite rectifiable Borel pieces covering every positive fibre
    value. Their excess is null in the target measure. All
    choices remain local; no completed-target preimage implication
    or measurability of a source restriction is assumed. *)
Theorem positive_fibre_target_cover_exists (R:realType) (X:metricType R)
    (beta:set X->\bar R) (hb:is_measure beta) (hr:is_borel_regular_measure beta)
    mu (f:X->extended_real_line R):
  (forall t:R,(0<t)%R ->measure_measurable beta [set x|t%:E<=f x] /\
    is_measure_m_rectifiable beta mu [set x|t%:E<=f x]) ->
  exists D,is_positive_fibre_target_cover beta mu [set x|0<f x] D.
Proof.
move=>hThreshold.
pose t j:=(((j.+1)%:R:R)^-1)%R.
have ht j:(0<t j)%R by rewrite /t invr_gt0 ltr0n.
pose Z j:set X:=[set x|(t j)%:E<=f x].
have hB j:exists B,borel_set B /\is_measure_m_rectifiable beta mu B /\Z j `<=` B /\beta (B `\` Z j)=0.
  have hZ:=hThreshold (t j) (ht j).
  exact (@finite_measurable_rectifiable_borel_cover_exists R X beta hb hr mu (Z j) hZ.1 hZ.2).
have [B hLaws]:=choice hB.
pose D:=set_sequence_disjointify B.
have hUnion:(\bigcup_j D j)=\bigcup_j B j:=set_sequence_disjointify_union B.
have hZj j:Z j `<=` [set x|0<f x].
  move=>x hx; apply:lt_le_trans _ hx; by rewrite lte_fin.
have hPositive:[set x|0<f x] `<=` \bigcup_j Z j.
  move=>x hx; change (is_true (0<f x)) in hx.
  case hValue:(f x)=>[a| |] in hx *; last by [].
  - have ha:(0<a)%R:=hx; have [j hj]:=positive_reciprocal_nat_small ha.
    exists j=>//; change (is_true ((t j)%:E<=f x)); rewrite hValue lee_fin; exact (ltW hj).
  - exists 0%N=>//; change (is_true ((t 0%N)%:E<=f x)); by rewrite hValue leey.
exists D; constructor.
- move=>j; apply:borel_set_difference (hLaws j).1 _.
  apply:(@borel_set_countable_union X [the choiceType of (nat:Type)] [set i|(i<j)%N] B (countableP _)).
  move=>i hi; exact:(hLaws i).1.
- move=>j; apply:(measure_rectifiable_subset _ (hLaws j).2.1).
  by move=>x [hx _].
- exact:set_sequence_disjointify_disjoint.
- rewrite hUnion; move=>x hx; have [j _ hj]:=hPositive x hx.
  exists j=>//; exact:(hLaws j).2.2.1 x hj.
- rewrite hUnion.
  have hNull:beta (\bigcup_j (B j `\` Z j))=0.
    apply:(measure_null_countable_union hb (countableP _))=>j _; exact:(hLaws j).2.2.2.
  apply:(measure_null_subset hb _ hNull)=>x [[j _ hBx] hNot].
  exists j=>//; split=>//; move=>hZx; exact:hNot (hZj j x hZx).
Qed.
