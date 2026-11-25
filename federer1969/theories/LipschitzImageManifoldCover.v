(** Federer (1969), 3.2.29, p. 268: let the error of
    class-one approximation tend to zero through a countable
    sequence and unite the corresponding manifold families. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  EuclideanSubmanifoldUP RectifiableManifoldCoverUP LipschitzSmallManifoldRemainder
  HausdorffMeasure MeasureUP MeasureBasic ExtendedScaledErrorBound ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lipschitz_image_countable_manifold_cover]: the
    global-image forward argument in Federer 3.2.29, p. 268.
    Countably many approximation tolerances suffice. Neither source
    nor target dimension bounds, finite image mass, measurability
    of the desired subset, or a globally injective map is assumed. *)
Theorem lipschitz_image_countable_manifold_cover (R:realType) m n
    (F:inner_metric_space (@euclidean_inner_productP R m.+1)->
      inner_metric_space (@euclidean_inner_productP R n)) L:
  is_metric_lipschitz_bound setT F L ->
  has_countable_submanifold_measure_cover m.+1 1 (F @` setT).
Proof.
move=>hLip.
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose beta:=@hausdorff_measure R Y m.+1.
pose hb:=@hausdorff_measure_is_measure R Y m.+1.
pose r j:=(((j.+1)%:R:R)^-1)%R.
have hr j:0<r j by rewrite /r invr_gt0 ltr0n.
have hex j:exists C:set (set (R_n R n)),countable C /\
    (forall S,C S ->@is_euclidean_submanifold R n m.+1 1 S) /\
    (beta ((F @` setT) `\` \bigcup_(S in C) S)<=(L^+m.+1*r j)%:E)%E.
  exact:lipschitz_small_manifold_remainder hLip (hr j).
have [C hC]:=choice hex.
pose G:=\bigcup_(j in @setT nat) C j.
have hG:countable G:=bigcup_countable (countableP _) (fun j _=>(hC j).1).
have hBound e:0<e ->(beta ((F @` setT) `\` \bigcup_(S in G) S)<=(0+L^+m.+1*e)%:E)%E.
  move=>he; have [j hj]:=positive_reciprocal_nat_small he.
  have hSub:(F @` setT) `\` \bigcup_(S in G) S `<=` (F @` setT) `\` \bigcup_(S in C j) S.
    move=>x [hx hn]; split; first exact hx.
    move=>[S hS hxS]; apply:hn; exists S; last exact hxS.
    by exists j.
  apply:le_trans (measure_mono hb hSub) _.
  apply:le_trans (hC j).2.2 _.
  rewrite add0r lee_fin; exact (ler_wpM2l (exprn_ge0 m.+1 hLip.1) (ltW hj)).
exists G; constructor.
- exact hG.
- move=>S [j _ hS]; exact:(hC j).2.1 S hS.
- apply/eqP; rewrite eq_le (measure_nonnegative hb) andbT.
  exact (@extended_upper_bound_from_scaled_errors R _ 0 (L^+m.+1) (exprn_ge0 m.+1 hLip.1) hBound).
Qed.
