(** Federer (1969), 2.10.47(3), p. 205: continuity of t |-> gamma_i(E
    intersect {x_1<=t}). The supporting statement below separates the
    topological neighbourhood argument from the dyadic covering estimate:
    arbitrarily cheap relative open neighbourhoods of each compact level
    imply continuity of the finite real slice values. No Borel measurability
    of the cutoff content is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactLevelNeighborhood MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_content_slice_continuous]: supporting
    continuity assertion of 2.10.47(3), p. 205.
    Subadditivity controls both changes of a slice by the
    mass of a small band. The open-neighbourhood premise
    is to be proved for the dyadic content, rather than
    silently replacing that content by a Borel measure. *)
Theorem compact_content_slice_continuous (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (E : set X)
    (f : X -> real_line_metric R) (F : R -> R) :
  compact E -> continuous f ->
  (forall t, mu (E `&` [set x | (f x<=t)%R])=(F t)%:E) ->
  (forall t e : R, 0<e -> exists U, [/\ open U,
    (E `&` [set x | f x=t]) `<=` U & (mu (E `&` U)<e%:E)%E ]) ->
  continuous (F : real_line_metric R -> real_line_metric R).
Proof.
move=> hE hf hF hopen t W hW.
have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP
  (F t : real_line_metric R) W) hW.
have [U [hU hlevel hmass]] := hopen t e he.
have [d [hd hband]] := @compact_level_open_neighbourhood R X E U f t hE hf hU hlevel.
have hnum : mu (E `&` U) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm (E `&` U))); exact: lt_trans hmass (ltry e).
have hvalue : mu (E `&` U)=(fine (mu (E `&` U)))%:E := esym (fineK hnum).
have hsmall : fine (mu (E `&` U))<e by rewrite hvalue lte_fin in hmass.
apply: (proj2 (metricType_numDomainType.nbhs_mdistP (t : real_line_metric R) (F @^-1` W))).
exists d=> // s hs.
have hst : `|s-t|<d.
  change (is_true (`|t-s|<d)) in hs; by rewrite distrC.
rewrite ltr_norml in hst; have /andP[hstlo hsthi] := hst.
have hleft : (mu (E `&` [set x | (f x<=s)%R])<=mu (E `&` [set x | (f x<=t)%R])+mu (E `&` U))%E.
  apply: (@measure_binary_cover R X mu hm)=> x [hx hxs].
  change (is_true (f x<=s)) in hxs.
  case: (leP (f x) t)=> hxt; first by left; split.
  right; split=> //; apply: hband; split=> //.
  change (is_true (`|f x-t|<d)); rewrite ltr_norml; apply/andP; split; lra.
have hright : (mu (E `&` [set x | (f x<=t)%R])<=mu (E `&` [set x | (f x<=s)%R])+mu (E `&` U))%E.
  apply: (@measure_binary_cover R X mu hm)=> x [hx hxt].
  change (is_true (f x<=t)) in hxt.
  case: (leP (f x) s)=> hxs; first by left; split.
  right; split=> //; apply: hband; split=> //.
  change (is_true (`|f x-t|<d)); rewrite ltr_norml; apply/andP; split; lra.
rewrite !hF hvalue -EFinD lee_fin in hleft.
rewrite !hF hvalue -EFinD lee_fin in hright.
apply: hball; change (is_true (`|F t-F s|<e)).
rewrite ltr_norml; apply/andP; split; lra.
Qed.
