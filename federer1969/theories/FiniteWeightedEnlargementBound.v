(** Federer (1969), 2.10.24(2), p. 188:
    supporting finite weighted weak-level estimate. A
    disjoint layer is chosen by the sealed 2.8.4
    theorem and its controlled enlargements cover the
    level set. Least-real-weight peeling replaces only
    the printed rational-to-integer reduction. Source
    editions: WeightedMetricEnvelopeUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals constructive_ereal topology lra.
From Federer Require Import MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelopeLaws MetricScaleCutoffCost MeasureBasic
  CaratheodoryWeakEnlargementUP DiameterEnlargements FiniteDisjointWeightedLayers
  FiniteEnlargedDisjointCover FiniteEnlargedCoverCost FiniteWeightedGeneratorSums
  WeightedMetricEnvelopeUP NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_weighted_enlargement_bound]: supporting
    finite-family estimate preceding the integer layers
    of 2.10.24(2), p. 188. The target may
    be any subset on which the weighted multiplicity
    is at least t>0. No measurability is required.
    Only the finite family in use needs finite costs;
    unbounded generators outside it may have infinite cost. *)
Theorem finite_weighted_enlargement_bound (R : realType) (X : metricType R)
    (F : set (set X)) (c : set X -> \bar R) (E : set X -> set X) (k d : R)
    (nu : set X -> \bar R) (P : {fset set_type F}) (u : set_type F -> R) (A : set X) (t : R) :
  is_weak_caratheodory_enlargement F c E k ->
  (forall S, F S -> S<>set0) -> (forall j, j \in P -> c (val j)< +oo) ->
  is_metric_scale_envelope (fun j : set_type F=>val j) (fun j=>c (val j)) (k*d)%R%:E nu ->
  (forall j, j \in P -> extended_metric_diameter (val j)<=d%:E) ->
  (forall j, j \in P -> (0<=u j)%R) -> (0<t)%R ->
  (forall x, A x -> t%:E<=weighted_generator_sum (fun j : set_type F=>val j) [set` P] u x) ->
  t%:E*nu A<=k%:E*weighted_generator_cost (fun j : set_type F=>c (val j)) [set` P] u.
Proof.
move=> hE hne hfinite hn hd hu ht hlevel.
pose J := [the choiceType of set_type F].
pose a (j : J) := fine (c (val j)).
have hk := weak_enlargement_constant_positive hE.
have hc (j : J) : 0<=c (val j) := @weak_enlargement_cost_nonnegative R X F c E k hE (val j) (set_valP j).
have hcf (j : J) (hj : j \in P) : c (val j) \is a fin_num.
  rewrite ge0_fin_numE; [exact: hfinite j hj|exact: hc].
have haE (j : J) (hj : j \in P) : (a j)%:E=c (val j) by rewrite /a (fineK (hcf j hj)).
have ha j (hj : j \in P) : (0<=a j)%R.
  have hh := hc j; by rewrite -(haE j hj) lee_fin in hh.
have hcosteq : weighted_generator_cost (fun j : J=>c (val j)) [set` P] u=(\sum_(j <- P) u j*a j)%R%:E.
  have he : weighted_generator_cost (fun j : J=>c (val j)) [set` P] u=
      weighted_generator_cost (fun j=>(a j)%:E) [set` P] u.
    apply: nonnegative_sum_ext=> j hj; by rewrite (haE j hj).
  rewrite he; exact: finite_weighted_generator_cost hu ha.
have hlevelR x (hx : A x) : (t<=\sum_(j <- P) (if x \in val j then u j else 0))%R.
  have hh := hlevel x hx; by rewrite (finite_weighted_generator_point_sum _ _ hu) lee_fin in hh.
have hcover : A `<=` \bigcup_(j in [set` P]) val j.
  move=> x hx; apply: contrapT=> hnone.
  have hz : (\sum_(j <- P) (if x \in val j then u j else 0))%R=0%R.
    rewrite big_seq; apply: big1=> j hj.
    have hjnot : x \notin val j.
      apply/negP=> /set_mem hxj; apply: hnone; by exists j.
    by rewrite (negbTE hjnot).
  have hh := hlevelR x hx; by rewrite hz leNgt ht in hh.
have hAenlarged : A `<=` \bigcup_(j in [set` P]) E (val j).
  move=> x hx; have [j hj hxj] := hcover x hx; exists j=> //.
  exact (@weak_enlargement_contains R X F c E k hE (val j) (set_valP j) x
    (@diameter_enlargement_contains R X F (val j) (set_valP j) x hxj)).
have hnuupper := @finite_enlarged_cover_cost R X F c E k d nu P a A hE hn haE hd hAenlarged.
have hnu0 : 0<=nu A := @metric_scale_envelope_nonnegative R X J (fun j=>val j) (fun j=>c (val j)) _ nu hn A.
have hnufinite : nu A \is a fin_num.
  rewrite ge0_fin_numE; [exact: le_lt_trans hnuupper (ltry _)|exact hnu0].
pose b := fine (nu A).
have hbE : b%:E=nu A by rewrite /b fineK.
have hb : (0<=b)%R by have hh := hnu0; rewrite -hbE lee_fin in hh.
case: (pselect (A!=set0))=> [hAne|hAempty]; last first.
  have he : A=set0 by apply/seteqP; split=> // x hx; exfalso; apply: hAempty; by exists x.
  have hnm := metric_scale_envelope_is_measure hn (fun j=>weak_enlargement_cost_nonnegative hE (set_valP j)).
  have hezero : nu A=0 by rewrite he (measure_empty hnm).
  rewrite hezero mule0 hcosteq; apply: mule_ge0; [by rewrite lee_fin; exact: ltW hk|].
  rewrite lee_fin big_seq; apply: sumr_ge0=> j hj; exact: mulr_ge0 (hu j hj) (ha j hj).
have hselect (Q : {fset J}) (hQP : forall j, j \in Q -> [set` P] j)
    (hQA : A `<=` \bigcup_(j in [set` Q]) val j) :
    exists H : {fset J}, (H `<=` Q)%fset /\ H!=fset0 /\
      (forall i j, i \in H -> j \in H -> i!=j -> val i `&` val j=set0) /\
      (b<=\sum_(j <- H) k*a j)%R.
  have hQdiam j (hj : j \in Q) := hd j (hQP j hj).
  have [H [hHQ [hHdisj hHcover]]] := @finite_enlarged_disjoint_cover R X F c E k d Q hE
    (fun j _=>hne _ (set_valP j)) hQdiam.
  have hAH : A `<=` \bigcup_(j in [set` H]) E (val j) by move=> x hx; exact: hHcover x (hQA x hx).
  have hHne : H!=fset0.
    apply/negP=> /eqP he; have [x hx] := hAne; have [j hj _] := hAH x hx.
    change (is_true (j \in H)) in hj; by rewrite he in_fset0 in hj.
  have hHdiam j (hj : j \in H) := hQdiam j ((fsubsetP hHQ) j hj).
  have hbound := @finite_enlarged_cover_cost R X F c E k d nu H a A hE hn (fun j hj=>haE j (hQP j ((fsubsetP hHQ) j hj))) hHdiam hAH.
  rewrite -hbE lee_fin big_distrr in hbound.
  exists H; split=> //; split=> //; split.
have hresult := @finite_weighted_disjoint_layer_bound R X J (fun j=>val j) [set` P] A (fun j=>(k*a j)%R) b
  hAne hb (fun j hj=>mulr_ge0 (ltW hk) (ha j hj)) hselect P u t (fun j hj=>hj) hu ht hlevelR.
rewrite hcosteq -hbE -!EFinM lee_fin big_distrr.
apply: le_trans hresult _; apply: ler_sum=> j _; rewrite mulrA [((u j)*k)%R]mulrC -mulrA; exact: lexx.
Qed.
