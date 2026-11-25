(** Federer (1969), 3.3.19, p. 304:
    a finite weighted collection on an actual closed
    curve is bounded by its variation after ordering
    its actual parameter values. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import CurveVariationUP OrderedCurveWeightBudget ClosedCurveOrderedPolygon.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [closed_curve_ordered_weight_budget]:
    supporting complete cyclic weight sum in 3.3.19,
    p. 304. The actual first and last
    labels differ; their closing chord pays the
    two remaining endpoint weights. *)
Lemma closed_curve_ordered_weight_budget (R:realType) (Y:metricType R)
    (I:eqType) (g:R->Y) (t:I->R) (w:I->R) (a b:R) (i j:I) (s:seq I):
  uniq (i::j::s) ->sorted <=%O (map t (i::j::s)) ->
  (forall k,k \in i::j::s ->a<=t k /\t k<=b) ->g a=g b ->
  (forall k l,k \in i::j::s ->l \in i::j::s ->k!=l ->
    w k+w l<=mdist (g (t k)) (g (t l))) ->
  ((2*(\sum_(k<-i::j::s) w k))%:E<=curve_variation g a b)%E.
Proof.
move=>hUnique hSorted hBounds hEnds hPair.
have hOpen:=@ordered_curve_chain_weight_budget R Y I g t w i (j::s) hUnique hPair.
have hLast:last i (j::s) \in j::s by rewrite last_cons;exact:mem_last.
have hLastFull:last i (j::s) \in i::j::s by rewrite inE hLast orbT.
have hDistinct:i!=last i (j::s).
  have /andP[hi _]:=hUnique.
  apply/negP=>/eqP hEqual;move:hi;by rewrite hEqual hLast.
have hClosing:=hPair i (last i (j::s)) (mem_head i (j::s)) hLastFull hDistinct.
have hLower:(2*(\sum_(k<-i::j::s) w k))<=
    chain_sum g (map t (i::j::s))+mdist (g (t (last i (j::s)))) (g (t i)).
  rewrite metric_sym;lra.
have hMapBounds x:x \in map t (i::j::s) ->a<=x /\x<=b.
  move=>/mapP[k hk ->];exact:hBounds k hk.
have hUpper:=@closed_curve_ordered_polygon_bound R Y g a b (t i) (map t (j::s))
  hSorted hMapBounds hEnds.
rewrite last_map in hUpper.
apply:(le_trans _ hUpper);by rewrite lee_fin.
Qed.
