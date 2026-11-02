(** Federer (1969), 3.2.6, p. 246: convert
    the ordered regular-root crossing count into the actual
    difference of positive- and negative-derivative fibre
    multiplicities. No orientation between f(a) and f(b)
    is assumed; equal endpoint values are included. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality constructive_ereal topology normedtype lra.
From Federer Require Import RealMetricBackground RealCurveDerivativeUP RealDerivativeRepresentative
  ScalarCurveDerivativeLoci FiniteCountingSequences FiniteRegularRootCrossing EndpointLevelSigns
  MappingMultiplicity CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_regular_level_signed_multiplicity]:
    the finite-fibre observation in Federer 3.2.6, p. 246.
    The two actual counting masses are finite real values,
    and their difference is the oriented interval indicator.
    Regularity and finiteness are local helper hypotheses;
    their almost-everywhere validity is proved separately. *)
Theorem scalar_regular_level_signed_multiplicity (R:realType) (f:R->R) (a b y:R):
  a<b -> continuous (f:real_line_metric R->real_line_metric R) ->
  (@mapping_multiplicity R [the choiceType of real_line_metric R] R f `[a,b] y< +oo)%E ->
  (forall x,a<=x -> x<=b -> f x=y ->
    exists v:R,has_real_curve_derivative f x v /\ v!=0 /\ a<x /\ x<b) ->
  exists p q:R,
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f (scalar_positive_derivative_set f a b) y=p%:E /\
    @mapping_multiplicity R [the choiceType of real_line_metric R] R f (scalar_negative_derivative_set f a b) y=q%:E /\
    p-q=oriented_level_indicator (f a) (f b) y.
Proof.
move=>hab hCont hFinite hRegular.
pose E:=mapping_fibre f (`[a,b]:set (real_line_metric R)) y.
have hSet:finite_set E:=@finite_counting_measure_set_finite R [the choiceType of real_line_metric R] E hFinite.
have [F hF]:=(@finite_fsetP [the choiceType of real_line_metric R] E).1 hSet.
pose roots:=sort <=%O (enum_fset F).
pose D:=real_derivative_representative f.
have hRootsSet:[set t|t \in roots]=E.
  apply/seteqP; split=>t ht.
  - change (is_true (t \in roots)) in ht.
    have hFt:t \in F by move:ht; rewrite /roots mem_sort.
    change ([set` F] t) in hFt; by rewrite -hF in hFt.
  - rewrite hF in ht; change (is_true (t \in F)) in ht.
    change (is_true (t \in roots)); by rewrite /roots mem_sort.
have hData t:t \in roots -> exists v:R,has_real_curve_derivative f t v /\ v!=0 /\ a<t /\ t<b.
  move=>ht; have hE:E t by rewrite -hRootsSet.
  have [hIt hty]:=hE; move:hIt; rewrite /= in_itv /= =>/andP[hat htb].
  exact (hRegular t hat htb hty).
have hInside t:t \in roots -> a<t /\ t<b.
  move=>ht; have [v [hv [hv0 [hat htb]]]]:=hData t ht; by split.
have hDiff t:t \in roots -> has_real_curve_derivative f t (D t) /\ D t!=0.
  move=>ht; have [v [hv [hv0 _]]]:=hData t ht.
  have hd:D t=v:=real_derivative_representative_value hv.
  by rewrite hd; split.
have hRoot t:a<=t -> t<=b -> (f t=y <-> t \in roots).
  move=>hat htb; split.
  - move=>hty; change ([set u|u \in roots] t); rewrite hRootsSet; split=>//.
    by rewrite /= in_itv /= hat htb.
  - move=>ht; have hE:E t by rewrite -hRootsSet.
    exact hE.2.
have hUniq:uniq roots by rewrite /roots sort_uniq fset_uniq.
have hSorted:pairwise <%O roots.
  rewrite -lt_sorted_pairwise /roots sort_lt_sorted fset_uniq; exact:erefl.
have hSum:=@finite_regular_root_signed_crossing R f D y roots hCont a b hab hSorted hInside hRoot hDiff.
have hCounts:=@real_sign_sum_counts R [the eqType of real_line_metric R] roots D
  (fun t ht=>(hDiff t ht).2).
pose P t:=(0<D t).
pose N t:=(D t<0).
have hPos: mapping_fibre f (scalar_positive_derivative_set f a b) y=
    [set t|t \in [seq t<-roots|P t]].
  apply/seteqP; split=>t.
  - move=>[[hIt [v [hv hvPos]]] hty].
    move:hIt; rewrite /= in_itv /= =>/andP[hat htb].
    have ht: t \in roots:=(hRoot t (ltW hat) (ltW htb)).1 hty.
    have hd:D t=v:=real_derivative_representative_value hv.
    change (is_true (t \in [seq t<-roots|P t])); rewrite mem_filter; apply/andP; split=>//; by rewrite /P hd.
  - move=>ht; change (is_true (t \in [seq t<-roots|P t])) in ht.
    move:ht; rewrite mem_filter=>/andP[hPt ht].
    have [hat htb]:=hInside t ht.
    have hIt:(`]a,b[:set (real_line_metric R)) t by rewrite /= in_itv /= hat htb.
    split.
    + split=>//; exists (D t); split; [exact (hDiff t ht).1|exact hPt].
    + exact ((hRoot t (ltW hat) (ltW htb)).2 ht).
have hNeg: mapping_fibre f (scalar_negative_derivative_set f a b) y=
    [set t|t \in [seq t<-roots|N t]].
  apply/seteqP; split=>t.
  - move=>[[hIt [v [hv hvNeg]]] hty].
    move:hIt; rewrite /= in_itv /= =>/andP[hat htb].
    have ht:t \in roots:=(hRoot t (ltW hat) (ltW htb)).1 hty.
    have hd:D t=v:=real_derivative_representative_value hv.
    change (is_true (t \in [seq t<-roots|N t])); rewrite mem_filter; apply/andP; split=>//; by rewrite /N hd.
  - move=>ht; change (is_true (t \in [seq t<-roots|N t])) in ht.
    move:ht; rewrite mem_filter=>/andP[hNt ht].
    have [hat htb]:=hInside t ht.
    have hIt:(`]a,b[:set (real_line_metric R)) t by rewrite /= in_itv /= hat htb.
    split.
    + split=>//; exists (D t); split; [exact (hDiff t ht).1|exact hNt].
    + exact ((hRoot t (ltW hat) (ltW htb)).2 ht).
pose p:=(count P roots)%:R:R.
pose q:=(count N roots)%:R:R.
exists p,q; split.
- rewrite /mapping_multiplicity hPos (counting_measure_finite_sequence R (filter_uniq P hUniq)) size_filter.
  exact:erefl.
split.
- rewrite /mapping_multiplicity hNeg (counting_measure_finite_sequence R (filter_uniq N hUniq)) size_filter.
  exact:erefl.
have hA:f a!=y.
  apply/eqP=>he; have [v [hv [hv0 [haa _]]]]:=hRegular a (lexx _) (ltW hab) he.
  by rewrite ltxx in haa.
have hB:f b!=y.
  apply/eqP=>he; have [v [hv [hv0 [_ hbb]]]]:=hRegular b (ltW hab) (lexx _) he.
  by rewrite ltxx in hbb.
have hEndpoints:=endpoint_level_sign_difference hA hB.
rewrite hCounts hEndpoints in hSum.
change (p-q=oriented_level_indicator (f a) (f b) y); rewrite /p /q /P /N; lra.
Qed.
