(** Federer (1969), 3.3.7, p. 294: a bounded original
    projected source has a finite small-ball cover with original centres. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals topology.
From Federer Require Import SeparatedMetricSetUP MaximalSeparatedSealed
  SeparatedMetricNet CompactSeparatedCardinality MetricClosedBalls FiniteSeparatedMetricNetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [contained_compact_finite_separated_metric_net_exists]:
    supporting local finiteness of the actual projected measure in Federer
    3.3.7, p. 294. The original subset A of compact K need not be
    closed or measurable. Existing opaque maximal-separated laws and
    the compact cardinal bound give a finite net with centres in A.
    No new global selected net is introduced. *)
Theorem contained_compact_finite_separated_metric_net_exists (R:realType) (X:metricType R)
    (x0:X) (A K:set X) (r:R):
  compact K ->A `<=` K ->0<r ->exists B,is_finite_separated_metric_net A r B.
Proof.
move=>hK hAK hr.
pose S:=@MaximalSeparated.value R X A r.
have hS:=@MaximalSeparated.laws R X A r.
have hInside:S `<=` A:=@separated_subset_inside R X A r S hS.
have hSeparate:is_strictly_separated_metric_set r S:=@separated_subset_separation R X A r S hS.
have [N [_ hBound]]:=@compact_separated_cardinal_bound R X x0 K r hK hr.
have hFinite:finite_set S.
  have hSepLe a b:S a ->S b ->a<>b ->r<=mdist a b.
    move=>ha hb hDifferent; exact:ltW (hSeparate a b ha hb hDifferent).
  exact:card_le_finite (hBound S (fun x hx=>hAK x (hInside x hx)) hSepLe) (@finite_finset _ (@setT 'I_N)).
pose B:=fset_set S.
have hMember (a:X):a \in B <->S a.
  rewrite /B in_fset_set //; split; [exact:set_mem|exact:mem_set].
exists B; constructor.
- move=>a ha; exact:hInside a ((hMember a).1 ha).
- move=>a b ha hb /eqP hDifferent.
  exact:hSeparate a b ((hMember a).1 ha) ((hMember b).1 hb) hDifferent.
- move=>x hx.
  have [a [ha hxa]]:=@maximal_separated_subset_covers R X A S r (ltW hr) hS x hx.
  exists a; first exact:(hMember a).2 ha.
  change (is_true (mdist a x<=r)).
  by rewrite metric_sym.
Qed.
