(** Federer (1969), 3.4.8(11), p. 333:
    each positive component contains an
    interior critical maximum of Psi. The
    compact closure and zero boundary give
    an interior maximizer; the proved local
    Fermat lemma gives its zero differential. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP
  NormClassZeroTopology NormBoundedLinearTopology RealMetricBackground ScalarNormExtendedEmbedding
  CompactRelativeMaximum NormDifferentialLocalMaximum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_positive_critical_maximum]:
    choose eta in C intersect H
    in 3.4.8(11), p. 333.
    All neighbourhoods and maxima remain local
    witnesses; no critical point is assumed. *)
Theorem norm_positive_critical_maximum (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A C K:set X) (f:X->R^o)
    (D:X->Hom X R^o) a:
  norm_class_zero NX (fun z:R^o=>`|z|) A f ->
  (forall x,A x ->has_norm_differential NX (fun z:R^o=>`|z|) A f x (D x)) ->
  @compact (real_norm_metric_space hNX) K ->C `<=` K ->K `<=` A ->
  C a ->0<f a ->
  (forall x,@closure (real_norm_metric_space hNX) C x ->
    ~@interior (real_norm_metric_space hNX) C x ->f x = 0) ->
  exists b,C b /\ 0<f b /\ forall v,D b v = 0.
Proof.
move=>hContinuous hD hK hCK hKA hCa hPositive hBoundary.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hKClosed:@closed T K:=compact_closed (@metric_hausdorff R (real_norm_metric_space hNX)) hK.
have hClosure:@closure T C `<=` K.
  have h:=@closureS T C K hCK.
  by rewrite -((@closure_id T K).1 hKClosed) in h.
have hCompact:@compact T (@closure T C).
  have hEqual:@closure T C = K `&` @closure T C.
    apply/seteqP;split;[move=>x hx;split;[exact:hClosure x hx|exact:hx]|by move=>x [_ hx]].
  rewrite hEqual;exact:compact_closedI hK (@closed_closure T C).
have hNonempty:@closure T C !=set0 by exists a;exact:subset_closure hCa.
have hRealContinuous:{within (@closure T C),continuous (fun x:T=>(f x:R^o))}.
  apply:continuous_in_subspaceT=>x /asboolP hx.
  exact:(@continuous_comp T
    (Topological.clone (real_norm_metric_space (@scalar_absolute_value_norm R)) _)
    (Topological.clone (real_line_metric R) _)
    (fun x:T=>(f x:real_norm_metric_space (@scalar_absolute_value_norm R)))
    (fun z:real_norm_metric_space (@scalar_absolute_value_norm R)=>(z:real_line_metric R)) x
    (@norm_class_zero_continuous_at R X R^o NX (fun z:R^o=>`|z|) hNX
      (@scalar_absolute_value_norm R) A f x hContinuous (hKA x (hClosure x hx)))
    (@ScalarNormExtendedEmbedding.scalar_norm_real_identity_continuous R (f x))).
have [b [hB hMaximum]]:=@continuous_compact_relative_maximum R T (@closure T C) f
  hNonempty hCompact hRealContinuous.
have hPositiveB:0<f b:=lt_le_trans hPositive (hMaximum a (subset_closure hCa)).
have hInterior:@interior T C b.
  apply:contrapT=>hNot;have hZero:=hBoundary b hB hNot.
  by move:hPositiveB;rewrite hZero ltxx.
have hCb:C b:=interior_subset hInterior.
exists b;split;first exact:hCb.
split;first exact:hPositiveB.
apply:(@norm_differential_local_maximum_zero R X NX hNX A f b (D b)
  (hD b (hKA b (hClosure b hB)))).
have hOpen:@open T (@interior T C):=@open_interior T C.
rewrite openE in hOpen.
have [r [hr hBall]]:=(@norm_domain_interior_neighbourhood R X NX hNX (@interior T C) b).2
  (hOpen b hInterior).
exists r;split;first exact:hr.
move=>h hh;apply:hMaximum;apply:subset_closure;exact:interior_subset (hBall h hh).
Qed.
