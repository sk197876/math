(** Federer (1969), 3.4.5, p. 320: finitely
    many analytic germs have actual representatives on one
    common open analytic neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology NormAnalyticUP NormAnalyticOperations
  AnalyticGermNeighbourhood AnalyticGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_analytic_representative_neighbourhood]:
    a common U for the original finite equation system
    in 3.4.5, p. 320. The empty family
    yields the whole source space. *)
Theorem finite_analytic_representative_neighbourhood (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X) (I:finType)
    (f:I->@analytic_representative_type R X NX hNX a):
  exists U:set X,U a /\@open (real_norm_metric_space hNX) U /\
    forall i,@norm_analytic R X R^o NX (fun z=>`|z|) hNX (@scalar_absolute_value_norm R)
      U (analytic_representative_value (f i)).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hex i:=@analytic_germ_open_representative R X R^o NX (fun z=>`|z|) hNX
  (@scalar_absolute_value_norm R) setT (analytic_representative_value (f i)) a
  (analytic_representative_analytic (f i)).
pose V i:=projT1 (cid (hex i)).
have hV i:=projT2 (cid (hex i)).
pose U:set T:=fun x=>forall i,V i x.
have ha:U a by move=>i;exact:(hV i).1.
have hU:open U.
  rewrite openE=>x hx;apply:(@filter_forall T I _ (nbhs x) (nbhs_filter x))=>i.
  have hOpen:@open T (V i):=(hV i).2.2.1.
  rewrite openE in hOpen;exact:hOpen x (hx i).
have hOpen x (hx:U x):norm_domain_interior NX U x.
  have hNeighbourhood:=hU;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R X NX hNX U x).2 (hNeighbourhood x hx)).
exists U;split;first exact:ha.
split;first exact:hU.
move=>i;exact:(@norm_analytic_open_restriction R X R^o NX (fun z=>`|z|) hNX
  (@scalar_absolute_value_norm R) (V i) U (analytic_representative_value (f i))
  (fun x hx=>hx i) hOpen (hV i).2.2.2).
Qed.
