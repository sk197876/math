(** Federer (1969), 3.4.12, p. 339, extending 3.4.5,
    p. 320: finitely many original holomorphic representatives
    are holomorphic on one common open neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import HolomorphicUP NormAnalyticLocal RealNormUP ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm
  NormMetric NormDifferentialUP NormBoundedLinearTopology NormAnalyticDomain HolomorphicUP
  HolomorphicRestriction HolomorphicGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [finite_holomorphic_representative_neighbourhood]:
    the common domain for the original finite generator family,
    3.4.12, p. 339. The empty family retains the whole space. *)
Theorem finite_holomorphic_representative_neighbourhood (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a (I:finType)
    (f:I->@holomorphic_representative_type R X NX hNX a):
  exists U:set X,U a /\@open (real_norm_metric_space hNX) U /\
    forall i,@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
      (@complex_modulus_real_norm R) U (holomorphic_representative_value (f i)).
Proof.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have hex i:=holomorphic_representative_holomorphic (f i).
pose V i:=projT1 (cid (hex i)).
have hV i:=projT2 (cid (hex i)).
pose U:set T:=fun x=>forall i,V i x.
have ha:U a by move=>i;exact:(hV i).1.
have hOpenV i:@open T (V i):=norm_analytic_domain_open (hV i).2.1.
have hU:open U.
  rewrite openE=>x hx;apply:(@filter_forall T I _ (nbhs x) (nbhs_filter x))=>i.
  have hOpen:=hOpenV i;rewrite openE in hOpen;exact:hOpen x (hx i).
have hOpen x (hx:U x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX U x.
  have hNeighbourhood:=hU;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X)
    NX hNX U x).2 (hNeighbourhood x hx)).
exists U;split;first exact:ha.
split;first exact:hU.
move=>i;exact:(@holomorphic_open_restriction R X (ComplexScalars.C R)^o NX (@complex_modulus R)
  hNX (@complex_modulus_real_norm R) (V i) U (holomorphic_representative_value (f i))
  (fun x hx=>hx i) hOpen (hV i).2).
Qed.
