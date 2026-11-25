(** Federer (1969), 4.1.7, p. 358: the
    norm-density measure is locally finite on U.
    This supporting cover is an adapter of the
    original opaque compact exhaustion from 4.1.1,
    p. 344, to the actual relative topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology functions.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP LinearBasis
  SmoothCompactSet SmoothCompactExhaustionUP SmoothCompactExhaustionSealed
  CompactExhaustionInteriorCover IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [smooth_domain_compact_open_cover]:
    actual compact subsets C_j of U and
    open subsets W_j contained in C_j cover U,
    supporting Federer 4.1.7, p. 358, by
    the already proved compact exhaustion of 4.1.1,
    p. 344. The empty domain is included. *)
Theorem smooth_domain_compact_open_cover (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (hU:forall x,U x->norm_domain_interior NX U x):
  exists C W:nat->set (set_type (U:set (real_norm_metric_space hNX))),
    (forall j,compact (C j)) /\ (forall j,open (W j)) /\
    (forall j,W j `<=` C j) /\
    setT `<=` \bigcup_j C j /\ setT `<=` \bigcup_j W j.
Proof.
pose XT:=real_norm_metric_space hNX.
pose UT:topologicalType:=[the topologicalType of set_type (U:set XT)].
pose K:=@SmoothCompactExhaustion.value R X NX hNX n b hb U hU.
have hK:=@SmoothCompactExhaustion.laws R X NX hNX n b hb U hU.
pose C j:set UT:=set_val @^-1` smooth_compact_carrier (K j).
pose W j:set UT:=set_val @^-1` (@interior XT (smooth_compact_carrier (K j))).
have hC j:compact (C j).
  exact:(@set_type_compact_preimage XT U (smooth_compact_carrier (K j))
    (smooth_compact_is_compact (K j)) (smooth_compact_in_domain (K j))).
have hW j:open (W j).
  apply:open_comp; last exact:open_interior.
  by move=>x _; exact:set_type_val_continuous.
have hWC j:W j `<=` C j by move=>x hx; exact:interior_subset hx.
have hCover:setT `<=` \bigcup_j W j.
  move=>x _; have [j hj]:=@smooth_compact_exhaustion_interior_cover R X NX hNX U K hK
    (set_val x) (set_valP x).
  by exists j.
exists C,W; split=>//; split=>//; split=>//; split=>//.
move=>x hx; have [j _ hj]:=hCover x hx.
exists j=>//; exact:hWC j x hj.
Qed.
