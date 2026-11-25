(** Federer (1969), 3.4.2(6), p. 312: compact source tubes contained
    in the original retraction domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealNormUP NormMetric HomeomorphismUP
  InnerOwnNormTopology FiniteNormCompactness VectorSetSum EuclideanVectorSumCompact
  MetricOpenThickening MetricCompactNeighbourhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_critical_source_tube]: the closed distance tube
    V_delta in the proof of 3.4.2(6), p. 312, specified by its source
    centres and norm bounds. For compact C this is its closed tube;
    the empty source gives the empty set. No distance function is chosen. *)
Definition is_critical_source_tube (R:realType) m (C:set (R_n R m)) e
    (T:set (R_n R m)):Prop:=
  forall x,T x <->exists c,C c /\inner_norm (@euclidean_inner_productP R m) (x-c)<=e.

(** Source for [critical_compact_source_tube_exists]: compactness of
    V_delta in 3.4.2(6), p. 312. The existing opaque vector-set sum
    of C with a compact closed ball supplies a local existence witness.
    All natural ambient dimensions and empty sources are retained. *)
Theorem critical_compact_source_tube_exists (R:realType) m (C:set (R_n R m)) e:
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  exists T,is_critical_source_tube C e T /\
    @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) T.
Proof.
move=>hC.
pose X:=R_n R m.
pose hP:=@euclidean_inner_productP R m.
pose N:=inner_norm hP;pose hN:=inner_norm_real_norm hP.
pose E:=inner_metric_space hP;pose M:=real_norm_metric_space hN.
pose B:set X:=[set w|N w<=e].
have hCInner:@compact E C.
  have h:=continuous_compact (continuous_subspaceT
    (homeomorphism_inverse_continuous (inner_own_norm_homeomorphism hP))) hC.
  by rewrite image_id in h.
have hBall:@compact E B:=@finite_norm_ball_compact R X _ hP N hN m
  (@coordinate_basis R m) (@coordinate_basisP R m) e.
pose T:=vector_set_sum C B.
have hTInner:@compact E T:=euclidean_vector_sum_compact hCInner hBall.
exists T;split.
- move=>x;split.
  + move/vector_set_sum_membership=>[c [w [hc [hw ->]]]].
    exists c;split;first exact:hc.
    by rewrite (addrC c w) addrK.
  + move=>[c [hc hBound]];apply/vector_set_sum_membership.
    exists c,(x-c);split;first exact:hc.
    split;first exact:hBound.
    by rewrite addrC subrK.
- have h:=continuous_compact (continuous_subspaceT
    (homeomorphism_continuous (inner_own_norm_homeomorphism hP))) hTInner.
  by rewrite image_id in h.
Qed.

(** Source for [critical_compact_source_tube_inside_open]: every
    sufficiently small tube about compact C stays in U, as used in
    3.4.2(6), p. 312. A uniform open thickening is derived from
    compactness; half its radius supplies the closed tube witness. *)
Theorem critical_compact_source_tube_inside_open (R:realType) m
    (C U:set (R_n R m)):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->
  @open (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) U ->C `<=` U ->
  exists e T,0<e /\is_critical_source_tube C e T /\
    @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) T /\T `<=` U.
Proof.
move=>hC hU hCU.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose M:=real_norm_metric_space hN.
have [r [hr hThick]]:=@compact_metric_open_thickening R M C U hC hU hCU.
have he:0<r/2 by rewrite divr_gt0.
have heSmall:r/2<r by lra.
have [T [hT hCompact]]:=@critical_compact_source_tube_exists R m C (r/2) hC.
exists (r/2),T;split;first exact:he.
split;first exact:hT.
split;first exact:hCompact.
move=>x hx;have [c [hc hBound]]:=(hT x).1 hx.
apply:hThick;exists c;first exact:hc.
change (is_true (N (c-x)<r)).
rewrite /N (real_seminorm_subtract hN.1 c x).
exact:(le_lt_trans hBound heSmall).
Qed.
