(** Federer (1969), 3.4.2(6), p. 312: one compact tube and a
    finite Lipschitz bound suffice for the positive-radius limit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness RealNormUP NormMetric HomeomorphismUP
  InnerOwnNormTopology NormDifferentialUP NormClassOneUP NormClassZeroTopology
  InnerClassOneCompactLipschitz LipschitzUP CriticalCompactTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_source_tube_contains_source]: the original
    compact C lies in each tube of nonnegative radius, as used in
    3.4.2(6), p. 312. The statement uses only the tube's defining law. *)
Lemma critical_source_tube_contains_source (R:realType) m (C T:set (R_n R m)) e:
  is_critical_source_tube C e T ->0<=e ->C `<=` T.
Proof.
move=>hTube he c hc;apply:(hTube c).2;exists c;split;first exact:hc.
by rewrite subrr inner_norm0.
Qed.

(** Source for [critical_source_tube_interior]: a point at distance
    strictly below the tube radius is interior to that tube, supporting
    the derivative bound for the retracted segment in 3.4.2(6), p. 312. *)
Lemma critical_source_tube_interior (R:realType) m (C T:set (R_n R m)) e c x:
  is_critical_source_tube C e T ->C c ->
  inner_norm (@euclidean_inner_productP R m) (x-c)<e ->
  norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) T x.
Proof.
move=>hTube hc hx.
pose N:=inner_norm (@euclidean_inner_productP R m).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
exists (e-N (x-c));split;first by rewrite subr_gt0.
move=>v hv;apply:(hTube (x+v)).2;exists c;split;first exact:hc.
have hSum:x+v-c=(x-c)+v by rewrite addrAC.
rewrite hSum.
have hTriangle:=real_seminorm_triangle hN.1 (x-c) v.
rewrite /N in hv.
apply:(le_trans hTriangle);lra.
Qed.

(** Source for [critical_compact_tube_lipschitz_bound]: the finite
    bound for r on a sufficiently small compact tube in 3.4.2(6),
    p. 312. Class one gives local Lipschitz bounds; compactness gives
    one finite bound. Increase it to at least one and keep this fixed
    tube and constant while smaller cutoffs tend to zero. *)
Theorem critical_compact_tube_lipschitz_bound (R:realType) m
    (C U:set (R_n R m)) (r:R_n R m->R_n R m):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) C ->C `<=` U ->
  norm_class_one (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) U r ->
  exists e T M,0<e /\1<=M /\is_critical_source_tube C e T /\
    @compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) T /\T `<=` U /\
    forall x y,T x ->T y ->
      inner_norm (@euclidean_inner_productP R m) (r x-r y)<=
        M*inner_norm (@euclidean_inner_productP R m) (x-y).
Proof.
move=>hC hCU hR.
pose X:=R_n R m;pose hP:=@euclidean_inner_productP R m.
pose N:=inner_norm hP;pose hN:=inner_norm_real_norm hP.
have hU:@open (real_norm_metric_space hN) U.
  have [D hField]:=hR.
  exact:(@norm_class_zero_domain_open R X X N N hN U r (norm_class_one_zero hField)).
have [e [T [he [hTube [hCompact hTU]]]]]:=
  @critical_compact_source_tube_inside_open R m C U hC hU hCU.
have hInner:@compact (inner_metric_space hP) T.
  have h:=continuous_compact (continuous_subspaceT
    (homeomorphism_inverse_continuous (inner_own_norm_homeomorphism hP))) hCompact.
  by rewrite image_id in h.
have [L [hL [hL0 hBound]]]:=@inner_class_one_compact_lipschitz R X X _ _ hP hP
  U T r hR hTU hInner.
exists e,T,(L+1);split;first exact:he.
split;first by lra.
split;first exact:hTube.
split;first exact:hCompact.
split;first exact:hTU.
move=>x y hx hy.
have h:=hBound x y hx hy.
rewrite !inner_metric_distanceE in h.
have hNorm:0<=inner_norm hP (x-y):=inner_norm_nonnegative hP (x-y).
nra.
Qed.
