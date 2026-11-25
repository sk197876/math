(** Federer (1969), 3.4.2(7), p. 312: reduce a relatively closed
    subset of the original manifold to countably many compact subsets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  InnerMetric HilbertFormCompactness NormMetric HomeomorphismUP InnerOwnNormTopology
  EuclideanSubmanifoldUP SubmanifoldCountableCompactCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_relatively_closed_source]: the relatively closed
    subset C of S in 3.4.2(7), p. 311. General topology expresses C
    as the intersection of S with an ambient closed set. *)
Definition is_relatively_closed_source (T:topologicalType) (S C:set T):Prop:=
  exists F:set T,closed F /\C=S `&` F.

(** Source for [relatively_closed_source_subset]: C lies in S under
    the relative closedness hypothesis of 3.4.2(7), p. 311. *)
Lemma relatively_closed_source_subset (T:topologicalType) (S C:set T):
  is_relatively_closed_source S C ->C `<=` S.
Proof. move=>[F [hF ->]] x [hx _];exact:hx. Qed.

(** Source for [critical_relatively_closed_compact_cover]: the first
    reduction in the proof of 3.4.2(7), p. 312. The original relatively
    closed C is a countable union of compact subsets contained in C.
    Local compactness of the manifold supplies the cover of S; intersect
    its members with an ambient closed representative of C. *)
Theorem critical_relatively_closed_compact_cover (R:realType) m mu k
    (S C:set (R_n R m)):
  is_euclidean_submanifold mu k S ->
  @is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) S C ->
  exists K:nat->set (R_n R m),
    (forall i,@compact (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R m))) (K i) /\K i `<=` C) /\
    C=\bigcup_i K i.
Proof.
move=>hS [F [hF hC]].
have [K [hK hCover]]:=submanifold_countable_compact_cover hS.
pose G i:=K i `&` F.
have hNormCompact i:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))) (K i).
  have h:=continuous_compact (continuous_subspaceT
    (homeomorphism_continuous (inner_own_norm_homeomorphism
      (@euclidean_inner_productP R m)))) (hK i).1.
  by rewrite image_id in h.
exists G;split.
- move=>i;split;first exact:(compact_closedI (hNormCompact i) hF).
  move=>x [hx hFx];rewrite hC;split;[exact:(hK i).2 x hx|exact:hFx].
- apply/seteqP;split.
  + move=>x hxC.
    have [hx hFx]:S x /\F x by move:hxC;rewrite hC.
    have hxUnion:(\bigcup_i K i) x by rewrite -hCover.
    have [i _ hxi]:=hxUnion.
    exists i;first exact:I.
    by split.
  + move=>x [i _ [hxi hFx]];rewrite hC;split;[exact:(hK i).2 x hxi|exact:hFx].
Qed.
