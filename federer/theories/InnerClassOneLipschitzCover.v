(** Federer (1969), 3.2.47, p. 283: supporting
    finite local Lipschitz refinements of the actual smooth
    product charts. Class one implies a local bound by
    3.1.1 and 3.1.11, pp. 210–211,222;
    compactness supplies a finite cover, including an empty compact set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp finmap classical_sets topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  RealNormUP NormClassOneUP NormClassOneLocalLipschitz
  CoveringFamilyUP MetricClosedBalls CompactFiniteCover LipschitzUP LipschitzBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_class_one_local_lipschitz_patch]: every
    domain point has an actual open metric neighborhood inside
    the original domain on which the original map is Lipschitz;
    supporting the product-chart argument of 3.2.47, p. 283. *)
Lemma inner_class_one_local_lipschitz_patch (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    (A:set V) (f:V->W) a:
  A a ->norm_class_one (inner_norm hB) (inner_norm hC) A f ->
  exists U:set (inner_metric_space hB),@open (inner_metric_space hB) U /\
    U a /\U `<=` A /\@is_metric_lipschitz R (inner_metric_space hB) (inner_metric_space hC) U f.
Proof.
move=>ha hf.
have [L [d [hL [hd [hDomain hBound]]]]]:=@norm_class_one_local_lipschitz R V W
  (inner_norm hB) (inner_norm hC) (inner_norm_real_norm hB) (inner_norm_real_norm hC) A f a ha hf.
pose U:=@metric_open_ball R (inner_metric_space hB) a d.
have hNorm (x:inner_metric_space hB) (hx:U x):inner_norm hB (x-a)<d.
  change (is_true (inner_norm hB (a-x)<d)) in hx.
  by rewrite (real_seminorm_subtract (inner_norm_real_norm hB).1).
exists U; split; first exact:metric_open_ball_open.
split.
- change (is_true (inner_norm hB (a-a)<d)).
  rewrite subrr; have hZero:inner_norm hB (0:V)=0 by apply/eqP; rewrite inner_norm_eq0.
  by rewrite hZero.
- split.
  + move=>x hx; exact:hDomain x (hNorm x hx).
  + apply:metric_lipschitz_of_bound; split; first exact:ltW hL.
    move=>x y hx hy; rewrite !inner_metric_distanceE.
    exact:hBound x y (hNorm x hx) (hNorm y hy).
Qed.

(** Source for [inner_class_one_compact_lipschitz_cover]: every
    actual compact part of a smooth product chart is covered
    by finitely many open subsets of its original domain with
    proved finite Lipschitz bounds, supporting 3.2.47, p. 283.
    No bound on the whole printed open patch is assumed. *)
Theorem inner_class_one_compact_lipschitz_cover (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    (A K:set V) (f:V->W):
  norm_class_one (inner_norm hB) (inner_norm hC) A f ->K `<=` A ->
  @compact [the topologicalType of inner_metric_space hB] K ->
  exists F:{fset set (inner_metric_space hB)},
    (forall U,U \in F ->@open (inner_metric_space hB) U /\U `<=` A /\
      @is_metric_lipschitz R (inner_metric_space hB) (inner_metric_space hC) U f) /\
    K `<=` \bigcup_(U in [set` F]) U.
Proof.
move=>hf hKA hK.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space hC.
pose D:set (set X):=[set U:set X|@open [the topologicalType of X] U /\U `<=` A /\@is_metric_lipschitz R X Y U f].
have hCover:K `<=` \bigcup_(U in D) U.
  move=>a ha.
  have [U [hU [haU [hUA hLip]]]]:=
    @inner_class_one_local_lipschitz_patch R V W B C hB hC A f a (hKA a ha) hf.
  exists U; first by split; last split.
  exact haU.
have [F hFD hFK]:=@compact_open_finite_cover [the topologicalType of X]
  [the choiceType of set X] D id K hK (fun U hU=>hU.1) hCover.
exists F; split; last exact hFK.
move=>U hU; have hDU:D U by apply/set_mem; exact:hFD U hU.
exact hDU.
Qed.
