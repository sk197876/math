(** Federer (1969), 3.2.28(4), printed p. 267:
    the square map is open on an antipodally symmetric
    subset of the unit sphere, onto its actual image.
    The explicit sqrt(2) lift supplies openness, with no
    manifold or compactness hypothesis needed for this step. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology lra ring.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  SymmetricGrading InnerSymmetricPositivity MetricSubsetBackground HomeomorphismUP
  MetricLocalLiftingOpen SymmetricSquareGeometry SymmetricSquareLocalLifts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenSquare.
Variable R:realType.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.
Local Notation X:=(inner_metric_space hB).
Local Notation hS:=(@symmetric_inner_productP R V B hB 2).
Local Notation Y:=(inner_metric_space hS).
Local Notation T:=(@inner_projective_square R V).
Variable A:set X.
Local Notation F:=(fun x:X=>(T x:Y)).

(** Source for [inner_projective_square_restricted_member]:
    the actual image of a source point in the openness
    argument of Federer 3.2.28(4), p. 267.
    This supporting subtype law assigns no outside value. *)
Lemma inner_projective_square_restricted_member (x:metric_subset A):
  (F @` A) (F (val x)).
Proof. exists (val x); first exact:set_valP. reflexivity. Qed.

(** Source for [inner_projective_square_restricted]: T as
    a map from the actual relative source to its image,
    supporting Federer 3.2.28(4), p. 267. *)
Definition inner_projective_square_restricted (x:metric_subset A):metric_subset (F @` A):=
  exist _ (F (val x)) (mem_set (inner_projective_square_restricted_member x)).

(** Source for [inner_projective_square_restricted_open]: the
    map T on every antipodally symmetric sphere subset is
    open onto its image, Federer 3.2.28(4), p. 267.
    The sign choice and quantitative lift have already been
    proved from the exact symmetric-power metric formula. *)
Theorem inner_projective_square_restricted_open:
  (forall x,A x ->inner_norm hB x= 1) ->
  (forall x,A x ->A (-x)) ->is_open_map inner_projective_square_restricted.
Proof.
move=>hUnit hAnti.
apply:metric_local_lifting_open=>x e he.
pose K:=Num.sqrt (2:R)+1.
have hK:0<K by rewrite /K; have:=sqrtr_ge0 (2:R); lra.
have hNon:0<=Num.sqrt (2:R):=sqrtr_ge0 _.
exists (e/K); split; first by rewrite divr_gt0.
move=>y hNear.
have [v hv hVal]:=(set_valP y).
have [z [hz [hT [hZ hBound]]]]:=
  @inner_projective_square_unit_lift R V B hB (val x) v
    (hUnit _ (set_valP x)) (hUnit v hv).
have hAz:A z.
  case:hz=>->; [exact hv|exact:hAnti v hv].
exists (exist _ z (mem_set hAz):metric_subset A); split.
- rewrite metric_subset_distanceE inner_metric_distanceE.
  change (inner_norm hB (val x-z)<e).
  rewrite -[val x-z]opprB inner_normN.
  apply:le_lt_trans hBound _.
  have hDist:inner_norm hS (T v-T (val x))<e/K.
    move:hNear; rewrite !metric_subset_distanceE inner_metric_distanceE.
    change (inner_norm hS (T (val x)-val y)<e/K ->
      inner_norm hS (T v-T (val x))<e/K).
    by rewrite -hVal -[T (val x)-T v]opprB inner_normN.
  have hLe:Num.sqrt (2:R)<=K by rewrite /K; lra.
  have hPos:=inner_norm_nonnegative hS (T v-T (val x)).
  have hSmall:K*inner_norm hS (T v-T (val x))<e.
    by rewrite mulrC -ltr_pdivlMr.
  exact:le_lt_trans (ler_wpM2r hPos hLe) hSmall.
- apply:val_inj; change (T z=val y); by rewrite hT hVal.
Qed.
End OpenSquare.
