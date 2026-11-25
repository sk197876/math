(** Federer (1969), 3.2.29, pp. 267–268: supporting
    passage from individual Lipschitz images to countable
    almost covers, keeping arbitrary source sets. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanSubmanifoldUP RectifiableManifoldCoverUP HausdorffMeasure MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_cover_almost_transfer]: supporting
    the almost-cover convention in Federer 3.2.29,
    p. 267. A null excess over a set already covered
    almost everywhere remains null; the sets need not be measurable. *)
Lemma submanifold_cover_almost_transfer (R:realType) n m k (W S:set (R_n R n)):
  measure_almost_included (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W S ->
  has_countable_submanifold_measure_cover m k S ->has_countable_submanifold_measure_cover m k W.
Proof.
move=>hWS [C hC]; exists C; constructor.
- exact:submanifold_measure_cover_countable hC.
- exact:submanifold_measure_cover_class hC.
- pose mu:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
  pose hm:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
  apply:(measure_null_subset hm _ (measure_null_union hm hWS (submanifold_measure_cover_almost hC))).
  move=>x [hx hn]; case:(pselect (S x))=>hS.
  + right; by split.
  + left; by split.
Qed.

(** Source for [submanifold_cover_subset]: supporting subset
    passage in Federer 3.2.29, p. 268, from a
    global extended image to its original Lipschitz partial image. *)
Lemma submanifold_cover_subset (R:realType) n m k (W S:set (R_n R n)):
  W `<=` S ->has_countable_submanifold_measure_cover m k S ->
  has_countable_submanifold_measure_cover m k W.
Proof.
move=>hWS; apply:submanifold_cover_almost_transfer.
have hEmpty:W `\` S=set0 by apply/seteqP; split=>[x [hx hn]|x []]; exact:False_ind _ (hn (hWS x hx)).
rewrite /measure_almost_included hEmpty; exact:measure_empty (@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m).
Qed.

(** Source for [submanifold_cover_countable_union]: the countable
    union reduction implicit in Federer 3.2.29, pp. 267–268.
    Families and their choices remain local to this proved existence
    theorem. Null remainders are united only countably. *)
Theorem submanifold_cover_countable_union (R:realType) n m k (I:choiceType)
    (D:set I) (F:I->set (R_n R n)):
  countable D ->(forall i,D i ->has_countable_submanifold_measure_cover m k (F i)) ->
  has_countable_submanifold_measure_cover m k (\bigcup_(i in D) F i).
Proof.
move=>hD hF.
pose mu:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
pose hm:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hex i:exists C:set (set (R_n R n)),countable C /\
    (forall S,C S ->@is_euclidean_submanifold R n m k S) /\
    (D i ->mu (F i `\` \bigcup_(S in C) S)=0%E).
  case:(pselect (D i))=>hi.
  - have [C hC]:=hF i hi; exists C; split; first exact:submanifold_measure_cover_countable hC.
    split; first exact:submanifold_measure_cover_class hC.
    move=>_; exact:submanifold_measure_cover_almost hC.
  - exists set0; split; first exact:countable0.
    split; first by move=>S [].
    by move=>/hi.
have [C hC]:=choice hex.
exists (\bigcup_(i in D) C i); constructor.
- apply:bigcup_countable hD _=>i hi; exact:(hC i).1.
- move=>S [i hi hS]; exact:(hC i).2.1 S hS.
- have hZero:=@measure_null_countable_union R (inner_metric_space (@euclidean_inner_productP R n)) I
    mu hm D (fun i=>F i `\` \bigcup_(S in C i) S) hD (fun i hi=>(hC i).2.2 hi).
  apply:(measure_null_subset hm _ hZero).
  move=>x [[i hi hx] hn]; exists i; first exact hi.
  split; first exact hx.
  move=>[S hS hxS]; apply:hn; exists S; last exact hxS.
  by exists i.
Qed.
