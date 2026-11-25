(** Federer (1969), 2.1.5, p. 57, second irregular example, witnessing
    failures of (3),(4) on three points. The concrete ambient type option
    bool has the points None, Some false, Some true. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureSplit MeasureFiniteClosure
  MeasurePushforward CountingMeasure NonnegativeSum NonnegativeSumSupport NonnegativeSumBoolean
  FullSetMeasure FullSetMeasureSingleton.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [full_set_measure_partition_counterexample]: Federer
    2.1.5, p. 57, failure of (3). A singleton and its two-point
    complement have measures one and one, and their measurable union
    has finite measure two, but neither part is measurable. *)
Theorem full_set_measure_partition_counterexample (R : realType) :
  exists A B : set (option bool),
    measure_measurable (@full_set_measure R _) (A `|` B) /\
    full_set_measure (R := R) A + full_set_measure (R := R) B = full_set_measure (R := R) (A `|` B) /\
    full_set_measure (R := R) (A `|` B) < +oo /\
    ~ measure_measurable (@full_set_measure R _) A /\
    ~ measure_measurable (@full_set_measure R _) B.
Proof.
pose A : set (option bool) := [set None].
pose B := ~` A.
have hU : A `|` B = setT by rewrite /B setUCr.
have hA : full_set_measure (R := R) A = (1 : R)%:E.
  apply: (@full_set_measure_contains_excludes R _ A None (Some false))=> //.
have hB : full_set_measure (R := R) B = (1 : R)%:E.
  apply: (@full_set_measure_contains_excludes R _ B (Some false) None).
  - by move=> h; discriminate h.
  - by move=> hn; apply: hn.
have hnA : ~ measure_measurable (@full_set_measure R _) A.
  exact: (@full_set_measure_singleton_not_measurable R _ None (Some false) (Some true) isT isT isT).
have hnB : ~ measure_measurable (@full_set_measure R _) B.
  move=> h; have hc := measure_measurable_complement h.
  rewrite /B setCK in hc; exact: hnA.
exists A, B; rewrite hU hA hB (@full_set_measure_whole R _ None).
split; first exact: (@measure_measurable_whole R _ _ (@full_set_measure_is_measure R _)).
split; first by rewrite -EFinD.
split; first exact: ltry.
by split.
Qed.

(** Source for [measure_bool_set_cases]: Federer 2.1.5(4),
    p. 57, supporting set-theoretic enumeration of the four subsets
    of the two-point target used in the second counterexample. *)
Lemma measure_bool_set_cases (D : set bool) :
  D = set0 \/ D = [set true] \/ D = [set false] \/ D = setT.
Proof.
case: (pselect (D true))=> ht; case: (pselect (D false))=> hf.
- right; right; right; apply/seteqP; split=> [b _|[] _] //.
- right; left; apply/seteqP; split.
  + move=> [|] hx; first by []; exfalso; exact: hf.
  + by move=> b ->.
- right; right; left; apply/seteqP; split.
  + move=> [|] hx; last by []; exfalso; exact: ht.
  + by move=> b ->.
- left; apply/seteqP; split=> [[|] hx|b []]; [exact: ht | exact: hf].
Qed.

(** Source for [three_point_indicator]: Federer 2.1.5(4),
    p. 57, supporting explicit map for the second counterexample.
    It sends the singleton None to true and the other two points to false. *)
Definition three_point_indicator (x : option bool) :=
  if x is None then true else false.

(** Source for [three_point_indicator_true_preimage]: Federer
    2.1.5(4), p. 57, supporting computation of the problematic inverse image. *)
Lemma three_point_indicator_true_preimage :
  three_point_indicator @^-1` [set true] = [set None].
Proof. by apply/seteqP; split=> x; case: x=> [[]|] //=. Qed.

(** Source for [three_point_indicator_false_preimage]: Federer
    2.1.5(4), p. 57, supporting computation of the complementary fibre. *)
Lemma three_point_indicator_false_preimage :
  three_point_indicator @^-1` [set false] = ~` [set None].
Proof. by apply/seteqP; split=> x; case: x=> [[]|] //=. Qed.

(** Source for [full_set_measure_image_counting]: Federer
    2.1.5(4), p. 57, supporting verification: the image under this
    two-fibre map is counting measure on the two-point target. *)
Lemma full_set_measure_image_counting (R : realType) :
  measure_pushforward three_point_indicator (@full_set_measure R _) = @counting_measure R _.
Proof.
apply: funext=> D.
have [->|[->|[->|->]]] := measure_bool_set_cases D.
- rewrite /measure_pushforward preimage_set0 full_set_measure_empty counting_measure_sum.
  by rewrite nonnegative_sum_empty.
- rewrite /measure_pushforward three_point_indicator_true_preimage counting_measure_sum nonnegative_sum_singleton; last by rewrite lee_fin ler01.
  apply: (@full_set_measure_contains_excludes R _ [set None] None (Some false))=> //.
- rewrite /measure_pushforward three_point_indicator_false_preimage counting_measure_sum nonnegative_sum_singleton; last by rewrite lee_fin ler01.
  apply: (@full_set_measure_contains_excludes R _ (~` [set None]) (Some false) None).
  + by move=> h; discriminate h.
  + by move=> hn; apply: hn.
- rewrite /measure_pushforward preimage_setT (@full_set_measure_whole R _ None)
    counting_measure_sum nonnegative_sum_bool; last by move=> b; rewrite lee_fin ler01.
  by rewrite -EFinD.
Qed.

(** Source for [full_set_measure_pushforward_counterexample]: Federer
    2.1.5, p. 57, failure of (4) without regularity despite finite
    total measure. The target singleton is image-measurable, whereas
    its inverse-image singleton is not originally measurable. *)
Theorem full_set_measure_pushforward_counterexample (R : realType) :
  full_set_measure (R := R) (@setT (option bool)) < +oo /\
  measure_measurable (measure_pushforward three_point_indicator (@full_set_measure R _)) [set true] /\
  ~ measure_measurable (@full_set_measure R _) (three_point_indicator @^-1` [set true]).
Proof.
split; first by rewrite (@full_set_measure_whole R _ None) ltry.
split.
- rewrite full_set_measure_image_counting; exact: counting_measure_measurable.
- rewrite three_point_indicator_true_preimage.
  exact: (@full_set_measure_singleton_not_measurable R _ None (Some false) (Some true) isT isT isT).
Qed.
