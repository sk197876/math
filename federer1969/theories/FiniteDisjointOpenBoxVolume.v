(** Federer (1969), 3.2.41, printed p. 277, finite-family
    proof: the volume of the actual disjoint union is the sum
    of its box volumes. Positivity and finiteness are proved,
    not additional hypotheses of the induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanOpenCoordinateBoxUP EuclideanOpenCoordinateBoxMeasure
  EuclideanOpenBoxMeasurability FiniteDisjointOpenBoxFamilyUP
  MeasureUP MeasureBasic MeasureCountableClosure FiniteNullOverlapAdditivity
  FiniteCoverMeasureBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_disjoint_open_box_union_measurable]: supporting
    measurable finite unions in Federer 3.2.41, p. 277. The
    possibly empty finite family is included. *)
Lemma finite_disjoint_open_box_union_measurable (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->
  measure_measurable (@euclidean_lebesgue_measure R n) (\bigcup_i G i).
Proof.
move=> hG; apply:(measure_measurable_countable_union (euclidean_lebesgue_is_measure R n)
  (finite_set_countable (@finite_finset I setT)))=> i _.
exact:open_coordinate_box_measurable (finite_disjoint_open_box_law hG i).
Qed.

(** Source for [finite_disjoint_open_box_union_volume]: supporting
    actual finite sum in Federer 3.2.41, p. 277. All original
    side lengths enter their products; no volume is axiomatized. *)
Lemma finite_disjoint_open_box_union_volume (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))):
  is_finite_disjoint_open_box_family a b G ->
  @euclidean_lebesgue_measure R n (\bigcup_i G i)=
    (\sum_i \prod_j (b i j-a i j))%R%:E.
Proof.
move=> hG.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
have hMeas i:=open_coordinate_box_measurable (finite_disjoint_open_box_law hG i).
have hNull i j:i!=j ->mu (G i `&` G j)=0%E.
  move=> hNe.
  have hEmpty:G i `&` G j=set0.
    apply/seteqP; split; last by move=> x [].
    move=> x [hi hj]; exact:(@finite_disjoint_open_box_disjoint_law R n I a b G hG i j hNe x hi hj).
  by rewrite hEmpty /mu (measure_empty hm).
have hAdd:=@measure_finite_family_null_overlap_additivity R E I mu hm G setT
  (@finite_finset I setT) (fun i _=>hMeas i) (fun i j _ _=>hNull i j).
rewrite (@finite_type_nonnegative_sum R I (fun i=>mu (G i))
  (fun i=>measure_nonnegative hm (G i))) in hAdd.
rewrite /mu in hAdd.
rewrite hAdd (eq_bigr _ (fun i _=>open_coordinate_box_volume
  (finite_disjoint_open_box_law hG i))) sumEFin.
reflexivity.
Qed.

(** Source for [finite_disjoint_open_box_union_positive_finite]:
    supporting legal relative-mass normalization in Federer 3.2.41,
    p. 277. An actual member supplies positivity; the exact finite
    scalar sum supplies finiteness. *)
Lemma finite_disjoint_open_box_union_positive_finite (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))) (i:I):
  is_finite_disjoint_open_box_family a b G ->
  (0<@euclidean_lebesgue_measure R n (\bigcup_j G j) < +oo)%E.
Proof.
move=> hG; apply/andP; split.
- have hPos:=(andP (open_coordinate_box_positive_finite_volume
    (finite_disjoint_open_box_law hG i))).1.
  apply:lt_le_trans hPos _; apply:(@measure_mono R _ _ (euclidean_lebesgue_is_measure R n)).
  move=> x hx; by exists i.
- rewrite (finite_disjoint_open_box_union_volume hG); exact:ltry.
Qed.
