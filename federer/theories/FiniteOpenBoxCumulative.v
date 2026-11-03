(** Federer (1969), 3.2.41, printed p. 277, choice of b:
    the volume of a finite disjoint box union cut by x_i<b is
    a continuous real function of b. Prove this fact from actual
    clipped interval lengths before choosing a prescribed fraction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology normedtype.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanLebesgueDimensions EuclideanLebesgueBoxes
  EuclideanOpenBoxMeasurability EuclideanOpenBoxCutVolume EuclideanCoordinateHalfspaces
  ScalarOpenIntervalCuts FiniteDisjointOpenBoxFamilyUP MeasureUP MeasureBasic
  MeasureFiniteClosure FiniteNullOverlapAdditivity FiniteCoverMeasureBounds TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_left_cumulative_exists]: supporting
    continuous coordinate-volume function used in Federer 3.2.41,
    p. 277. Its exact original-set values are proved by actual
    finite disjoint additivity and coordinate product measure.
    The finite sum is only a local existence witness, and the
    empty-family boundary is retained. *)
Theorem finite_open_box_left_cumulative_exists (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n))) (k:'I_n):
  is_finite_disjoint_open_box_family a b G ->
  exists F:R->R,
    continuous (F:real_line_metric R->real_line_metric R) /\
    forall t:R,@euclidean_lebesgue_measure R n
      ((\bigcup_i G i) `&` [set x|x k<t])=(F t)%:E.
Proof.
move=> hG.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
pose F(t:R):R:=\sum_i Order.max 0 (Order.min (b i k) t-a i k)*
  (\prod_(j |j!=k) (b i j-a i j)).
exists F; split.
- change (continuous (fun t:R^o=>(\sum_i Order.max 0
    (Order.min (b i k) t-a i k)*(\prod_(j |j!=k) (b i j-a i j)):R^o))).
  apply:continuous_big; first exact:add_continuous.
  move=> i _ t.
  apply:(@continuousM R [the topologicalType of real_line_metric R]
    (fun t=>Order.max 0 (Order.min (b i k) t-a i k))
    (fun _=>\prod_(j |j!=k) (b i j-a i j)) t).
  + exact:scalar_interval_left_cut_continuous.
  + exact:cvg_cst.
- move=> t.
  pose C i:set E:=G i `&` [set x|x k<t].
  have hMeas i:measure_measurable mu (C i).
    apply:(measure_measurable_intersection hm
      (open_coordinate_box_measurable (finite_disjoint_open_box_law hG i))).
    exact:euclidean_borel_measurable (open_borel_set
      (@euclidean_coordinate_lower_halfspace_open R n k t)).
  have hNull i j:i!=j ->mu (C i `&` C j)=0%E.
    move=> hNe.
    have hEmpty:C i `&` C j=set0.
      apply/seteqP; split; last by move=> x [].
      move=> x [[hi _] [hj _]].
      exact:(@finite_disjoint_open_box_disjoint_law R n I a b G hG i j hNe x hi hj).
    by rewrite hEmpty /mu (measure_empty hm).
  have hAdd:=@measure_finite_family_null_overlap_additivity R E I mu hm C setT
    (@finite_finset I setT) (fun i _=>hMeas i) (fun i j _ _=>hNull i j).
  rewrite (@finite_type_nonnegative_sum R I (fun i=>mu (C i))
    (fun i=>measure_nonnegative hm (C i))) /mu in hAdd.
  have hUnion:(\bigcup_i G i) `&` [set x|x k<t]=\bigcup_i C i.
    apply/seteqP; split.
    + move=> x [[i _ hi] hCut]; exists i=>//; by split.
    + move=> x [i _ [hi hCut]]; split=>//; by exists i.
  rewrite hUnion hAdd (eq_bigr _ (fun i _=>
    @open_coordinate_box_left_cut_volume R n (a i) (b i) (G i) k t
      (finite_disjoint_open_box_law hG i))) sumEFin.
  reflexivity.
Qed.
