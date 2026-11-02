(** Federer (1969), proof of 2.4.6, p. 84: the explicitly displayed
    finite-family assertion for positive y_i and disjoint measurable A_i
    below the lower limit. We use finite sets of arbitrary indices,
    including the empty family, and keep infinite measures. Source context:
    ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP
  PartialFunctionLimitExtremaUP MeasureUP MeasureBasic MeasureAlmostUP
  MeasurableFunctionUP PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureUpperIntegralNonnegative MeasureContinuityBelow
  ExtendedLowerLimitUP ExtendedLowerLimit ExtendedPositiveWeightLimit ExtendedFiniteIncreasingBounds
  ExtendedContractionSqueeze FatouTailSets MeasureFiniteSimpleComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_fatou_finite_family]: direct finite-
    family assertion in the proof of Federer 2.4.6, p. 84,
    with the common domain made explicit for partial functions. *)
Lemma measure_fatou_finite_family (R : realType) (X I : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) (a : nat -> \bar R)
    (C : {fset I}) (A : I -> set X) (y : I -> R) :
  is_partial_function_lower_limit f g ->
  (forall n, measure_almost_everywhere mu (partial_extended_nonnegative_locus (f n))) ->
  (forall n, is_measure_integral mu (f n) (a n)) ->
  (forall i, i \in C -> measure_measurable mu (A i)) ->
  (forall i j, i \in C -> j \in C -> i != j -> forall x, A i x -> A j x -> False) ->
  (forall i, i \in C -> (0 < y i)%R) ->
  (forall i, i \in C -> forall x, A i x -> forall n, partial_function_domain (f n) x) ->
  (forall i, i \in C -> forall x, A i x ->
    exists z, partial_function_graph g x z /\ (y i)%:E <= z) ->
  (\sum_(i <- C) (y i)%:E*mu (A i)) <= extended_lower_limit a.
Proof.
move=> hg hp hi hA hd hy hdom hlow.
have ha n : 0 <= a n.
  have he := @measure_upper_integral_unique R X mu (f n) _ (a n)
    (measure_upper_integral_specification mu (f n)) (hi n).2.1.
  rewrite -he; exact (@measure_upper_integral_nonnegative R X mu hm (f n) (hp n)).
have hL : 0 <= extended_lower_limit a.
  apply: (extended_lower_limit_eventual_bound (extended_lower_limit_laws a)).
  exists 0%N=> n _; exact: ha.
apply: (@extended_contraction_squeeze R _ _ hL)=> t /andP[ht0 ht1].
pose B i n := fatou_tail_set f (A i) (t*y i)%:E n.
have hB i : i \in C -> forall n, measure_measurable mu (B i n).
  move=> hii n; exact (@fatou_tail_set_measurable R X mu hm f (A i) (t*y i)%:E n
    (fun k => (hi k).1) (hA i hii)).
have hinc i : forall n m, (n <= m)%N -> B i n `<=` B i m.
  move=> n m hnm; exact: fatou_tail_set_increasing hnm.
have hcover i : i \in C -> (\bigcup_n B i n) = A i.
  move=> hii; apply: (@fatou_tail_set_exhaustion R X f g (A i) _ hg (hdom i hii))=> x hx.
  have [z [hz hyz]] := hlow i hii x hx; exists z; split=> //.
  have hty : (t*y i < 1*y i)%R by rewrite ltr_pM2r //; exact: hy i hii.
  rewrite mul1r in hty; apply: lt_le_trans _ hyz; by rewrite lte_fin.
have hweight i : i \in C -> (0 < t*y i)%R.
  move=> hii; exact: mulr_gt0 ht0 (hy i hii).
have hlim i : i \in C -> extended_increases_to
    (fun n => (t*y i)%:E*mu (B i n)) ((t*y i)%:E*mu (A i)).
  move=> hii; apply: extended_positive_weight_increases (hweight i hii) _.
  have h := @measure_continuity_below R X mu hm (B i) (hB i hii) (hinc i).
  by rewrite (hcover i hii) in h.
have hs : (\sum_(i <- C) (t*y i)%:E*mu (A i)) <= extended_lower_limit a.
  apply: (@nonnegative_increasing_finite_lower_limit R I C
    (fun i n => (t*y i)%:E*mu (B i n)) (fun i => (t*y i)%:E*mu (A i)) a)=> //.
  - move=> i hii n; apply: mule_ge0; first by rewrite lee_fin; exact: ltW (hweight i hii).
    exact: measure_nonnegative.
  - move=> n; apply: (@measure_finite_simple_lower_bound R X I mu hm C
      (fun i => B i n) (fun i => (t*y i)%R) (f n) (a n))=> //.
    + move=> i hii; exact: hB i hii n.
    + move=> i j hii hj hne x [hix _] [hjx _]; exact: hd i j hii hj hne x hix hjx.
    + move=> i hii x [_ hx]; have [z [hz htz]] := hx n (leqnn n).
      exists z; split=> //; exact: ltW htz.
have he : t%:E*(\sum_(i <- C) (y i)%:E*mu (A i)) = \sum_(i <- C) (t*y i)%:E*mu (A i).
  rewrite !big_seq ge0_sume_distrr.
  - apply: eq_bigr=> i _; by rewrite muleA -EFinM.
  - move=> i hii; apply: mule_ge0; first by rewrite lee_fin; exact: ltW (hy i hii).
    exact: measure_nonnegative.
by rewrite he.
Qed.
