(** Federer (1969), 2.9.11, p. 158: choose a phi hull of A before comparing
    its density with a characteristic function. Here the original class M
    permits a Borel hull, obtained from finite local hulls on the bounded
    Borel partition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureHull MeasureDerivationContext
  BorelRegularMeasureUP TopologicalBorel BorelFamilyBasic CommonBorelHulls
  BoundedBorelPartitionUP BoundedBorelPartition MeasureDisjointIntersectionSum NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [derivation_measure_borel_hull]: supporting hull choice at
    the start of the proof of Federer 2.9.11, p. 158 The target A is
    arbitrary and may have infinite measure. Equal total mass alone is not
    used to assert a hull at infinity: every measurable test-set equality is
    proved by summing finite local hull laws. *)
Theorem derivation_measure_borel_hull (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (A : set X) :
  is_derivation_measure phi -> exists B, borel_set B /\ is_measure_hull phi A B.
Proof.
move=> hphi; have hm := derivation_measure_law hphi.
have hr := derivation_measure_borel_regular hphi.
have [P hP] := @bounded_borel_partition_exists R X.
have hPb n := @bounded_borel_partition_borel R X P hP n.
have hPm n := @borel_regular_borel_measurable R X phi hm hr (P n) (hPb n).
have hPd n m hne x : P n x -> P m x -> False :=
  @bounded_borel_partition_disjoint R X P hP n m hne x.
have hex n : exists H, borel_set H /\ (A `&` P n) `<=` H /\ H `<=` P n /\
    phi (A `&` P n)=phi H.
  have [H [hHb [hAH [hHP [he _]]]]] := @common_borel_hull_inside R X phi phi (P n)
    (A `&` P n) hm hm hr hr (hPb n) (fun x hx => hx.2).
  by exists H; split=> //; split=> //; split.
pose H n := projT1 (cid (hex n)).
have hH n : borel_set (H n) /\ (A `&` P n) `<=` H n /\ H n `<=` P n /\
    phi (A `&` P n)=phi (H n) := projT2 (cid (hex n)).
have hHm n := @borel_regular_borel_measurable R X phi hm hr (H n) (hH n).1.
have hHhull n : is_measure_hull phi (A `&` P n) (H n).
  apply: (@measure_hull_of_finite_equal_measure R X phi hm _ _ (hH n).2.1 (hHm n) (hH n).2.2.2).
  apply: le_lt_trans (@measure_mono R X phi hm (A `&` P n) (P n) (fun x hx => hx.2)) _.
  exact: derivation_measure_bounded_finite hphi (P n) (@bounded_borel_partition_bounded R X P hP n).
have hHd n m hne x (hx : H n x) (hy : H m x) : False :=
  hPd n m hne x ((hH n).2.2.1 x hx) ((hH m).2.2.1 x hy).
pose B := \bigcup_n H n.
have hBb : borel_set B.
  apply: (@borel_set_countable_union X nat setT H (countableP _))=> n _; exact: (hH n).1.
have hAB : A `<=` B.
  move=> x hx.
  have hxP : (\bigcup_n P n) x by rewrite (@bounded_borel_partition_union R X P hP).
  have [n _ hn] := hxP; exists n=> //; apply: (hH n).2.1; by split.
exists B; split=> //; constructor=> //.
- exact (@borel_regular_borel_measurable R X phi hm hr B hBb).
- move=> T hT.
  have hleft := @measure_disjoint_union_intersection_sum R X phi P hm hPm hPd (T `&` A).
  rewrite (@bounded_borel_partition_union R X P hP) setTI in hleft.
  have hright := @measure_disjoint_union_intersection_sum R X phi H hm hHm hHd T.
  rewrite hleft (setIC T B) /B hright.
  apply: nonnegative_sum_ext=> n _.
  have he : P n `&` (T `&` A)=T `&` (A `&` P n).
    apply/seteqP; split=> x; [move=> [hp [ht ha]]|move=> [ht [ha hp]]]; by split=> //; split.
  rewrite he (setIC (H n) T).
  exact (@measure_hull_test R X phi (A `&` P n) (H n) (hHhull n) T hT).
Qed.
