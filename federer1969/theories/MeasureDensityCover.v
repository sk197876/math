(** Federer (1969), 2.4.10, p. 85: the upper- integral density set function
    measures X, even when the density is not measurable. We use arbitrary
    countable index sets directly and the project's geometric error budget
    from 2.2.2. The corrected approximant convention is explained in
    MeasureNonnegativeUpperApproximation.v. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialZeroExtension
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialExtendedOrderLoci MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureDensityUP MeasureDensityBounds ZeroExtensionNonnegative
  MeasureNonnegativeUpperApproximation PartialDensityCoverComparison PartialNumericalSum
  MeasureCountableNonnegativeSum MeasureUpperIntegralMonotone NonnegativeSum NonnegativeSumAdd CountableGeometricBudget.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_density_countable_cover]: the countable covering
    inequality establishing that psi measures X in Federer 2.4.10, p. 85 No
    measurability is assumed for the covering sets. *)
Lemma measure_density_countable_cover (R : realType) (X J : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) (D : set J) (A : set X) (B : J -> set X) :
  is_measure_density mu h nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus h) ->
  countable D -> A `<=` \bigcup_(j in D) B j -> nu A <= nonnegative_sum D (fun j => nu (B j)).
Proof.
move=> hn hp hD hcover.
have hn0 C := @measure_density_nonnegative R X mu nu hm h hn hp C.
have hsum0 := @nonnegative_sum_nonnegative R J D (fun j => nu (B j)).
case hs: (nonnegative_sum D (fun j => nu (B j)))=> [r| |]; last by move: hsum0; rewrite hs.
2: exact: leey.
apply/lee_addgt0Pr=> e he.
have [b [hb hbsum]] := @countable_geometric_error_budget R J D e hD he.
have happ j : exists p : partial_function X (extended_real_line R) * R,
    D j -> (forall x y, partial_function_graph p.1 x y -> 0 <= y) /\
      is_measure_integral mu p.1 p.2%:E /\
      measure_almost_everywhere mu (partial_extended_le_locus
        (partial_function_zero_extension (0 : extended_real_line R) (B j) h) p.1) /\
      p.2%:E < nu (B j)+(b j)%:E.
  have [hj|hj] := pselect (D j); last by exists (@partial_function_empty X (extended_real_line R),0%R).
  have hfinite : nu (B j) < +oo.
    apply: le_lt_trans (@nonnegative_sum_term R J D (fun j => nu (B j)) j hj) _.
    by rewrite hs ltry.
  have hfupper : measure_upper_integral mu
      (partial_function_zero_extension (0 : extended_real_line R) (B j) h) < +oo.
    change (measure_subset_upper_integral mu (B j) h < +oo).
    by rewrite -(hn (B j)).
  have [v [a hv]] := @measure_nonnegative_upper_approximation R X mu hm
    (partial_function_zero_extension (0 : extended_real_line R) (B j) h) (b j)
    (@zero_extension_nonnegative_almost R X mu hm (B j) h hp)
    hfupper (hb j).
  exists (v,a)=> _; rewrite (hn (B j)); exact hv.
pose p j := projT1 (cid (happ j)).
have hpc j := projT2 (cid (happ j)).
pose v j := (p j).1.
pose a j := ((p j).2)%:E.
pose s := partial_function_numerical_sum D v.
have hvp j (hj : D j) : forall x y, partial_function_graph (v j) x y -> 0 <= y := (hpc j hj).1.
have hvi j (hj : D j) : is_measure_integral mu (v j) (a j) := (hpc j hj).2.1.
have hsi := @measure_countable_nonnegative_integral_values R X J mu hm D v s a hD
  (partial_function_numerical_sum_laws D v) hvp hvi.
have horder : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_function_zero_extension (0 : extended_real_line R) A h) s).
  have hall := @measure_almost_everywhere_countable R X J mu hm D
    (fun j => partial_extended_le_locus
      (partial_function_zero_extension (0 : extended_real_line R) (B j) h) (v j))
    hD (fun j hj => (hpc j hj).2.2.1).
  apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
    (@measure_almost_everywhere_and R X mu hm _ _ hp hall)).
  move=> x [hx hxj]; exact (@partial_density_cover_sum_order R X J D A B h v s x
    hcover (partial_function_numerical_sum_laws D v) hvp hx hxj).
have hsumupper := @measure_upper_integral_unique R X mu s _ _ (measure_upper_integral_specification mu s) hsi.2.1.
have hfirst : nu A <= nonnegative_sum D a.
  rewrite (hn A) -hsumupper; exact (@measure_upper_integral_monotone R X mu hm _ s horder).
apply: le_trans hfirst _.
have happrox : nonnegative_sum D a <= nonnegative_sum D (fun j => nu (B j)+(b j)%:E).
  apply: nonnegative_sum_mono=> j hj; exact: ltW (hpc j hj).2.2.2.
apply: le_trans happrox _.
have hnu j (_ : D j) := hn0 (B j).
have hb0 j (_ : D j) : 0 <= (b j)%:E := ltW (hb j).
rewrite (@nonnegative_sum_add R J D (fun j => nu (B j)) (fun j => (b j)%:E) hnu hb0) hs.
apply: leeD (lexx _) _; apply: le_trans hbsum _.
rewrite lee_fin ler_pdivrMr ?ltr0n // mulr_natr; by rewrite lerDl; exact: ltW he.
Qed.

(** Source for [measure_density_is_measure]: direct assertion
    that psi measures X in Federer 2.4.10, p. 85,
    for an almost-everywhere nonnegative, possibly nonmeasurable density. *)
Theorem measure_density_is_measure (R : realType) (X : choiceType)
    (mu nu : set X -> \bar R) (hm : is_measure mu)
    (h : partial_function X (extended_real_line R)) :
  is_measure_density mu h nu -> measure_almost_everywhere mu (partial_extended_nonnegative_locus h) -> is_measure nu.
Proof.
move=> hn hp; constructor; first exact (@measure_density_nonnegative R X mu nu hm h hn hp).
move=> A F hF hcover.
exact (@measure_density_countable_cover R X [the choiceType of set X] mu nu hm h F A (fun B => B) hn hp hF hcover).
Qed.
