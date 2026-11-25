(** Federer (1969), 2.10.28(4), pp. 192–193: specialness of the equal-cost
    family Phi(J,n). Work only with the abstract family laws. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CompactIntervalGauge CompactIntervalGaugeGeometry
  ConcaveIntervalGaugeUP CantorSplitRadiusUP CantorSplitRadius EqualCostIntervalFamilyUP
  EqualCostIntervalEnumeration EqualSpacingIntervalGeometry EqualSpacingContainedSum
  SpecialIntervalFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_28_4_special]: direct specialness of Phi(J,n)
    in 2.10.28(4), p. 192, proof p. 193. Disjointness, exact mass and all
    test-interval bounds are proved from the family laws. *)
Theorem federer_2_10_28_4_special (R : realType) (h : R -> R)
    (hg : is_concave_interval_gauge h) (J : compact_real_intervals R) n F :
  is_equal_cost_interval_family h J n F -> is_special_interval_family h J F.
Proof.
move=> hPhi.
have [hn [a [b [s [t [f [hJ [hd [hs [ht [hvalue [hf hF]]]]]]]]]]]] :=
  equal_cost_interval_ordinal_enumeration hPhi.
have hab : a<=b by lra.
have hspos := (cantor_split_radius_bounds hs).1.
have hst : s<t by rewrite ht; exact: cantor_split_spacing_strict hn hs.
have hend : b-a=(n%:R-1)*t+s by rewrite ht cantor_split_last_endpoint.
have hcost := cantor_split_radius_cost hs.
have hcostf i : concave_interval_cost h (val (f i))=h s.
  rewrite hvalue; exact: equal_spacing_child_cost (ltW hspos).
constructor.
- move=> S; rewrite hF=> /imfsetP[i hi ->].
  have hh := @equal_spacing_child_in_parent R a (b-a) s t n%:R i%:R
    hspos hst hend (@ler0n R (val i))
    (@natural_index_real_upper_bound R (val i) n (ltn_ord i)).
  have he : a+(b-a)=b by lra.
  by rewrite hvalue hJ; rewrite he in hh.
- move=> S T; rewrite hF=> /imfsetP[i hi ->] /imfsetP[j hj ->] hne.
  have hij : i!=j by apply/eqP=> hij; move: hne; by rewrite hij eqxx.
  rewrite !hvalue; exact: equal_spacing_ordinal_children_disjoint hspos hst hij.
- rewrite hJ (concave_interval_cost_segment h hab) hF big_imfset /=; last first.
    by move=> i j hi hj; exact: hf.
  rewrite undup_id ?enum_uniq // big_enum.
  have hsum : (\sum_(i : 'I_n) concave_interval_cost h (val (f i)))=\sum_(i : 'I_n) h s.
    by apply: eq_bigr=> i _; rewrite hcostf.
  rewrite hsum sumr_const card_ord -mulr_natl.
  have hN : (0<n%:R :> R) by rewrite ltr0n; exact: leq_trans (leqnSn 1%N) hn.
  by rewrite hcost mulrC divfK ?gt_eqF.
- move=> T; have [u [v [huv hT]]] := set_valP T.
  rewrite hT (concave_interval_cost_segment h huv) big_mkcond /= hF big_imfset /=; last first.
    by move=> i j hi hj; exact: hf.
  rewrite undup_id ?enum_uniq // big_enum.
  have he (i : 'I_n) : `[< val (f i) `<=` (`[u,v] : set (real_line_metric R)) >]=
      ((u<=a+i%:R*t) && (a+i%:R*t+s<=v)).
    apply/idP/idP.
    + move=> /asboolP hi.
      have hch : a+i%:R*t<=a+i%:R*t+s by lra.
      rewrite hvalue in hi.
      have [hl hr] := (@compact_segment_subset_endpoints R _ _ _ _ hch).1 hi.
      by apply/andP; split.
    + move=> /andP[hl hr]; apply/asboolP; rewrite hvalue.
      have hch : a+i%:R*t<=a+i%:R*t+s by lra.
      apply: (@compact_segment_subset_endpoints R _ _ _ _ hch).2; by split.
  have hsum : (\sum_(i : 'I_n) if `[< val (f i) `<=` (`[u,v] : set (real_line_metric R)) >]
      then concave_interval_cost h (val (f i)) else 0)=
      \sum_(i : 'I_n | (u<=a+i%:R*t) && (a+i%:R*t+s<=v)) h s.
    rewrite [RHS]big_mkcond /=; apply: eq_bigr=> i _; by rewrite he hcostf.
  rewrite hsum.
  apply: (@equal_spacing_contained_sum_bound R h hg n a (b-a) s t u v hn hd hspos hst hcost _ huv).
  exact ht.
Qed.
