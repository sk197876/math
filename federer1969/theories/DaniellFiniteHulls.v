(** Federer (1969), 2.5.3, pp. 94–95: the constructed measure has equal-mass
    finite F2 hulls. We use the equivalent error bounds 1/(n+1); after
    taking the intersection, monotonicity and all those bounds give equality
    directly. This is the order-bound form of the printed limit argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP FunctionLatticeLevelFamilies FunctionLatticePrefixHulls
  FunctionLatticeRegularityUP DaniellCoverUP DaniellOuterApproximation RealIntegralFunctionalUP
  MeasureUP MeasureBasic ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [daniell_cover_finite_hull]: finite-measure hull construction
    in Federer 2.5.3, pp. 94–95 The conclusion retains both F2 membership
    and equality of finite measures. *)
Theorem daniell_cover_finite_hull (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu L A) (hc : is_daniell_cover_envelope L A mu) (S : set X) :
  mu S < +oo -> exists W, S `<=` W /\ function_lattice_finite_hulls L mu W /\
    mu S=mu W /\ mu W < +oo.
Proof.
move=> hfin.
have hfinite : mu S \is a fin_num by rewrite ge0_fin_numE //; exact: (@measure_nonnegative R X mu hm S).
pose m := fine (mu S).
have hmE : mu S=m%:E := esym (fineK hfinite).
have happ n : exists V, S `<=` V /\ function_lattice_increasing_levels L V /\
    mu V <= (m+((n.+1)%:R)^-1)%R%:E.
  apply: (@daniell_finite_outer_approximation R X L A mu hm hA hc S (m+((n.+1)%:R)^-1)%R).
  by rewrite hmE lte_fin ltrDl invr_gt0 ltr0n.
pose V n := projT1 (cid (happ n)).
have hV n : S `<=` V n /\ function_lattice_increasing_levels L (V n) /\
    mu (V n) <= (m+((n.+1)%:R)^-1)%R%:E := projT2 (cid (happ n)).
pose D n := \bigcap_(i in [set i | (i <= n)%N]) V i.
have hD n : function_lattice_increasing_levels L (D n).
  exact: (@function_lattice_prefix_hull_member R X L hL V (fun i => (hV i).2.1) n).
have hSD n : S `<=` D n by move=> x hx i hi; exact: (hV i).1 x hx.
have hmono n k : (n <= k)%N -> D k `<=` D n.
  move=> hnk x hx i hi; exact: hx i (leq_trans hi hnk).
have hDV n : D n `<=` V n by move=> x hx; exact: hx n (leqnn n).
have hDfin : mu (D 0%N) < +oo.
  apply: le_lt_trans (@measure_mono R X mu hm _ _ (hDV 0%N)) _.
  exact: le_lt_trans (hV 0%N).2.2 (ltry _).
pose W := \bigcap_n D n.
have hSW : S `<=` W by move=> x hx n _; exact: hSD n x hx.
have hWF : function_lattice_finite_hulls L mu W.
  exists D; split=> //; split=> //; by split.
have hupper : mu W <= m%:E.
  apply: extended_real_reciprocal_upper_bound=> n.
  apply: le_trans (@measure_mono R X mu hm W (V n) _) (hV n).2.2.
  move=> x hx; exact: hDV n x (hx n Logic.I).
have heq : mu S=mu W.
  apply/eqP; rewrite eq_le (@measure_mono R X mu hm S W hSW) /= hmE; exact hupper.
exists W; split=> //; split=> //; split=> //; by rewrite -heq.
Qed.

(** Source for [daniell_cover_lattice_regular]: direct L regularity of the
    constructed measure in Federer 2.5.3, pp. 94–95 This uses Federer's
    finite-hull definition. *)
Theorem daniell_cover_lattice_regular (R : realType) (X : choiceType)
    (L : set (X -> R)) (A : (X -> R) -> R) (hL : is_function_lattice L)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (hA : is_real_integral_functional mu L A) (hc : is_daniell_cover_envelope L A mu) :
  is_function_lattice_regular L mu.
Proof.
move=> S; split; first exact: (@daniell_cover_finite_hull R X L A hL mu hm hA hc S).
by move=> [W [_ [_ [heq hfin]]]]; rewrite heq.
Qed.
