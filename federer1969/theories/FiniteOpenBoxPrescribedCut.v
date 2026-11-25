(** Federer (1969), 3.2.41, printed p. 277, choice of b:
    a finite nonempty disjoint box union admits a coordinate cut
    with any prescribed strict relative mass. Continuity, finite
    normalization and both actual cut values are proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology normedtype lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RealMetricBackground FiniteDisjointOpenBoxFamilyUP FiniteDisjointOpenBoxVolume
  FiniteOpenBoxCumulative FiniteRealEndpointBounds EuclideanCoordinateHalfspaces
  EuclideanLebesgueDimensions MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_open_box_prescribed_fraction_cut]: supporting
    proved choice of b in Federer 3.2.41, p. 277. The original
    union and its two strict cuts have exactly the stated actual
    volumes. The relative fraction lies strictly between zero and
    one; positivity and finiteness of the original mass are derived
    from its genuine nonempty proper-box family. *)
Theorem finite_open_box_prescribed_fraction_cut (R:realType) n (I:finType)
    (a b:I->R_n R n)
    (G:I->set (inner_metric_space (@euclidean_inner_productP R n)))
    (i0:I) (k:'I_n) (lambda:R):
  is_finite_disjoint_open_box_family a b G ->0<lambda ->lambda<1 ->
  exists t:R,
    @euclidean_lebesgue_measure R n ((\bigcup_i G i) `&` [set x|x k<t])=
      (lambda*fine (@euclidean_lebesgue_measure R n (\bigcup_i G i)))%:E /\
    @euclidean_lebesgue_measure R n ((\bigcup_i G i) `&` [set x|t<x k])=
      ((1-lambda)*fine (@euclidean_lebesgue_measure R n (\bigcup_i G i)))%:E.
Proof.
move=> hG hLambda hLambda1.
pose E:=inner_metric_space (@euclidean_inner_productP R n).
pose mu:=@euclidean_lebesgue_measure R n.
pose A:set E:=\bigcup_i G i.
have hm:=euclidean_lebesgue_is_measure R n.
have /andP[hPositive hFinite]:=@finite_disjoint_open_box_union_positive_finite R n I a b G i0 hG.
have hFiniteNum:mu A \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm A)); exact hFinite.
pose M:R:=fine (mu A).
have hMass:mu A=M%:E by rewrite /M fineK.
have hM:0<M by move:hPositive; rewrite -/(mu A) hMass lte_fin.
have [F [hCont hValues]]:=@finite_open_box_left_cumulative_exists R n I a b G k hG.
have hCDF t:mu (A `&` [set x:E|x k<t])=(F t)%:E:=hValues t.
have [l [u [hLU hBounds]]]:=@finite_real_endpoint_bounds R I (fun i=>a i k) (fun i=>b i k).
have hEmpty:A `&` [set x:E|x k<l]=set0.
  apply/seteqP; split; last by move=> x [].
  move=> x [[i _ hi] hCut].
  have /andP[hLow _]:=((finite_disjoint_open_box_law hG i).2 x).1 hi k.
  have hBad:(l<l):=lt_trans (le_lt_trans (hBounds i).1 hLow) hCut.
  by rewrite ltxx in hBad.
have hWhole:A `&` [set x:E|x k<u]=A.
  apply/seteqP; split=> x hx; first exact hx.1.
  split=>//; have [i _ hi]:=hx.
  have /andP[_ hHigh]:=((finite_disjoint_open_box_law hG i).2 x).1 hi k.
  exact:lt_le_trans hHigh (hBounds i).2.
have hFL:F l=0.
  apply:EFin_inj; by rewrite -(hCDF l) hEmpty /mu (measure_empty hm).
have hFU:F u=M.
  apply:EFin_inj; by rewrite -(hCDF u) hWhole hMass.
pose q:R:=lambda*M.
have hQ:0<q by rewrite /q; exact:mulr_gt0 hLambda hM.
have hQM:q<M by rewrite /q -[X in _<X]mul1r ltr_pM2r.
have hMin:Order.min 0 M=0:=min_l (ltW hM).
have hMax:Order.max 0 M=M:=max_r (ltW hM).
have hRange:Order.min (F l) (F u)<=q<=Order.max (F l) (F u).
  by rewrite hFL hFU ?hMin ?hMax (ltW hQ) (ltW hQM).
have [t ht hFT]:=@IVT R F l u q (ltW hLU) (continuous_subspaceT hCont) hRange.
have hLeft:mu (A `&` [set x:E|x k<t])=q%:E by rewrite hCDF hFT.
have hRightNum:mu (A `&` [set x:E|t<x k]) \is a fin_num.
  rewrite (ge0_fin_numE (measure_nonnegative hm _)).
  have hBelow:(mu (A `&` [set x:E|(t<x k)%R])<=mu A)%E.
    apply:(@measure_mono R E mu hm); by move=> x hx; exact hx.1.
  exact:(le_lt_trans hBelow hFinite).
have hRight:mu (A `&` [set x:E|t<x k])=(fine (mu (A `&` [set x:E|t<x k])))%:E.
  by rewrite fineK.
have hSplit:=@euclidean_coordinate_halfspace_volume_split R n k t A.
change (mu A=(mu (A `&` [set x:E|(x k<t)%R])+mu (A `&` [set x:E|(t<x k)%R]))%E) in hSplit.
rewrite hMass hLeft hRight -EFinD in hSplit.
have hScalar:M=q+fine (mu (A `&` [set x:E|t<x k])):=EFin_inj hSplit.
have hR:fine (mu (A `&` [set x:E|t<x k]))=(1-lambda)*M.
  rewrite /q in hScalar; nra.
exists t; split; first exact hLeft.
exact:(eq_trans hRight (congr1 (fun v:R=>v%:E) hR)).
Qed.
