(** Federer (1969), 3.4.8(10), pp. 331–332:
    the original polynomial zero system has
    its printed regularity, prescribed projection
    charts, compact finite fibres and component
    homeomorphisms. Apply the checked equations,
    coordinate bounds and ordered-fibre theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex RealMetricBackground ScalarNormExtendedEmbedding
  NormDifferentialUP NormClassOneUP NormRegularity NormBoundedLinearTopology NormClassZeroNonzeroLocus
  NormFiniteLinearBound NormAnalyticUP NormAnalyticLocal NormCoordinateSystemUP FunctionalAnalyticSubmanifoldUP
  AnalyticPrefixCoordinatesUP OrdinalCoordinateTail AnalyticPrefixSuffixSeparation AnalyticPrefixTailCoordinateLaws
  OriginalFunctionalPolynomialSystem OriginalPolynomialEquationDifferentials OriginalJointCoordinateSeparation
  OriginalPolynomialCompactFibres OriginalPolynomialFiniteFibres OriginalPolynomialFibreSeparation AnalyticEquationProjectionChartDimension
  NormCoordinateRelativeLocalInverse FiniteNormOpenCompactNeighbourhood RelativeLocalInverseUP
  MetricSubsetBackground HomeomorphismUP FiniteOrderedProjectionComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalGeometry.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable P:Hom X Y.
Hypothesis hP:is_analytic_prefix_projection omega hMN P.
Local Notation index:=[the finType of 'I_(n-m)].
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Local Notation xi:=(fun j:index=>omega (tail j)).
Variable first:index.
Variable k:nat.
Hypothesis hK:(0<k)%N.
Variable U:set Y.
Hypothesis hUOpen:@open (real_norm_metric_space hNY) U.
Variable delta:Y->R.
Variable b0:'I_k->Y->R.
Variable b:index->'I_k->Y->R.
Hypothesis hDelta:@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U delta.
Hypothesis hB0:forall i,@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U (b0 i).
Hypothesis hB:forall j i,@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U (b j i).
Local Notation A:=(fun x:X=>U (P x)).
Local Notation V:=(fun y:Y=>U y /\delta y!=0).
Local Notation AN f:=(@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f).
Variables w wD s:X->R.
Variable t:index->X->R.
Hypothesis hWAnalytic:AN w.
Hypothesis hTAnalytic:forall j,AN (t j).
Hypothesis hW:forall a,A a ->exists L:Hom X R^o,
  has_norm_differential NX (fun z:R^o=>`|z|) A w a L /\
  forall u,P u = 0 ->L u = wD a*xi first u.
Hypothesis hWValue:forall x,w x = (xi first x)^+k+\sum_(i<k) b0 i (P x)*(xi first x)^+(i:nat).
Hypothesis hTValue:forall j x,t j x = \sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
Hypothesis hIdentity:forall x,A x ->wD x*t first x-delta (P x) = s x*w x.

(** Source for [original_polynomial_system_geometry]:
    all geometric assertions for the actual
    polynomial zero system in 3.4.8(10),
    pp. 331–332. The original basis,
    coordinate covectors and projection remain.
    No compactness, finite-fibre, chart or
    component-homeomorphism conclusion is a premise. *)
Theorem original_polynomial_system_geometry:
  exists (f:index->X->R) (Z:set X),
    (forall j x,f j x = if j==first then w x else delta (P x)*xi j x-t j x) /\
    (forall x,Z x <->A x /\(forall j,f j x = 0) /\delta (P x)<>0) /\
    (forall j,AN (f j)) /\is_functional_analytic_submanifold m A Z /\
    (forall x,Z x ->wD x!=0) /\
    (forall C:set Y,compact [set y:real_norm_metric_space hNY|C y] ->C `<=` V ->
      compact [set x:real_norm_metric_space hNX|Z x /\C (P x)]) /\
    (forall y:Y,finite_set [set x|Z x /\P x = y] /\
      forall q:seq X,uniq q ->(forall x,x \in q ->Z x /\P x = y) ->(size q<=k)%N) /\
    (forall a,Z a ->exists (O:set X) (W:set Y) (psi:Y->X),
      O a /\is_inner_convex W /\@norm_analytic R X Y NX NY hNX hNY O P /\
      @norm_analytic R Y X NY NX hNY hNX W psi /\
      is_norm_coordinate_system hNX hNY Z O W P psi 1%N) /\
    forall x,Z x ->exists F:metric_subset [set a:real_norm_metric_space hNX|
        @connected_component (real_norm_metric_space hNX) Z x a]->
      metric_subset [set y:real_norm_metric_space hNY|
        @connected_component (real_norm_metric_space hNY) V (P x) y],
      (forall a,val (F a) = P (val a)) /\is_homeomorphism F.
Proof.
have hPBound:=@norm_finite_linear_bounded R X Y NX NY hNX hNY n e he P.
have hXiBound j:=@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
  (@scalar_absolute_value_norm R) n e he (xi j).
pose v:=fun j:index=>e (tail j).
have hV j:P (v j) = 0:=@analytic_prefix_original_tail_zero R X n e omega hDual m hMN P hP j.
have hTailDual i j:xi i (v j) = if i==j then 1 else 0:=
  @analytic_original_tail_duality R X n e omega hDual m hMN i j.
have [f [Z [hF [hZ [hFAnalytic [hDeltaPull [hFunctional hWD]]]]]]]:=
  @original_polynomial_functional_submanifold R n m hMN first Y NY hNY U hUOpen P hPBound
    xi hXiBound v hV hTailDual k b delta hB hDelta w wD s t hWAnalytic hTAnalytic hW hTValue hIdentity.
have hNonzero x:Z x ->delta (P x)!=0 by move=>hx;apply/eqP;exact:((hZ x).1 hx).2.2.
have hRoot x:Z x ->(xi first x)^+k+\sum_(i<k) b0 i (P x)*(xi first x)^+(i:nat) = 0.
  move=>hx;rewrite -hWValue.
  have h:=((hZ x).1 hx).2.1 first;by rewrite hF eqxx in h.
have hRelations x:Z x ->forall j,j!=first ->
    delta (P x)*xi j x = \sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
  move=>hx j hJ;have h:=((hZ x).1 hx).2.1 j.
  rewrite hF (negbTE hJ) hTValue in h.
  apply/eqP;by rewrite -subr_eq0 h eqxx.
have hCompact C:compact [set y:real_norm_metric_space hNY|C y] ->C `<=` V ->
    compact [set x:real_norm_metric_space hNX|Z x /\C (P x)].
  move=>hC hCV.
  have hCU:C `<=` U by move=>y hy;exact:(hCV y hy).1.
  have hDC y:C y ->delta y!=0 by move=>hy;exact:(hCV y hy).2.
  exact:(@original_polynomial_compact_fibres R X NX hNX n m e he omega hDual hMN P hP first k hK
    U C delta b0 b Z hC hCU hDC hDelta hB0 hB f
    (fun j=>norm_class_continuous (norm_analytic_class_all_orders (hFAnalytic j) 0%N)) hZ hRoot hRelations).
have hFinite y:=@original_polynomial_finite_fibres R X n m e he omega hDual hMN P hP first k
  delta b0 b Z hNonzero hRoot hRelations y.
have hU y (hy:U y):norm_domain_interior NY U y.
  have h:=hUOpen;rewrite openE in h.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY U y).2 (h y hy)).
have hJoint a:Z a ->exists D:index->Hom X R^o,
    (forall j,has_norm_differential NX (fun z:R^o=>`|z|) A (f j) a (D j)) /\
    forall u,P u = 0 ->(forall j,D j u = 0) ->u=0.
  move=>ha;have hAt:=((hZ a).1 ha).1.
  have [D [hD hDirections]]:=@original_polynomial_equation_differentials R X Y NX NY hNX hNY
    U hU P hPBound index first xi hXiBound k b delta hB hDelta w wD hW t hTValue f hF a hAt.
  exists D;split;first exact:hD.
  apply:(@original_joint_coordinate_separation R X Y index first P xi D (delta (P a)) (wD a)
    (fun j=>\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)
    _ hDirections (hNonzero a ha) (hWD a ha)).
  exact:(@analytic_prefix_suffix_separate R X n e he omega hDual m hMN P hP).
have hCharts a:Z a ->exists (O:set X) (W:set Y) (psi:Y->X),
    O a /\is_inner_convex W /\@norm_analytic R X Y NX NY hNX hNY O P /\
    @norm_analytic R Y X NY NX hNY hNX W psi /\
    is_norm_coordinate_system hNX hNY Z O W P psi 1%N.
  move=>ha.
  have [O [W [psi [hO [_ hRest]]]]]:=@analytic_equation_projection_chart_any_dimension R n m hMN
    A Z P f (fun x=>delta (P x)) hPBound hFAnalytic hDeltaPull hZ hJoint a ha.
  by exists O,W,psi;split.
have hLocalCharts x:Z x ->exists O W psi,
    @is_relative_local_inverse (real_norm_metric_space hNX) (real_norm_metric_space hNY) P Z x O W psi.
  move=>hx;have [O [W [psi [hO [_ [_ [_ hChart]]]]]]]:=hCharts x hx.
  exists O,W,psi;exact:(@norm_coordinate_relative_local_inverse R X Y NX NY hNX hNY Z O W P psi 1%N x hx hO hChart).
have hBaseOpen:@open (real_norm_metric_space hNY) V:=
  @norm_class_zero_nonzero_locus_open R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R)
    U delta (norm_class_continuous (norm_analytic_class_all_orders hDelta 0%N)).
have hNeighbour y:V y ->exists C:set Y,nbhs (y:real_norm_metric_space hNY) C /\
    compact [set x:real_norm_metric_space hNX|Z x /\C (P x)].
  move=>hy;have [C [hC [hCCompact hCV]]]:=@finite_norm_open_compact_neighbourhood R Y NY hNY
    m (@coordinate_basis R m) (@coordinate_basisP R m) V y hBaseOpen hy.
  exists C;split;first exact:hC.
  exact:hCompact C hCCompact hCV.
have hPContinuous:=@norm_bounded_linear_continuous R X Y NX NY hNX hNY P hPBound.
have hXiContinuous:continuous (fun x:real_norm_metric_space hNX=>(xi first x:real_line_metric R)).
  move=>x;apply:continuous_comp
    (@norm_bounded_linear_continuous R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R)
      (xi first) (hXiBound first) x) (@scalar_norm_real_identity_continuous R (xi first x)).
have hInjective x z:Z x ->Z z ->P x = P z ->xi first x=xi first z ->x=z.
  move=>hx hz hPx hFirst.
  pose numer:=fun j:index=>\sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
  have hX j (hj:j!=first):delta (P x)*xi j x = numer j:=hRelations x hx j hj.
  have hZZ j (hj:j!=first):delta (P x)*xi j z = numer j.
    have h:=hRelations z hz j hj;by rewrite -hPx -hFirst in h.
  exact:(@original_polynomial_fibre_separation R X n m e he omega hDual hMN P hP first
    x z (delta (P x)) numer (hNonzero x hx) hPx hFirst hX hZZ).
have hComponents:=@finite_ordered_projection_components R (real_norm_metric_space hNX)
  (real_norm_metric_space hNY) P Z V (xi first) 0 hPContinuous hXiContinuous hBaseOpen
  (fun x hx=>conj ((hZ x).1 hx).1 (hNonzero x hx)) (fun y _=>(hFinite y).1)
  hInjective hNeighbour hLocalCharts.
exists f,Z;split;first exact:hF.
split;first exact:hZ.
split;first exact:hFAnalytic.
split;first exact:hFunctional.
split;first exact:hWD.
split;first exact:hCompact.
split;first exact:hFinite.
by split;[exact:hCharts|exact:hComponents].
Qed.
End OriginalGeometry.
