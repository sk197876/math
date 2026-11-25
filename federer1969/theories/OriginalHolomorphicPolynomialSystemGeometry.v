(** Federer (1969), 3.4.12, p. 339: the actual original
    polynomial zero system has independent complex differentials,
    compact finite fibres, prescribed holomorphic projection charts
    and k local holomorphic sheets. Reuse the checked original
    equations, coordinate bounds, inverse and closed-field root count.
    Global ordered sheets are not asserted over complex bases. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis FiniteCoordinates
  ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm ComplexOrderedBases
  HolomorphicCoordinateNorm HolomorphicUP HolomorphicLinear HolomorphicDifferentialRestriction NormDifferentialUP NormClassOneUP
  NormRegularity NormBoundedLinearTopology NormClassZeroNonzeroLocus NormFiniteLinearBound NormAnalyticLocal
  InnerConvex NormCoordinateSystemUP FunctionalHolomorphicSubmanifoldUP FieldPrefixCoordinatesUP
  OrdinalCoordinateTail FieldPrefixSuffixSeparation FieldPrefixTailCoordinateLaws
  OriginalFunctionalHolomorphicPolynomialSystem OriginalHolomorphicPolynomialEquationDifferentials
  FieldJointCoordinateSeparation OriginalComplexPolynomialCompactFibres FieldPolynomialFiniteFibres
  HolomorphicEquationProjectionChartDimension HolomorphicPolynomialDerivativeValue
  ClosedFieldPolynomialSystemFibres ComplexScalarAlgebraicClosure FiniteFibreEnumerationUP
  HolomorphicFiniteCoverUP FiniteHolomorphicProjectionCoverAssembly
  NormCoordinateRelativeLocalInverse FiniteNormOpenCompactNeighbourhood RelativeLocalInverseUP.
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
Local Notation K:=(ComplexScalars.C R).
Local Notation X:=(coordinate_space K n).
Local Notation Y:=(coordinate_space K m).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation NY:=(@holomorphic_coordinate_norm R m).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation hNY:=(complex_norm_real (@holomorphic_coordinate_norm_laws R m)).
Local Notation XR:=(restricted_space (ComplexScalars.embed R) X).
Local Notation YR:=(restricted_space (ComplexScalars.embed R) Y).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) K^o).
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X K^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable P:Hom X Y.
Hypothesis hP:is_field_prefix_projection omega hMN P.
Local Notation index:=[the finType of 'I_(n-m)].
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Local Notation xi:=(fun j:index=>omega (tail j)).
Variable first:index.
Variable k:nat.
Hypothesis hK:(0<k)%N.
Variable U:set Y.
Hypothesis hUOpen:@open (real_norm_metric_space hNY) U.
Variable delta:Y->K.
Variable bW:'I_k.+1->Y->K.
Hypothesis hLeading:forall y,bW ord_max y = 1.
Local Notation b0:=(fun (i:'I_k) y=>bW (widen_ord (leqnSn k) i) y).
Variable b:index->'I_k->Y->K.
Hypothesis hDelta:@is_holomorphic R Y K^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U delta.
Hypothesis hBW:forall i,@is_holomorphic R Y K^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U (bW i).
Hypothesis hB:forall j i,@is_holomorphic R Y K^o NY (@complex_modulus R) hNY (@complex_modulus_real_norm R) U (b j i).
Local Notation A:=(fun x:X=>U (P x)).
Local Notation V:=(fun y:Y=>U y /\delta y!=0).
Local Notation AN f:=(@is_holomorphic R X K^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f).
Variables w wD s:X->K.
Variable t:index->X->K.
Hypothesis hWAnalytic:AN w.
Hypothesis hTAnalytic:forall j,AN (t j).
Hypothesis hW:forall a,A a ->exists L:Hom XR CR,
  @has_norm_differential R XR CR NX (@complex_modulus R) A w a L /\
  forall u,P u = 0 ->L u = wD a*xi first u.
Hypothesis hWValue:forall x,w x = (xi first x)^+k+\sum_(i<k) b0 i (P x)*(xi first x)^+(i:nat).
Hypothesis hTValue:forall j x,t j x = \sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
Hypothesis hIdentity:forall x,A x ->wD x*t first x-delta (P x) = s x*w x.

(** Source for [original_holomorphic_polynomial_system_geometry]:
    all geometric assertions for the actual
    polynomial zero system in 3.4.12, p. 339, extending 3.4.8(10),
    pp. 331–332. The original basis,
    coordinate covectors and projection remain.
    No compactness, finite-fibre, chart or
    covering conclusion is a premise. *)
Theorem original_holomorphic_polynomial_system_geometry:
  exists (f:index->X->K) (Z:set X),
    (forall j x,f j x = if j==first then w x else delta (P x)*xi j x-t j x) /\
    (forall x,Z x <->A x /\(forall j,f j x = 0) /\delta (P x)<>0) /\
    (forall j,AN (f j)) /\is_functional_holomorphic_submanifold m A Z /\
    (forall x,Z x ->wD x!=0) /\
    (forall C:set Y,compact [set y:real_norm_metric_space hNY|C y] ->C `<=` V ->
      compact [set x:real_norm_metric_space hNX|Z x /\C (P x)]) /\
    (forall y:Y,finite_set [set x|Z x /\P x = y] /\
      forall q:seq X,uniq q ->(forall x,x \in q ->Z x /\P x = y) ->(size q<=k)%N) /\
    (forall a,Z a ->exists (O:set X) (W:set Y) (psi:Y->X),
      O a /\@is_inner_convex R YR W /\@is_holomorphic R X Y NX NY hNX hNY O P /\
      @is_holomorphic R Y X NY NX hNY hNX W psi /\
      is_norm_coordinate_system hNX hNY Z O W P psi 1%N) /\
    @is_finite_holomorphic_projection_cover R X Y NX NY hNX hNY Z V P k.
Proof.
have hB0 i:=hBW (widen_ord (leqnSn k) i).
have hPBound:=@norm_finite_linear_bounded R XR YR NX NY hNX hNY (n+n)
  (ordered_real_basis e) (ordered_real_basisP he) (complex_hom_real P).
have hXiBound j:=@norm_finite_linear_bounded R XR CR NX (@complex_modulus R) hNX
  (@complex_modulus_real_norm R) (n+n) (ordered_real_basis e) (ordered_real_basisP he) (complex_hom_real (xi j)).
pose v:=fun j:index=>e (tail j).
have hV j:P (v j) = 0:=@field_prefix_original_tail_zero K X n e omega hDual m hMN P hP j.
have hTailDual i j:xi i (v j) = if i==j then 1 else 0:=
  @field_original_tail_duality K X n e omega hDual m hMN i j.
have [f [Z [hF [hZ [hFAnalytic [hDeltaPull [hFunctional hWD]]]]]]]:=
  @original_holomorphic_polynomial_functional_submanifold R n m hMN first Y NY hNY U hUOpen P hPBound
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
  exact:(@original_complex_polynomial_compact_fibres R X NX (@holomorphic_coordinate_norm_laws R n) n m e he omega hDual hMN P hP first k hK
    U C delta b0 b Z hC hCU hDC hDelta.1 (fun i=>(hB0 i).1) (fun j i=>(hB j i).1) hRoot hRelations f
    (fun j=>norm_class_continuous (norm_analytic_class_all_orders (hFAnalytic j).1 0%N)) hZ).
have hFinite y:=@field_polynomial_finite_fibres K X n m e he omega hDual hMN P hP first k
  delta b0 b Z hNonzero hRoot hRelations y.
have hU y (hy:U y):@norm_domain_interior R YR NY U y.
  have h:=hUOpen;rewrite openE in h.
  exact:((@norm_domain_interior_neighbourhood R YR NY hNY U y).2 (h y hy)).
have hJoint a:Z a ->exists D:index->Hom XR CR,
    (forall j,@has_norm_differential R XR CR NX (@complex_modulus R) A (f j) a (D j)) /\
    forall u,P u = 0 ->(forall j,D j u = 0) ->u=0.
  move=>ha;have hAt:=((hZ a).1 ha).1.
  have [D [hD hDirections]]:=@original_holomorphic_polynomial_equation_differentials R X Y NX NY hNX hNY
    U hU P hPBound index first xi hXiBound k b delta hB hDelta w wD hW t hTValue f hF a hAt.
  have hLiftExists j:exists E:Hom X K^o,complex_hom_real E=D j.
    exact:(@holomorphic_actual_differential_complex_restriction R X K^o NX (@complex_modulus R)
      hNX (@complex_modulus_real_norm R) A (f j) a (D j) (hFAnalytic j) (hD j)).
  have [E hE]:=choice hLiftExists.
  have hEDirections j u (hZero:P u=0):E j u=if j==first then wD a*xi first u else
      delta (P a)*xi j u-(\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)*xi first u.
    change (complex_hom_real (E j) u=if j==first then wD a*xi first u else
      delta (P a)*xi j u-(\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)*xi first u).
    rewrite hE;exact:hDirections j u hZero.
  exists D;split;first exact:hD.
  have hSeparation:=@field_joint_coordinate_separation K X Y index first P xi E
    (delta (P a)) (wD a)
    (fun j=>\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)
    (@field_prefix_suffix_separate K X n e he omega hDual m hMN P hP)
    hEDirections
    (hNonzero a ha) (hWD a ha).
  move=>u hZero hAll;apply:(@hSeparation u hZero)=>j.
  change (complex_hom_real (E j) u=0);by rewrite hE hAll.
have hCharts a:Z a ->exists (O:set X) (W:set Y) (psi:Y->X),
    O a /\@is_inner_convex R YR W /\@is_holomorphic R X Y NX NY hNX hNY O P /\
    @is_holomorphic R Y X NY NX hNY hNX W psi /\
    is_norm_coordinate_system hNX hNY Z O W P psi 1%N.
  move=>ha.
  have [O [W [psi [hO [_ hRest]]]]]:=@holomorphic_equation_projection_chart_any_dimension R n m hMN
    A Z P f (fun x=>delta (P x)) hPBound hFAnalytic hDeltaPull hZ hJoint a ha.
  by exists O,W,psi;split.
have hLocalCharts x:Z x ->exists O W psi,
    @is_relative_local_inverse (real_norm_metric_space hNX) (real_norm_metric_space hNY) P Z x O W psi.
  move=>hx;have [O [W [psi [hO [_ [_ [_ hChart]]]]]]]:=hCharts x hx.
  exists O,W,psi;exact:(@norm_coordinate_relative_local_inverse R XR YR NX NY hNX hNY Z O W P psi 1%N x hx hO hChart).
have hBaseOpen:@open (real_norm_metric_space hNY) V:=
  @norm_class_zero_nonzero_locus_open R YR CR NY (@complex_modulus R) hNY (@complex_modulus_real_norm R)
    U delta (norm_class_continuous (norm_analytic_class_all_orders hDelta.1 0%N)).
have hNeighbour y:V y ->exists C:set Y,nbhs (y:real_norm_metric_space hNY) C /\
    compact [set x:real_norm_metric_space hNX|Z x /\C (P x)].
  move=>hy;have [C [hC [hCCompact hCV]]]:=@finite_norm_open_compact_neighbourhood R YR NY hNY
    (m+m) (ordered_real_basis (@coordinate_basis K m)) (ordered_real_basisP (@coordinate_basisP K m)) V y hBaseOpen hy.
  exists C;split;first exact:hC.
  exact:hCompact C hCCompact hCV.
have hPContinuous:=@norm_bounded_linear_continuous R XR YR NX NY hNX hNY (complex_hom_real P) hPBound.
have hStructured x:Z x <->U (P x) /\
    ((xi first x)^+k+\sum_(i<k) b0 i (P x)*(xi first x)^+(i:nat)=0) /\
    (forall j,j!=first ->delta (P x)*xi j x=\sum_(i<k) b j i (P x)*(xi first x)^+(i:nat)) /\delta (P x)!=0.
  split.
  - move=>hx;split;first exact:((hZ x).1 hx).1.
    split;first exact:hRoot x hx.
    split;first exact:hRelations x hx;exact:hNonzero x hx.
  - move=>[hx [hRootX [hRelationsX hDeltaX]]];apply:(hZ x).2;split;first exact:hx.
    split;last by apply/eqP;exact:hDeltaX.
    move=>j;rewrite hF;case hCase:(j==first).
    + by rewrite hWValue hRootX.
    + have hOther:j!=first by rewrite hCase.
      by rewrite hTValue (hRelationsX j hOther) subrr.
have hFullValue x:w x=\sum_(i<k.+1) bW i (P x)*(xi first x)^+(i:nat).
  by rewrite hWValue big_ord_recr hLeading mul1r addrC.
have hDerivativeValue:=@holomorphic_polynomial_actual_derivative_value R X Y NX NY hNX hNY
  U P (xi first) k.+1 bW w wD (v first) hU hPBound (hXiBound first) hBW hFullValue
  (hV first) (ltac:(by rewrite hTailDual eqxx)) hW.
have hSimple x (hx:Z x):
    (\sum_(i<k.+1) (i:nat)%:R*bW i (P x)*(xi first x)^+(i:nat).-1)<>0.
  rewrite -(hDerivativeValue x ((hZ x).1 hx).1);apply/eqP;exact:hWD x hx.
have hEnumeration y (hy:V y):exists a:'I_k->X,is_finite_fibre_enumeration P Z y a.
  exact:(@closed_field_polynomial_system_fibres K (@complex_scalar_algebraically_closed R)
    X n m hMN e he omega hDual P hP first k U delta bW b Z hLeading hStructured hSimple y hy.1 hy.2).
have hChartsHol x (hx:Z x):exists (O:set (real_norm_metric_space hNX))
    (W:set (real_norm_metric_space hNY)) (psi:Y->X),
    @is_relative_local_inverse (real_norm_metric_space hNX) (real_norm_metric_space hNY) P Z x O W psi /\
    @is_holomorphic R Y X NY NX hNY hNX W psi.
  have [O [W [psi [hO [_ [_ [hPsi hChart]]]]]]]:=hCharts x hx.
  exists O,W,psi;split;last exact:hPsi.
  exact:(@norm_coordinate_relative_local_inverse R XR YR NX NY hNX hNY Z O W P psi 1%N x hx hO hChart).
have hCover:=@finite_holomorphic_projection_cover_assembly R X Y NX NY hNX hNY P Z V k
  hPContinuous hBaseOpen (fun x hx=>conj ((hZ x).1 hx).1 (hNonzero x hx))
  hEnumeration hNeighbour hChartsHol.
exists f,Z;split;first exact:hF.
split;first exact:hZ.
split;first exact:hFAnalytic.
split;first exact:hFunctional.
split;first exact:hWD.
split;first exact:hCompact.
split;first exact:hFinite.
by split;[exact:hCharts|exact:hCover].
Qed.
End OriginalGeometry.
