(** Federer (1969), 3.4.8(10), pp. 327, 331–332:
    assemble the actual analytic representatives,
    equation ideal and geometric local model.
    The same representatives determine its
    functions, germs and variety-germ equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormDifferentialLocal
  NormFiniteLinearBound NormClassOneUP NormRegularity NormClassZeroTopology NormAnalyticUP NormAnalyticLocal
  NormAnalyticOperations AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRing AnalyticCoordinateGermsSealed AnalyticPrefixGermMap AnalyticCoordinateSubringFamilySealed
  PointedFunctionalGermExistence OrdinalCoordinateTail AnalyticPrefixCoordinatesUP AnalyticPrefixTailCoordinateLaws
  CommutativeIdealUP SetGermUP SetGermSealed AnalyticZeroGermSealed IdealVarietyGermSealed
  OriginalEquationAnalyticRepresentatives OriginalPolynomialSystemGeometry FiniteEquationOffZeroGerm
  AnalyticPrimeLocalModelUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Assembly.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation Top:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation PX:=(@analytic_representative_type R X NX hNX 0).
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation vx:=(@analytic_representative_value R X NX hNX 0).
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Hypothesis hDual:forall i j,omega i (e j) = if i==j then 1 else 0.
Variable P:Hom X Y.
Hypothesis hP:is_analytic_prefix_projection omega hMN P.
Local Notation index:=[the finType of 'I_(n-m)].
Local Notation tail:=(ordinal_coordinate_tail_index hMN).
Local Notation xi:=(fun j:index=>omega (tail j)).
Local Notation gamma:=(fun j:'I_n=>@AnalyticCoordinateGerms.value R X NX hNX n e he omega j).
Local Notation E:=(@analytic_prefix_germ_map R X NX hNX n e he omega m hMN).
Variables Ig F K:set G.
Variables (hIg:is_finitely_generated_commutative_ideal Ig)
  (hF:is_finitely_generated_commutative_ideal F) (hK:is_finitely_generated_commutative_ideal K).
Variable k:nat.
Variable first:index.
Hypothesis hFirst:(first:nat) = 0%N.
Hypothesis hPositive:(0<k)%N.
Variable U:set Y.
Hypotheses (hOrigin:U 0) (hUOpen:@open (real_norm_metric_space hNY) U).
Variable d:PY.
Variables bW:'I_k.+1->PY.
Variable bT:index->'I_k->PY.
Variables w wD s dX:PX.
Variable t:index->PX.
Local Notation A:=(fun x:X=>U (P x)).
Local Notation ANY f:=(@norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U f).
Local Notation ANX f:=(@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f).
Hypothesis hDAnalytic:ANY (vy d).
Hypothesis hBWAnalytic:forall i,ANY (vy (bW i)).
Hypothesis hBTAnalytic:forall j i,ANY (vy (bT j i)).
Hypothesis hWAnalytic:ANX (vx w).
Hypothesis hTAnalytic:forall j,ANX (vx (t j)).
Hypothesis hLeading:forall y,vy (bW ord_max) y = 1.
Hypothesis hLower:forall i:'I_k.+1,(i<k)%N ->vy (bW i) 0 = 0.
Hypothesis hWValue:forall x,vx w x = \sum_(i<k.+1) vy (bW i) (P x)*(xi first x)^+(i:nat).
Hypothesis hTValue:forall j x,vx (t j) x = \sum_(i<k) vy (bT j i) (P x)*(xi first x)^+(i:nat).
Hypothesis hDXValue:forall x,vx dX x = vy d (P x).
Hypothesis hWDerivative:forall a,A a ->exists L:Hom X R^o,
  has_norm_differential NX (fun z:R^o=>`|z|) A (vx w) a L /\
  forall u,P u = 0 ->L u = vx wD a*xi first u.
Hypothesis hIdentity:forall x,A x ->vx wD x*vx (t first) x-vx dX x = vx s x*vx w x.
Hypothesis hDeltaOutside:~Ig (E (analytic_germ d)).
Hypothesis hGenerated:is_generated_commutative_ideal
  [set alpha:G|exists j:index,alpha = if j==first then (analytic_germ w:G) else
    (analytic_germ dX:G)*gamma (tail j)-(analytic_germ (t j):G)] F.
Hypothesis hFI:F `<=` Ig.
Hypothesis hKGenerated:is_generated_commutative_ideal (Ig `|` [set alpha:G|alpha = E (analytic_germ d)]) K.
Hypothesis hVariety:@IdealVarietyGerm.value R X NX hNX 0 Ig hIg =
  @SetGerms.join Top 0 (@IdealVarietyGerm.value R X NX hNX 0 K hK)
    (@SetGerms.meet Top 0 (@IdealVarietyGerm.value R X NX hNX 0 F hF)
      (@SetGerms.neg Top 0 (@AnalyticZeroGerm.value R X NX hNX 0 (analytic_germ dX)))).
Hypothesis hLarger:forall H:set G,is_commutative_ideal H ->Ig `<=` H ->
  (exists alpha:G,H alpha /\~Ig alpha) ->exists beta:G,H beta /\
    @AnalyticCoordinateSubringFamily.value R X NX hNX n e he omega m beta /\~Ig beta /\beta<>0.

(** Source for [analytic_prime_local_model_assembly]:
    assemble the original local model of
    3.4.8(10), pp. 327, 331–332,
    from its checked algebraic and analytic
    witnesses. The same defining functions
    have the stated germs and all
    geometric conclusions; no model conclusion
    is assumed as a premise. *)
Theorem analytic_prime_local_model_assembly:
  exists (b:index->'I_k->PY) (f:index->PX) (Z:set X),
    @is_analytic_prime_local_model R n m hMN e he omega P Ig hIg k first U d b f Z K hK.
Proof.
pose lower:=fun i:'I_k=>bW (widen_ord (leqnSn k) i).
have hWMonic x:vx w x = (xi first x)^+k+
    \sum_(i<k) vy (lower i) (P x)*(xi first x)^+(i:nat).
  by rewrite hWValue big_ord_recr hLeading mul1r addrC.
have hActualIdentity x:A x ->vx wD x*vx (t first) x-vy d (P x) = vx s x*vx w x.
  move=>hx;rewrite -hDXValue;exact:hIdentity x hx.
have [f0 [Z [hF0 [hZ [hF0Analytic [hFunctional [hWD [hCompact [hFinite [hCharts hComponents]]]]]]]]]]:=
  @original_polynomial_system_geometry R n m hMN e he omega hDual P hP first k hPositive U hUOpen
    (vy d) (fun i=>vy (lower i)) (fun j i=>vy (bT j i)) hDAnalytic
    (fun i=>hBWAnalytic (widen_ord (leqnSn k) i)) hBTAnalytic
    (vx w) (vx wD) (vx s) (fun j=>vx (t j)) hWAnalytic hTAnalytic hWDerivative hWMonic hTValue hActualIdentity.
have hCoordinate j:exists v:PX,forall x,vx v x = xi j x.
  have hBound:=@norm_finite_linear_bounded R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) n e he (xi j).
  have [v hV]:=@pointed_functional_representative_exists R X NX hNX 0 (xi j) hBound.
  exists v=>x;by rewrite hV subr0.
have [v hV]:=choice hCoordinate.
have hVGerm j:(analytic_germ (v j):G) = gamma (tail j).
  exact:(@AnalyticCoordinateGerms.laws R X NX hNX n e he omega (tail j) (v j) (hV j)).
have [f [hFValue hFGerm]]:=@original_equation_analytic_representatives R X NX hNX 0 index first w dX v t.
have hEqual j x:vx (f j) x = f0 j x by rewrite hFValue hDXValue hV hF0.
have hFAnalytic j:ANX (vx (f j)).
  apply:(norm_analytic_domain_agreement _ (hF0Analytic j))=>x _;exact:esym (hEqual j x).
have hSeedEquality:[set alpha:G|exists j:index,alpha = if j==first then (analytic_germ w:G) else
      (analytic_germ dX:G)*gamma (tail j)-(analytic_germ (t j):G)] =
    [set alpha:G|exists j:index,(analytic_germ (f j):G) = alpha].
  apply/seteqP;split=>alpha [j hj];exists j.
  - rewrite hFGerm hVGerm;exact:esym hj.
  - have hG:(analytic_germ (f j):G) = if j==first then (analytic_germ w:G) else
      (analytic_germ dX:G)*gamma (tail j)-(analytic_germ (t j):G) by rewrite hFGerm hVGerm.
    by rewrite -hG;exact:esym hj.
have hGeneratedRep:is_generated_commutative_ideal [set alpha:G|exists j:index,(analytic_germ (f j):G) = alpha] F.
  by rewrite -hSeedEquality.
have hInIdeal j:Ig (analytic_germ (f j)).
  apply:hFI;apply:(generated_commutative_ideal_contains hGeneratedRep);by exists j.
have hAOrigin:A 0 by rewrite /A linear0.
have hAOpen:@open (real_norm_metric_space hNX) A.
  exact:(@norm_class_zero_domain_open R X R^o NX (fun z:R^o=>`|z|) hNX A (f0 first)
    (norm_class_continuous (norm_analytic_class_all_orders (hF0Analytic first) 0%N))).
have hOff:=@finite_equation_off_zero_germ R X NX hNX 0 F hF index f dX A
  hAOrigin hAOpen hFAnalytic hGeneratedRep.
have hSet:[set x:X|A x /\(forall j,vx (f j) x = 0) /\vx dX x!=0] = Z.
  apply/seteqP;split.
  - move=>x [hx [hZero hNonzero]];apply:(hZ x).2;split;first exact:hx.
    split.
    + move=>j;rewrite -(hEqual j x);exact:hZero j.
    + apply/eqP;by rewrite -hDXValue.
  - move=>x hx;have h:=(hZ x).1 hx;split;first exact:h.1.
    split.
    + move=>j;rewrite hEqual;exact:h.2.1 j.
    + rewrite hDXValue;apply/eqP;exact:h.2.2.
rewrite hSet in hOff.
have hVarietyFinal:@IdealVarietyGerm.value R X NX hNX 0 Ig hIg =
    @SetGerms.join Top 0 (@IdealVarietyGerm.value R X NX hNX 0 K hK) (@set_germ Top 0 Z).
  by rewrite -hOff.
pose b:=fun (j:index) (i:'I_k)=>if j==first then lower i else bT j i.
exists b,f,Z.
split;first exact:hFirst.
split;first exact:hPositive.
split;first exact:hOrigin.
split;first exact:hUOpen.
split;first exact:hDAnalytic.
split.
- move=>j i;rewrite /b;case:(j==first);[exact:hBWAnalytic|exact:hBTAnalytic].
split;first exact:hFAnalytic.
split.
- move=>i;rewrite /b eqxx;apply:hLower;exact:ltn_ord i.
split.
- move=>j x;rewrite hFValue hDXValue hV.
  case hCase:(j==first).
  + have hJ:j=first:=eqP hCase;subst j.
    by rewrite hWMonic /b eqxx.
  + by rewrite hTValue /b hCase.
split.
- move=>x;split.
  + move=>hx;have h:=(hZ x).1 hx;split;first exact:h.1.
    split.
    * move=>j;rewrite hEqual;exact:h.2.1 j.
    * apply/eqP;exact:h.2.2.
  + move=>[hx [hZero hNonzero]];apply:(hZ x).2;split;first exact:hx.
    split.
    * move=>j;rewrite -(hEqual j x);exact:hZero j.
    * apply/eqP;exact:hNonzero.
split;first exact:hDeltaOutside.
split;first exact:hInIdeal.
split;first exact:hKGenerated.
split;first exact:hVarietyFinal.
split.
- move=>x hx;have hAt:=(hZ x).1 hx.
  have [L [hL hDirections]]:=@hWDerivative x hAt.1.
  exists L;split.
  + apply:(norm_differential_domain_agreement hNX _ hL)=>z _.
    by rewrite hFValue eqxx.
  + have hTail:P (e (tail first)) = 0:=
      @analytic_prefix_original_tail_zero R X n e omega hDual m hMN P hP first.
    rewrite (hDirections _ hTail) /xi hDual eqxx mulr1;exact:hWD x hx.
split;first exact:hFunctional.
split;first exact:hCompact.
split;first exact:hFinite.
by split;[exact:hComponents|exact:hLarger].
Qed.
End Assembly.
