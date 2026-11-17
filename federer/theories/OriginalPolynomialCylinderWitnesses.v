(** Federer (1969), 3.4.8(10), pp. 327, 331:
    the original monic polynomial, derivative,
    bounded numerators and denominator have actual
    representatives on one connected prefix cylinder.
    Existing representative and identity theorems
    supply every witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormBoundedLinearTopology NormLinearDomainLaws NormDifferentialLocal NormAnalyticUP NormAnalyticLinear NormAnalyticOperations
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing AnalyticGermRingLaws
  PointedAnalyticPullbackUP FiniteAnalyticNeighbourhood PointedPolynomialAnalyticRepresentative
  PointedPolynomialAnalyticFamily AnalyticPrefixPolynomialWitnesses DistinguishedCoefficientRepresentatives
  NormPrefixBallNeighbourhood AnalyticGermProductIdentity OriginalPolynomialInverseIdentity
  CommutativePolynomialUP CommutativePolynomialDegreeUP CommutativePolynomialEvaluationUP
  CommutativeFactorizationUP FormalPolynomialDerivativeUP DistinguishedPolynomialUP AnalyticGermValueSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CylinderWitnesses.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable projection:Hom X Y.
Local Notation A:=[the comNzRingType of (@analytic_germ_ring R Y NY hNY 0)].
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation PY:=(@analytic_representative_type R Y NY hNY 0).
Local Notation PX:=(@analytic_representative_type R X NX hNX 0).
Local Notation vy:=(@analytic_representative_value R Y NY hNY 0).
Local Notation vx:=(@analytic_representative_value R X NX hNX 0).
Local Notation ANX U f:=(@norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) U f).
Local Notation ANY U f:=(@norm_analytic R Y R^o NY (fun t=>`|t|) hNY (@scalar_absolute_value_norm R) U f).
Variable E:{rmorphism A->G}.
Hypothesis hE:is_pointed_analytic_germ_pullback projection E.
Hypothesis hProjection:norm_bounded_linear NX NY projection.
Variable xi:Hom X R^o.
Hypothesis hXi:norm_bounded_linear NX (fun t:R^o=>`|t|) xi.
Variable fXi:PX.
Hypothesis hXiValues:forall x,vx fXi x = xi x.
Variable P:comNzRingType.
Variable embed:{rmorphism A->P}.
Variable variable:P.
Variable coefficient:P->nat->A.
Hypothesis hP:is_commutative_polynomial_ring embed variable coefficient.
Variable J:{rmorphism P->G}.
Hypothesis hJ:is_commutative_polynomial_evaluation embed variable E (analytic_germ fXi) J.
Variable ideal:set G.
Variables W derivative:P.
Variable k:nat.
Hypothesis hDistinguished:is_distinguished_polynomial coefficient (@AnalyticGermValue.map R Y NY hNY 0) W k.
Hypothesis hDerivative:is_formal_polynomial_derivative coefficient W derivative.
Hypothesis hKernel:forall H:P,ideal (J H) <->commutative_divides W H.
Variable delta:A.
Variable index:finType.
Variable T:index->P.
Variable first:index.
Hypothesis hBound:forall j i,(k<=i)%N ->coefficient (T j) i = 0.
Hypothesis hRelation:ideal (J derivative*J (T first)-E delta).

(** Source for [original_polynomial_connected_cylinder_witnesses]:
    the original common analytic domain and
    exact derivative-inverse identity, 3.4.8(10),
    pp. 327, 331. Leading coefficient
    one and all lower centre values
    are retained. The displayed germ relation
    is extended by the existing analytic
    identity theorem; no fibrewise identity,
    differential or nonvanishing conclusion is assumed. *)
Theorem original_polynomial_connected_cylinder_witnesses:
  exists (U:set Y) (bW:'I_k.+1->PY) (bT:index->'I_k->PY)
    (w wD s dX:PX) (t:index->PX) (d:PY),
    U 0 /\@open (real_norm_metric_space hNY) U /\
    @open (real_norm_metric_space hNX) (fun x=>U (projection x)) /\
    @connected (real_norm_metric_space hNX) (fun x=>U (projection x)) /\
    (forall i,ANY U (vy (bW i))) /\(forall j i,ANY U (vy (bT j i))) /\ANY U (vy d) /\
    ANX (fun x=>U (projection x)) (vx w) /\ANX (fun x=>U (projection x)) (vx wD) /\
    ANX (fun x=>U (projection x)) (vx s) /\ANX (fun x=>U (projection x)) (vx dX) /\
    (forall j,ANX (fun x=>U (projection x)) (vx (t j))) /\
    (analytic_germ w:G) = J W /\(analytic_germ wD:G) = J derivative /\
    (forall j,(analytic_germ (t j):G) = J (T j)) /\(analytic_germ d:A) = delta /\
    (analytic_germ dX:G) = E delta /\
    (forall i,(analytic_germ (bW i):A) = coefficient W i) /\
    (forall j i,(analytic_germ (bT j i):A) = coefficient (T j) i) /\
    (forall y,vy (bW ord_max) y = 1) /\
    (forall i:'I_k.+1,(i<k)%N ->vy (bW i) 0 = 0) /\
    (forall x,vx w x = \sum_(i<k.+1) vy (bW i) (projection x)*(xi x)^+(i:nat)) /\
    (forall j x,vx (t j) x = \sum_(i<k) vy (bT j i) (projection x)*(xi x)^+(i:nat)) /\
    (forall x,vx dX x = vy d (projection x)) /\
    (forall a:X,U (projection a) ->exists L:Hom X R^o,
      has_norm_differential NX (fun z:R^o=>`|z|) (fun x=>U (projection x)) (vx w) a L /\
      forall v:X,projection v = 0 ->L v = vx wD a*xi v) /\
    forall x,U (projection x) ->vx wD x*vx (t first) x-vx dX x = vx s x*vx w x.
Proof.
have [bW [hBW [hLeading hLower]]]:=@distinguished_coefficient_actual_representatives R Y NY hNY
  P coefficient W k hDistinguished.
have hSupport:forall i,(k.+1<=i)%N ->coefficient W i = 0.
  exact:hDistinguished.1.1.2.
have [UW [w [wD [hUWOrigin [hUWOpen [hBWAnalytic [hW [hWD [hWAnalytic [hWDAnalytic
  [hWValues [hWDValues hWDifferential]]]]]]]]]]]]:=
  @analytic_prefix_polynomial_actual_witnesses R X Y NX NY hNX hNY projection E xi fXi
    P embed variable coefficient hP J W derivative k.+1 bW hE hProjection hXi hXiValues hJ
    hDerivative hSupport hBW.
have hBTExists (q:(index*'I_k)%type):exists b:PY,(analytic_germ b:A) = coefficient (T q.1) q.2.
  exact:analytic_germ_has_representative.
have [c hC]:=choice hBTExists.
pose bT (j:index) (i:'I_k):=c (j,i).
have hBT j i:(analytic_germ (bT j i):A) = coefficient (T j) i:=hC (j,i).
have [UT [t [hUTOrigin [hUTOpen [hBTAnalytic [hT [hTAnalytic hTValues]]]]]]]:=
  @pointed_polynomial_analytic_family R X Y NX NY hNX hNY projection E xi fXi
    P embed variable coefficient hP J index T k bT hE hProjection hXi hXiValues hJ hBound hBT.
have [S hS]:=@original_polynomial_inverse_identity A P G embed variable E (analytic_germ fXi)
  J ideal W derivative (T first) delta hJ hKernel hRelation.
have [US [s [hUSOrigin [hUSOpen [hSGerm hSAnalytic]]]]]:=
  @pointed_polynomial_analytic_representative R X Y NX NY hNX hNY projection E xi fXi
    P embed variable coefficient hP J S hE hProjection hXi hXiValues hJ.
have [d hD]:=@analytic_germ_has_representative R Y NY hNY 0 delta.
have [UD [hUDOrigin [hUDOpen hDAnalytic]]]:=@finite_analytic_representative_neighbourhood R Y NY hNY 0
  [the finType of 'I_1] (fun _=>d).
have [dX [hDXGerm hDXValues]]:=hE d.
have hDX:(analytic_germ dX:G) = E delta by rewrite -hD hDXGerm.
pose V:=UW `&` (UT `&` (US `&` UD)).
have hVOrigin:V 0 by split;[exact:hUWOrigin|split;[exact:hUTOrigin|split]].
have hVOpen:@open (real_norm_metric_space hNY) V:=openI hUWOpen (openI hUTOpen (openI hUSOpen hUDOpen)).
have [r [hR [hRadius [hCylinderOpen hConnected]]]]:=@norm_prefix_ball_neighbourhood R X Y NX NY hNX hNY
  projection V hProjection hVOpen hVOrigin.
pose U:set Y:=fun y=>NY y<r.
pose C:set X:=fun x=>U (projection x).
have hOrigin:U 0 by rewrite /U (real_seminorm_zero hNY.1).
have hUInterior y (hy:U y):norm_domain_interior NY U y.
  have hy0:NY (y-0)<r by rewrite subr0.
  have [rho [hRho hLocal]]:=@norm_open_ball_domain_interior R Y NY hNY 0 r y hy0.
  exists rho;split;first exact:hRho.
  move=>z hz;have h:=hLocal z hz;by rewrite subr0 in h.
have hUOpen:@open (real_norm_metric_space hNY) U.
  rewrite openE=>y hy;exact:((@norm_domain_interior_neighbourhood R Y NY hNY U y).1 (hUInterior y hy)).
have hCInterior x (hx:C x):norm_domain_interior NX C x.
  exact:(@norm_bounded_linear_preimage_interior R X Y NX NY hNX projection U x hProjection (hUInterior _ hx)).
have hUInV:U `<=` V by move=>y hy;exact:hRadius y hy.
have hUW:C `<=` (fun x=>UW (projection x)) by move=>x hx;exact:(hUInV _ hx).1.
have hUT:C `<=` (fun x=>UT (projection x)) by move=>x hx;exact:(hUInV _ hx).2.1.
have hUS:C `<=` (fun x=>US (projection x)) by move=>x hx;exact:(hUInV _ hx).2.2.1.
have hUD:U `<=` UD by move=>y hy;exact:(hUInV _ hy).2.2.2.
have hWFinal:ANX C (vx w):=norm_analytic_open_restriction hUW hCInterior hWAnalytic.
have hWDFinal:ANX C (vx wD):=norm_analytic_open_restriction hUW hCInterior hWDAnalytic.
have hSFinal:ANX C (vx s):=norm_analytic_open_restriction hUS hCInterior hSAnalytic.
have hTFinal j:ANX C (vx (t j)):=norm_analytic_open_restriction hUT hCInterior (hTAnalytic j).
have hDFinal:ANY U (vy d):=norm_analytic_open_restriction hUD hUInterior (hDAnalytic ord0).
have hProjectionAnalytic:@norm_analytic R X Y NX NY hNX hNY C projection:=
  @norm_bounded_linear_analytic R X Y NX NY hNX hNY C hCInterior projection hProjection.
have hDPull:=@norm_analytic_compose_on R X Y R^o NX NY (fun z:R^o=>`|z|) hNX hNY
  (@scalar_absolute_value_norm R) C U projection (vy d) (fun x hx=>hx) hProjectionAnalytic hDFinal.
have hDXFinal:ANX C (vx dX).
  apply:(norm_analytic_domain_agreement _ hDPull)=>x _;exact:esym (hDXValues x).
have hIdentity:(analytic_germ wD:G)*(analytic_germ (t first):G)-(analytic_germ dX:G) =
    (analytic_germ s:G)*(analytic_germ w:G).
  rewrite hWD (hT first) hDX hSGerm hW -(polynomial_evaluation_constants hJ delta) -rmorphM -rmorphB hS rmorphM.
  by [].
have hCOrigin:C 0 by rewrite /C linear0.
have hActualIdentity:=@analytic_germ_product_identity R X NX hNX 0 C wD (t first) dX s w
  hCylinderOpen hCOrigin hConnected hWDFinal (hTFinal first) hDXFinal hSFinal hWFinal hIdentity.
exists U,bW,bT,w,wD,s,dX,t,d.
split;first exact:hOrigin.
split;first exact:hUOpen.
split;first exact:hCylinderOpen.
split;first exact:hConnected.
split.
- move=>i;apply:(norm_analytic_open_restriction _ hUInterior (hBWAnalytic i))=>y hy;exact:(hUInV y hy).1.
split.
- move=>j i;apply:(norm_analytic_open_restriction _ hUInterior (hBTAnalytic j i))=>y hy;exact:(hUInV y hy).2.1.
split;first exact:hDFinal.
split;first exact:hWFinal.
split;first exact:hWDFinal.
split;first exact:hSFinal.
split;first exact:hDXFinal.
split;first exact:hTFinal.
split;first exact:hW.
split;first exact:hWD.
split;first exact:hT.
split;first exact:hD.
split;first exact:hDX.
split;first exact:hBW.
split;first exact:hBT.
split;first exact:hLeading.
split;first exact:hLower.
split;first exact:hWValues.
split;first exact:hTValues.
split;first exact:hDXValues.
split;last exact:hActualIdentity.
move=>a ha;have [L [hL hDirections]]:=hWDifferential a (hUW a ha).
exists L;split;last exact:hDirections.
exact:(norm_differential_restrict hUW (hCInterior a ha) hL).
Qed.
End CylinderWitnesses.
