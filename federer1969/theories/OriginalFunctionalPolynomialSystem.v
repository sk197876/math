(** Federer (1969), 3.4.8(10), pp. 327, 331–332:
    the original polynomial equations define
    a functional analytic submanifold outside
    delta=0. Its regularity follows from
    the actual derivative-inverse identity and
    the original transverse coordinate matrix. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormBoundedLinearTopology NormLinearDomainLaws
  NormAnalyticUP NormAnalyticLinear NormAnalyticOperations NormAnalyticScalarProducts
  OriginalPolynomialEquationDifferentials OriginalEquationTransverseIndependence
  FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FunctionalSystem.
Variable R:realType.
Variables n m:nat.
Hypothesis hMN:(m<=n)%N.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation index:=[the finType of 'I_(n-m)].
Variable first:index.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable U:set Y.
Hypothesis hUOpen:@open (real_norm_metric_space hNY) U.
Variable P:Hom X Y.
Hypothesis hP:norm_bounded_linear NX NY P.
Variable xi:index->Hom X R^o.
Hypothesis hXi:forall j,norm_bounded_linear NX (fun t:R^o=>`|t|) (xi j).
Variable v:index->X.
Hypothesis hV:forall j,P (v j) = 0.
Hypothesis hDual:forall i j,xi i (v j) = if i==j then 1 else 0.
Variable k:nat.
Variable b:index->'I_k->Y->R.
Variable delta:Y->R.
Hypothesis hB:forall j i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U (b j i).
Hypothesis hDelta:@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U delta.
Local Notation A:=(fun x:X=>U (P x)).
Local Notation AN f:=(@norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) A f).
Variables w wD s:X->R.
Variable t:index->X->R.
Hypothesis hWAnalytic:AN w.
Hypothesis hTAnalytic:forall j,AN (t j).
Hypothesis hW:forall a,A a ->exists L:Hom X R^o,
  has_norm_differential NX (fun z:R^o=>`|z|) A w a L /\
  forall u,P u = 0 ->L u = wD a*xi first u.
Hypothesis hT:forall j x,t j x = \sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
Hypothesis hIdentity:forall x,A x ->wD x*t first x-delta (P x) = s x*w x.

(** Source for [original_polynomial_functional_submanifold]:
    the original finite zero system outside
    delta=0 is an m-dimensional functional
    analytic submanifold, and W' is nonzero
    at every one of its points,
    3.4.8(10), pp. 327, 331–332.
    The actual differentials and their independence
    are proved; they are not new premises. *)
Theorem original_polynomial_functional_submanifold:
  exists (f:index->X->R) (Z:set X),
    (forall j x,f j x = if j==first then w x else delta (P x)*xi j x-t j x) /\
    (forall x,Z x <->A x /\(forall j,f j x=0) /\delta (P x)<>0) /\
    (forall j,AN (f j)) /\AN (fun x=>delta (P x)) /\
    is_functional_analytic_submanifold m A Z /\forall x,Z x ->wD x!=0.
Proof.
pose f:=fun (j:index) (x:X)=>if j==first then w x else delta (P x)*xi j x-t j x.
pose Z:set X:=fun x=>A x /\(forall j,f j x=0) /\delta (P x)<>0.
have hU y (hy:U y):norm_domain_interior NY U y.
  have hNeighbourhood:=hUOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY U y).2 (hNeighbourhood y hy)).
have hA x (hx:A x):norm_domain_interior NX A x.
  exact:(@norm_bounded_linear_preimage_interior R X Y NX NY hNX P U x hP (hU _ hx)).
have hAOpen:@open (real_norm_metric_space hNX) A.
  rewrite openE=>x hx;exact:((@norm_domain_interior_neighbourhood R X NX hNX A x).1 (hA x hx)).
have hProjectionAnalytic:@norm_analytic R X Y NX NY hNX hNY A P:=
  @norm_bounded_linear_analytic R X Y NX NY hNX hNY A hA P hP.
have hDeltaPull:AN (fun x=>delta (P x)):=@norm_analytic_compose_on R X Y R^o NX NY
  (fun z:R^o=>`|z|) hNX hNY (@scalar_absolute_value_norm R) A U P delta
  (fun x hx=>hx) hProjectionAnalytic hDelta.
have hFAnalytic j:AN (f j).
  have hXiAnalytic:=@norm_bounded_linear_analytic R X R^o NX (fun z:R^o=>`|z|) hNX
    (@scalar_absolute_value_norm R) A hA (xi j) (hXi j).
  case hCase:(j==first).
  - apply:(norm_analytic_domain_agreement _ hWAnalytic)=>x _;by rewrite /f hCase.
  - have hOther:=norm_analytic_subtract (norm_analytic_scalar_product hDeltaPull hXiAnalytic) (hTAnalytic j).
    apply:(norm_analytic_domain_agreement _ hOther)=>x _;by rewrite /f hCase.
have hRegular x (hx:Z x):wD x!=0.
  have hZero:f first x=0:=hx.2.1 first.
  rewrite /f eqxx in hZero.
  apply/eqP=>hWDZero;apply:hx.2.2.
  have h:=@hIdentity x hx.1.
  rewrite hWDZero hZero mul0r mulr0 sub0r in h.
  have hNegative:=congr1 (fun z:R=>-z) h.
  by rewrite opprK oppr0 in hNegative.
have hFunctional:is_functional_analytic_submanifold m A Z.
  split;first exact:hMN.
  split;first exact:hAOpen.
  exists f,(fun x=>delta (P x));split;first exact:hFAnalytic.
  split;first exact:hDeltaPull.
  split;first by move=>x.
  move=>x hx.
  have [D [hD hDirections]]:=@original_polynomial_equation_differentials R X Y NX NY hNX hNY
    U hU P hP index first xi hXi k b delta hB hDelta w wD hW t hT f (fun j x=>erefl _) x hx.1.
  exists D;split;first exact:hD.
  apply:(@original_equation_transverse_independence R X Y index first P xi v D
    (delta (P x)) (wD x) (fun j=>\sum_(i<k) (i:nat)%:R*b j i (P x)*(xi first x)^+(i:nat).-1)
    hV hDual hDirections _ (hRegular x hx)).
  by apply/eqP;exact:hx.2.2.
exists f,Z;split;first by [].
split;first by move=>x.
split;first exact:hFAnalytic.
split;first exact:hDeltaPull.
by split.
Qed.
End FunctionalSystem.
