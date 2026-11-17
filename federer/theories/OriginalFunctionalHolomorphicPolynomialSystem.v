(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331–332:
    the original polynomial equations define
    a functional holomorphic submanifold outside
    delta=0. Its regularity follows from
    the actual derivative-inverse identity and
    the original transverse coordinate matrix. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicUP HolomorphicLinear HolomorphicRestriction HolomorphicFiniteCalculus HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP Hom RealNormUP NormMetric FiniteCoordinates HolomorphicCoordinateNorm ComplexNormUP NormDifferentialUP NormBoundedLinearTopology NormLinearDomainLaws
  NormAnalyticUP NormAnalyticLinear NormAnalyticOperations NormAnalyticScalarProducts
  OriginalHolomorphicPolynomialEquationDifferentials FieldEquationTransverseIndependence HolomorphicDifferentialRestriction HolomorphicNegation HolomorphicArithmetic HolomorphicProduct
  FunctionalHolomorphicSubmanifoldUP.
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
Local Notation X:=(coordinate_space (ComplexScalars.C R) n).
Local Notation NX:=(@holomorphic_coordinate_norm R n).
Local Notation hNX:=(complex_norm_real (@holomorphic_coordinate_norm_laws R n)).
Local Notation index:=[the finType of 'I_(n-m)].
Variable first:index.
Variable Y:lmodType (ComplexScalars.C R).
Variable NY:Y->R.
Hypothesis hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY.
Variable U:set Y.
Hypothesis hUOpen:@open (real_norm_metric_space hNY) U.
Variable P:Hom X Y.
Hypothesis hP:@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY (complex_hom_real P).
Variable xi:index->Hom X (ComplexScalars.C R)^o.
Hypothesis hXi:forall j,@norm_bounded_linear R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) (complex_hom_real (xi j)).
Variable v:index->X.
Hypothesis hV:forall j,P (v j) = 0.
Hypothesis hDual:forall i j,xi i (v j) = if i==j then 1 else 0.
Variable k:nat.
Variable b:index->'I_k->Y->ComplexScalars.C R.
Variable delta:Y->ComplexScalars.C R.
Hypothesis hB:forall j i,@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY
  (@complex_modulus_real_norm R) U (b j i).
Hypothesis hDelta:@is_holomorphic R Y (ComplexScalars.C R)^o NY (@complex_modulus R) hNY
  (@complex_modulus_real_norm R) U delta.
Local Notation A:=(fun x:X=>U (P x)).
Local Notation AN f:=(@is_holomorphic R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A f).
Variables w wD s:X->ComplexScalars.C R.
Variable t:index->X->ComplexScalars.C R.
Hypothesis hWAnalytic:AN w.
Hypothesis hTAnalytic:forall j,AN (t j).
Hypothesis hW:forall a,A a ->exists L:Hom (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o),
  @has_norm_differential R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) (ComplexScalars.C R)^o) NX (@complex_modulus R) A w a L /\
  forall u,P u = 0 ->L u = wD a*xi first u.
Hypothesis hT:forall j x,t j x = \sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
Hypothesis hIdentity:forall x,A x ->wD x*t first x-delta (P x) = s x*w x.

(** Source for [original_holomorphic_polynomial_functional_submanifold]:
    the original finite zero system outside
    delta=0 is an m-dimensional functional
    holomorphic submanifold, and W' is nonzero
    at every one of its points,
    3.4.12, p. 339, extending 3.4.8(10), pp. 327, 331–332.
    The actual differentials and their independence
    are proved; they are not new premises. *)
Theorem original_holomorphic_polynomial_functional_submanifold:
  exists (f:index->X->ComplexScalars.C R) (Z:set X),
    (forall j x,f j x = if j==first then w x else delta (P x)*xi j x-t j x) /\
    (forall x,Z x <->A x /\(forall j,f j x=0) /\delta (P x)<>0) /\
    (forall j,AN (f j)) /\AN (fun x=>delta (P x)) /\
    is_functional_holomorphic_submanifold m A Z /\forall x,Z x ->wD x!=0.
Proof.
pose f:=fun (j:index) (x:X)=>if j==first then w x else delta (P x)*xi j x-t j x.
pose Z:set X:=fun x=>A x /\(forall j,f j x=0) /\delta (P x)<>0.
have hU y (hy:U y):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) Y) NY U y.
  have hNeighbourhood:=hUOpen;rewrite openE in hNeighbourhood.
  exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) Y) NY hNY U y).2 (hNeighbourhood y hy)).
have hA x (hx:A x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX A x.
  exact:(@norm_bounded_linear_preimage_interior R (restricted_space (ComplexScalars.embed R) X) (restricted_space (ComplexScalars.embed R) Y) NX NY hNX (complex_hom_real P) U x hP (hU _ hx)).
have hAOpen:@open (real_norm_metric_space hNX) A.
  rewrite openE=>x hx;exact:((@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX A x).1 (hA x hx)).
have hProjectionAnalytic:@is_holomorphic R X Y NX NY hNX hNY A P:=
  @holomorphic_bounded_linear R X Y NX NY hNX hNY A P hA hP.
have hDeltaPull:AN (fun x=>delta (P x)):=@holomorphic_compose_on R X Y (ComplexScalars.C R)^o NX NY
  (@complex_modulus R) hNX hNY (@complex_modulus_real_norm R) A U P delta
  (fun x hx=>hx) hProjectionAnalytic hDelta.
have hFAnalytic j:AN (f j).
  have hXiAnalytic:=@holomorphic_bounded_linear R X (ComplexScalars.C R)^o NX (@complex_modulus R) hNX
    (@complex_modulus_real_norm R) A (xi j) hA (hXi j).
  case hCase:(j==first).
  - apply:(holomorphic_domain_agreement _ hWAnalytic)=>x _;by rewrite /f hCase.
  - have hOther:=holomorphic_add (holomorphic_product hDeltaPull hXiAnalytic) (holomorphic_negate (hTAnalytic j)).
    apply:(holomorphic_domain_agreement _ hOther)=>x _;by rewrite /f hCase.
have hRegular x (hx:Z x):wD x!=0.
  have hZero:f first x=0:=hx.2.1 first.
  rewrite /f eqxx in hZero.
  apply/eqP=>hWDZero;apply:hx.2.2.
  have h:=@hIdentity x hx.1.
  rewrite hWDZero hZero mul0r mulr0 sub0r in h.
  have hNegative:=congr1 (fun z:ComplexScalars.C R=>-z) h.
  by rewrite opprK oppr0 in hNegative.
have hFunctional:is_functional_holomorphic_submanifold m A Z.
  split;first exact:hMN.
  split;first exact:hAOpen.
  exists f,(fun x=>delta (P x));split;first exact:hFAnalytic.
  split;first exact:hDeltaPull.
  split;first by move=>x.
  move=>x hx.
  have [D [hD hDirections]]:=@original_holomorphic_polynomial_equation_differentials R X Y NX NY hNX hNY
    U hU P hP index first xi hXi k b delta hB hDelta w wD hW t hT f (fun j x=>erefl _) x hx.1.
  have hLiftExists j:exists E:Hom X (ComplexScalars.C R)^o,complex_hom_real E=D j.
    exact:(@holomorphic_actual_differential_complex_restriction R X (ComplexScalars.C R)^o
      NX (@complex_modulus R) hNX (@complex_modulus_real_norm R) A (f j) x (D j)
      (hFAnalytic j) (hD j)).
  have [E hE]:=choice hLiftExists.
  exists E;split.
  - move=>j;by rewrite hE.
  - apply:(@field_equation_transverse_independence (ComplexScalars.C R) X Y index first P xi v E
      (delta (P x)) (wD x) (fun j=>\sum_(i<k) (i:nat)%:R*b j i (P x)*(xi first x)^+(i:nat).-1)
      hV hDual _ _ (hRegular x hx)).
    + move=>j u hZero.
      change (complex_hom_real (E j) u=if j==first then wD x*xi first u else
        delta (P x)*xi j u-(\sum_(i<k) (i:nat)%:R*b j i (P x)*(xi first x)^+(i:nat).-1)*xi first u).
      by rewrite hE hDirections.
    + by apply/eqP;exact:hx.2.2.
exists f,Z;split;first by [].
split;first by move=>x.
split;first exact:hFAnalytic.
split;first exact:hDeltaPull.
by split.
Qed.
End FunctionalSystem.
