(** Federer (1969), 3.4.8(10), pp. 331–332:
    the original prefix and analytic equations
    give a joint analytic map with
    an actual local analytic inverse. Use
    finite coordinate synthesis and the proved
    analytic inverse theorem of 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialFiniteCalculus NormDifferentialLocal NormOpenDomainLaws
  NormAnalyticUP NormAnalyticLinear NormAnalyticOperations NormDiffeomorphismUP
  GrassmannAbbreviations FiniteCoordinates EuclideanCoordinateTopology EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormFiniteLinearBound EuclideanBlockLinearMaps
  NormAnalyticFiniteSynthesis NormDifferentialFiniteSynthesis FiniteAnalyticInversePoint.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section JointInverse.
Variable R:realType.
Variables m l:nat.
Local Notation X:=(R_n R (m+l)).
Local Notation Y:=(R_n R m).
Local Notation Z:=(R_n R l).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R (m+l))).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m)).
Local Notation NZ:=(inner_norm (@euclidean_inner_productP R l)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R (m+l))).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R l)).
Variable A:set X.
Hypothesis hA:forall x,A x ->norm_domain_interior NX A x.
Variable P:Hom X Y.
Hypothesis hP:norm_bounded_linear NX NY P.
Variable f:'I_l->X->R.
Hypothesis hF:forall j,@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
  (@scalar_absolute_value_norm R) A (f j).
Variable a:X.
Hypothesis ha:A a.
Variable D:'I_l->Hom X R^o.
Hypothesis hD:forall j,has_norm_differential NX (fun t:R^o=>`|t|) A (f j) a (D j).
Hypothesis hSeparate:forall u,P u = 0 ->(forall j,D j u = 0) ->u=0.

(** Source for [finite_analytic_joint_inverse]:
    an ambient analytic change of coordinates
    retains p_m as its first block
    and the original equations as its
    remaining coordinates, 3.4.8(10), pp. 331–332.
    Actual injectivity is proved from the
    original joint differential kernel calculation. *)
Theorem finite_analytic_joint_inverse:
  exists (H G:X->X) r,
    (forall x,@euclidean_first_block_map R m l (H x) = P x) /\
    (forall x j,@euclidean_last_block_map R m l (H x) j = f j x) /\
    @norm_analytic R X X NX NX hNX hNX A H /\0<r /\
    (forall x,NX (x-a)<r ->A x) /\
    is_norm_diffeomorphism hNX hNX [set x|NX (x-a)<r]
      (H @` [set x|NX (x-a)<r]) H G 1%N /\
    @norm_analytic R X X NX NX hNX hNX (H @` [set x|NX (x-a)<r]) G.
Proof.
pose F:=fun x:X=>[ffun j:'I_l=>f j x].
have hFValues x:F x = \sum_j f j x*:(@coordinate_basis R l j).
  rewrite -{1}(@euclidean_coordinate_expansion R l (F x)).
  apply:eq_bigr=>i _;by rewrite /F ffunE.
have hFAnalytic:@norm_analytic R X Z NX NZ hNX hNZ A F.
  have hSum:=@norm_analytic_finite_synthesis R X Z NX NZ hNX hNZ A [the finType of 'I_l]
    (@coordinate_basis R l) f hA hF.
  apply:(norm_analytic_domain_agreement _ hSum)=>x _;exact:esym (hFValues x).
have [DF [hDF hDFValues]]:=@norm_differential_finite_synthesis R X Z NX NZ hNX hNZ A a
  [the finType of 'I_l] (@coordinate_basis R l) f D (@hA a ha) hD.
have hFDerivative:has_norm_differential NX NZ A F a DF.
  apply:(norm_differential_domain_agreement hNX _ hDF)=>x _;exact:esym (hFValues x).
have hDFCoordinates u j:DF u j = D j u.
  have hVector:DF u = [ffun j:'I_l=>D j u].
    rewrite hDFValues -(@euclidean_coordinate_expansion R l [ffun j:'I_l=>D j u]).
    apply:eq_bigr=>i _;by rewrite ffunE.
  by rewrite hVector ffunE.
pose I:=@euclidean_first_injection_map R m l.
pose J:=@euclidean_last_injection_map R m l.
have hI:=@norm_finite_linear_bounded R Y X NY NX hNY hNX m
  (@coordinate_basis R m) (@coordinate_basisP R m) I.
have hJ:=@norm_finite_linear_bounded R Z X NZ NX hNZ hNX l
  (@coordinate_basis R l) (@coordinate_basisP R l) J.
pose H:=fun x:X=>I (P x)+J (F x).
pose L:=hom_comp I P+hom_comp J DF.
have hFirstAnalytic:=@norm_bounded_linear_analytic R X X NX NX hNX hNX A hA (hom_comp I P)
  (norm_bounded_linear_compose hP hI).
have hJAnalytic:=@norm_bounded_linear_analytic R Z X NZ NX hNZ hNX (fun _=>True)
  (fun z _=>norm_full_domain_interior NZ z) J hJ.
have hLastAnalytic:=@norm_analytic_compose_on R X Z X NX NZ NX hNX hNZ hNX A (fun _=>True)
  F J (fun x _=>Logic.I) hFAnalytic hJAnalytic.
have hH:@norm_analytic R X X NX NX hNX hNX A H:=norm_analytic_add hFirstAnalytic hLastAnalytic.
have hFirstDerivative:=@norm_differential_linear R X X NX NX hNX hNX A a (hom_comp I P)
  (@hA a ha) (norm_bounded_linear_compose hP hI).
have hLastDerivative:=@norm_differential_postcompose R X Z X NX NZ NX hNX A F a DF J hFDerivative hJ.
have hHDerivative:has_norm_differential NX NX A H a L:=norm_differential_add hNX hFirstDerivative hLastDerivative.
have hHFirst x:@euclidean_first_block_map R m l (H x) = P x.
  rewrite /H linearD /= /I /J euclidean_first_block_injectionK euclidean_first_block_last_injection.
  exact:addr0.
have hHLast x:@euclidean_last_block_map R m l (H x) = F x.
  rewrite /H linearD /= /I /J euclidean_last_block_first_injection euclidean_last_block_injectionK.
  exact:add0r.
have hLFirst u:@euclidean_first_block_map R m l (L u) = P u.
  rewrite /L hom_addE !hom_compE linearD /= /I /J
    euclidean_first_block_injectionK euclidean_first_block_last_injection;exact:addr0.
have hLLast u:@euclidean_last_block_map R m l (L u) = DF u.
  rewrite /L hom_addE !hom_compE linearD /= /I /J
    euclidean_last_block_first_injection euclidean_last_block_injectionK;exact:add0r.
have hKernel u (hu:L u = 0):u=0.
  have hPrefix:P u = 0.
    rewrite -(hLFirst u) hu;exact:linear0.
  apply:(@hSeparate u hPrefix)=>j.
  rewrite -(hDFCoordinates u j) -(hLLast u) hu linear0;by rewrite ffunE.
have hInjective:injective L.
  move=>u v hEqual.
  have hZero:L (u-v) = 0 by rewrite (linB (hom_linear L)) hEqual subrr.
  apply/eqP;by rewrite -subr_eq0 (hKernel (u-v) hZero) eqxx.
have [r [hR [hInside [G [hInverse hGAnalytic]]]]]:=@finite_analytic_inverse_from_point_differential
  R X (@euclidean_inner_product R (m+l)) (@euclidean_inner_productP R (m+l)) hNX
  (m+l)%N (@coordinate_basis R (m+l)) (@coordinate_basisP R (m+l)) A H a L
  hH ha hHDerivative hInjective.
exists H,G,r;split;first exact:hHFirst.
split;first by move=>x j;rewrite hHLast /F ffunE.
split;first exact:hH.
split;first exact:hR.
split;first exact:hInside.
by split.
Qed.
End JointInverse.
