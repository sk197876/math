(** Federer (1969), 3.4.2, pp. 310–316: actual
    endpoint, flat-cover, and critical-image regressions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerProductUP
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP
  NormDifferentialLinear NormOpenDomainLaws NormRegularity NormRegularityOperations
  RelativeClassUP GrassmannHomogeneousSpace EuclideanProjectionSpace CoordinateProjection
  CriticalManifoldFamilyUP CriticalProjectionSectionFamily CriticalOscillation
  CriticalManifoldCompactCover CriticalFlatCoverUP CriticalFlatDecomposition
  CriticalFlatPiecesUP CriticalFlatImage CriticalTangentImage CriticalRelativeDifferentialLaws
  CriticalValueEstimates RealPower RealPowerSuccessor ExtendedSupremumUP RadialRatioZero
  PartialFunctionUP PositiveRightOrderLimit CriticalDiscreteOscillation RealHausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_example_whole_manifold]: the whole
    Euclidean examples of Omega in 3.4.2(3), p. 310.
    Actual identity projections and the identity class-k section
    prove all hypotheses, including dimension zero. This witness
    is local to the regressions. *)
Local Lemma critical_example_whole_manifold (R:realType) n k:
  (0<k)%N ->exists Z:G (R_n R n) n,
    (forall x,grassmann_val Z x) /\critical_manifold_family Z n k setT.
Proof.
move=>hk.
pose V:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose I:=@linear_id R V.
have hInjective:injective I by move=>x y.
pose Z:=@linear_image_grassmann R V V n (@coordinate_basis R n)
  (@coordinate_basisP R n) I hInjective.
have hZ x:grassmann_val Z x by exists x.
have hStar:O_star I.
  exists I;split;by move=>x y.
have [p hP]:=euclidean_projection_linear_complete hStar.
have hInterior x (hx:setT x):norm_domain_interior N setT x:=norm_full_domain_interior N x.
have hBound:norm_bounded_linear N N (hom_of_linear I).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite hom_of_linearE mul1r.
have hClass:=@norm_class_linear R V V N N hN hN setT (hom_of_linear I) k hInterior hBound.
have hImage:(hom_of_linear I @` setT)=setT.
  apply/seteqP;split;first by move=>x _.
  by move=>x _;exists x.
have hFamily:=@critical_projection_section_family R n n Z n k p setT (hom_of_linear I)
  (leq_subr n n) hk (fun x _=>hZ x) (fun x y _ _ t _ _=>Logic.I) hClass
  (fun x _=>hP x).
exists Z;split;first exact:hZ.
by rewrite hImage in hFamily.
Qed.

(** Source for [critical_zero_space_full_flat_cover]: the
    nonempty R^0 endpoint of 3.4.2(6)–(7), pp. 311–312.
    The whole source has the actual class-two flat decomposition,
    and a nonzero constant has eta zero at every real cutoff. *)
Example critical_zero_space_full_flat_cover (R:realType):
  exists (Z:G (R_n R 0) 0) (T G:nat->set (R_n R 0)),
    is_critical_flat_cover (@scalar_absolute_value_norm R) Z 0 setT setT 2 T G /\
    forall delta:R,@critical_eta R 0 R^o (fun x:R=>`|x|) (grassmann_val Z)
      setT setT (fun _:R_n R 0=>(1:R)) 2 delta=0%E.
Proof.
have [Z [hZ hOmega]]:=@critical_example_whole_manifold R 0 2 (erefl true).
have hClosed:@is_relatively_closed_source (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R 0))) setT setT.
  exists setT;split;first exact:closedT.
  by rewrite setIT.
have [T [G hCover]]:=@critical_flat_cover_exists R 0 0 Z R^o (fun x:R=>`|x|)
  (@scalar_absolute_value_norm R) 0 2 setT setT hOmega hClosed.
exists Z,T,G;split;first exact:hCover.
move=>delta;exact:(@critical_eta_constant R 0 R^o (fun x:R=>`|x|)
  (@scalar_absolute_value_norm R) (grassmann_val Z) setT setT 1 2 delta).
Qed.

(** Source for [critical_line_constant_tangent_image]: a
    higher-class instance of the complete 3.4.2(9), p. 311.
    The nonzero constant on the whole line has every point
    tangent-critical. The theorem gives its actual nonempty image
    zero H^(1/2) measure. No boundedness of the original critical
    set is supplied. *)
Example critical_line_constant_tangent_image (R:realType)
    (hp:0<=(0:R)+1/2):
  @real_hausdorff_measure R (real_norm_metric_space (@scalar_absolute_value_norm R))
    (0+1/2) hp [set (1:R)]=0%E.
Proof.
have [Z [hZ hOmega]]:=@critical_example_whole_manifold R 1 2 (erefl true).
pose X:=R_n R 1.
pose N:=inner_norm (@euclidean_inner_productP R 1).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 1).
pose hR:=@scalar_absolute_value_norm R.
pose f:=fun _:X=>(1:R).
have hInterior x (hx:setT x):norm_domain_interior N setT x:=norm_full_domain_interior N x.
have hClass:=@norm_class_constant R X R^o N (fun x:R=>`|x|) hN hR setT 1 2 hInterior.
have hRelative:norm_class_relative hN hR setT setT f 2.
  apply:(@norm_relative_extension_class R X R^o N (fun x:R=>`|x|) hN hR
    setT setT f 2 setT f).
  split;first exact:hClass.
  split;first by move=>x hx.
  by move=>x hx;split.
have hCritical:critical_tangent_zero_locus hR (grassmann_val Z) setT f=setT.
  apply/seteqP;split;first by move=>x _.
  move=>x hx;split;first exact:Logic.I.
  have hDiff:=@norm_differential_constant R X R^o N (fun x:R=>`|x|) hN hR setT x 1
    (hInterior x Logic.I).
  have [L [hOuter hValues]]:=@critical_relative_differential_from_extension R X R^o N
    (fun x:R=>`|x|) hN hR setT setT f f x 0 Logic.I (fun y _ _=>erefl (f y)) hDiff.
  exists L;split;first exact:hOuter.
  move=>z y hz hy;have hValue:=((hValues z y).1 hy).2.
  by rewrite hom_zeroE in hValue;exact:esym hValue.
have hImage:f @` critical_tangent_zero_locus hR (grassmann_val Z) setT f=[set 1].
  rewrite hCritical;apply/seteqP;split.
  - by move=>y [x _ <-].
  - move=>y ->;exists 0;by [].
have hResult:=@critical_tangent_critical_image_nullity R 1 1 Z 1 2 setT R^o
  (fun x:R=>`|x|) hR f hp hOmega (erefl true) hRelative.
by rewrite hImage in hResult.
Qed.

(** Source for [critical_identity_half_order_image]: the real
    order 0<lambda<1 allowed in 3.4.2(8), p. 311.
    The identity on the line has vanishing half-order eta
    at a singleton centre, and the complete theorem proves
    the actual H^2 nullity of its nonempty image. *)
Example critical_identity_half_order_image (R:realType) (hp:0<=(0:R)+1/(1/2)):
  exists Z:G (R_n R 1) 1,
    positive_right_extended_order_limit
      (fun delta=>critical_eta (inner_norm (@euclidean_inner_productP R 1))
        (grassmann_val Z) setT [set (0:R_n R 1)] (fun x=>x) (1/2) delta) 0%E /\
    @real_hausdorff_measure R (real_norm_metric_space
      (inner_norm_real_norm (@euclidean_inner_productP R 1)))
      (0+1/(1/2)) hp [set (0:R_n R 1)]=0%E.
Proof.
have [Z [hZ hOmega]]:=@critical_example_whole_manifold R 1 1 (erefl true).
pose X:=R_n R 1.
pose N:=inner_norm (@euclidean_inner_productP R 1).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 1).
have hHalf:0<(1/2:R) by rewrite divr_gt0 // ltr0n.
have hHalfSum:(1/2+1/2:R)= 1 by field.
have hHalfProduct:(2*(1/2):R)= 1 by field.
have hEta:positive_right_extended_order_limit
    (fun delta=>critical_eta N (grassmann_val Z) setT [set (0%R:X)] (fun x=>x) (1/2) delta) 0%E.
  apply:nonnegative_positive_right_limit_zero.
  - move=>delta hDelta;exact:critical_eta_nonnegative.
  - move=>eps hEps.
    pose e:=eps/2.
    have he:0<e by rewrite /e divr_gt0 // ltr0n.
    pose d:=real_power e 2.
    have hd:0<d:=real_power_strictly_positive _ he.
    exists d;split;first exact:hd.
    move=>delta hDelta hSmall.
    have hBound:(critical_eta N (grassmann_val Z) setT [set (0%R:X)]
        (fun x=>x) (1/2) delta<=e%:E)%E.
      apply:(extended_supremum_least (critical_eta_laws N (grassmann_val Z)
        setT [set (0%R:X)] (fun x=>x) (1/2) delta)).
      move=>q [->|[x [c [_ [hc [_ [hDist ->]]]]]]].
      + rewrite lee_fin;exact:ltW he.
      + rewrite lee_fin.
        have /andP[hPositive hRadius]:=hDist.
        have hPowerPositive:0<real_power (N (x-c)) (1/2):=real_power_strictly_positive _ hPositive.
        have hSquare:real_power (N (x-c)) (1/2)*real_power (N (x-c)) (1/2)=N (x-c).
          have hAdd:=@real_power_add_exponents_positive R (N (x-c)) (1/2) (1/2) hPositive.
          have hOne:=@real_power_one_exponent R (N (x-c)) (ltW hPositive).
          rewrite hHalfSum hOne in hAdd;exact:esym hAdd.
        have hRatio:N (x-c)/real_power (N (x-c)) (1/2)=real_power (N (x-c)) (1/2).
          by rewrite -{1}hSquare mulfK ?gt_eqF.
        rewrite hRatio.
        have hPower:=real_power_monotone (ltW hPositive) (le_trans hRadius (ltW hSmall)) hHalf.
        have hRoot:real_power d (1/2)=e.
          have hTwo:0<(2:R) by rewrite ltr0n.
          have hIter:=@real_power_positive_iterate R e 2 (1/2) (ltW he) hTwo hHalf.
          have hOne:=@real_power_one_exponent R e (ltW he).
          by rewrite hHalfProduct hOne in hIter.
        by rewrite hRoot in hPower.
    apply:(le_lt_trans hBound);rewrite lte_fin /e;lra.
have hInterior x (hx:setT x):norm_domain_interior N setT x:=norm_full_domain_interior N x.
have hBound:norm_bounded_linear N N (hom_of_linear (@linear_id R X)).
  exists 1;split;first exact:ler01.
  by move=>x;rewrite hom_of_linearE mul1r.
have hClass:=@norm_class_linear R X X N N hN hN setT (hom_of_linear (@linear_id R X))
  1 hInterior hBound.
have hRelative:norm_class_relative hN hN setT setT (fun x=>x) 1.
  apply:(@norm_relative_extension_class R X X N N hN hN setT setT (fun x=>x)
    1 setT (hom_of_linear (@linear_id R X))).
  split;first exact:hClass.
  split;first by move=>x hx.
  by move=>x hx;split.
have hNull:=@critical_flat_image_nullity R 1 1 Z 1 setT [set (0%R:X)] X N hN
  (fun x=>x) (1/2) hp hOmega (erefl true) (fun x hx=>Logic.I)
  (@compact_set1 (real_norm_metric_space hN) 0) hRelative hHalf hEta.
exists Z;split;first exact:hEta.
by rewrite image_id in hNull.
Qed.
