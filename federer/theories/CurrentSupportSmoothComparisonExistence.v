(** Federer (1969), 4.1.15, p. 372: construct
    the two actual smooth families used in the original
    support-coincidence proof. Ambient plateau extensions serve
    only this existence proof. A compact target margin
    derives one original V-valued source neighbourhood; the
    intermediate G_r remains ambient-valued. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology NormRegularity NormClassOneUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet SmoothClassOpenRestriction
  SmoothLipschitzDifferentialRestriction CurrentLipschitzCompactImage
  CurrentSmoothApproximationUP CurrentSupportSmoothComparisonUP
  CurrentLipschitzGlobalPlateau NormCompactUniformImageNeighbourhood
  RadialSmoothingFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSupportSmoothComparisonExistence.
Variable R:realType.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation MX:=(real_norm_metric_space hNX).
Local Notation MY:=(real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX U.
Variables f g:X->Y.
Hypothesis hFImage:forall x,U x->V (f x).
Hypothesis hGImage:forall x,U x->V (g x).
Hypothesis hFLocal:@is_locally_metric_lipschitz R MX MY U f.
Hypothesis hGLocal:@is_locally_metric_lipschitz R MX MY U g.
Variable A:set X.
Hypothesis hAK:A `<=` smooth_compact_carrier K.
Hypothesis hAgree:forall x,A x->f x=g x.

(** Source for [current_support_smooth_comparison_exists]:
    the original smoothing comparison families in Federer
    4.1.15, p. 372, exist near the whole K.
    Their pairwise equality is needed only near A,
    and that neighbourhood may shrink with the index.
    No global V-valued extension, convexity, finite mass
    or flat-current assumption enters this analytic existence law. *)
Theorem current_support_smooth_comparison_exists:
  exists Z:set X,exists a:nat->X->Y,exists b:nat->X->Y,
    @is_current_support_smooth_comparison R n nu U V K f g A Z a b.
Proof.
have[F [WF [Lf [hWF [hKWF [hWFU [hFA [hLf [hFBound hFContinuous]]]]]]]]]:=
  @current_lipschitz_global_plateau_exists R n nu U hU K f hFLocal.
have[G [WG [Lg [hWG [hKWG [hWGU [hGA [hLg [hGBound hGContinuous]]]]]]]]]:=
  @current_lipschitz_global_plateau_exists R n nu U hU K g hGLocal.
have[a [b [hAClass [hBClass [hALip [hBLip [hAUniform [hBUniform hNearby]]]]]]]]:=
  @radial_smoothing_families_exists R n nu F G Lf Lg
    (ltW hLf) (ltW hLg) hFBound hGBound.
have hFImageK:forall x,smooth_compact_carrier K x->V (F x).
  move=>x hx;rewrite (@hFA x (@hKWF x hx)).
  exact:(@hFImage x (smooth_compact_in_domain K x hx)).
have hGImageK:forall x,smooth_compact_carrier K x->V (G x).
  move=>x hx;rewrite (@hGA x (@hKWG x hx)).
  exact:(@hGImage x (smooth_compact_in_domain K x hx)).
have[ZF [hZF [hKZF [hZFU [hZFEmpty [NF hNF]]]]]]:=
  @norm_compact_uniform_image_neighbourhood R X Y NX NY hNX hNY
    U V hU hV K F a hFContinuous hFImageK hAUniform.
have[ZG [hZG [hKZG [hZGU [hZGEmpty [NG hNG]]]]]]:=
  @norm_compact_uniform_image_neighbourhood R X Y NX NY hNX hNY
    U V hU hV K G b hGContinuous hGImageK hBUniform.
have hZFOpen:@open MX ZF.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX ZF x).1
    (@hZF x hx).
have hZGOpen:@open MX ZG.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX ZG x).1
    (@hZG x hx).
pose Z:=ZF `&` ZG.
have hZOpen:@open MX Z:=openI hZFOpen hZGOpen.
have hZ:forall x,Z x->norm_domain_interior NX Z x.
  move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX Z x).2
    (open_nbhs_nbhs (conj hZOpen hx)).
have hKZ:smooth_compact_carrier K `<=` Z.
  move=>x hx;exact:conj (@hKZF x hx) (@hKZG x hx).
have hZU:Z `<=` U by move=>x hx;exact:(@hZFU x hx.1).
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose N:=maxn NF NG.
pose aa i:=a (N+i)%N.
pose bb i:=b (N+i)%N.
have hAa:@is_current_smooth_approximation R n nu Z V KZ f aa.
  constructor.
  - move=>i x hx;apply:(@hNF (N+i)%N _ x hx.1).
    exact:(leq_trans (leq_maxl NF NG) (leq_addr i N)).
  - move=>i;exact:(@smooth_class_open_restriction R X Y NX NY hNX hNY
      setT Z (a (N+i)%N) (fun _ _=>Logic.I) hZ (hAClass (N+i)%N)).
  - exists Lf;split;first exact:ltW hLf.
    move=>i x hx.
    exact:(@smooth_global_lipschitz_differential_restriction R n nu (a (N+i)%N)
      Lf Z (ltW hLf) (hAClass (N+i)%N) (@hALip (N+i)%N) hZ x (@hKZ x hx)).
  - move=>delta hDelta;have[M hM]:=@hAUniform delta hDelta.
    exists M=>i hi x hx.
    have hValue:=@hM (N+i)%N (leq_trans hi (leq_addl N i)) x.
    by rewrite (@hFA x (@hKWF x hx)) in hValue.
have hBb:@is_current_smooth_approximation R n nu Z V KZ g bb.
  constructor.
  - move=>i x hx;apply:(@hNG (N+i)%N _ x hx.2).
    exact:(leq_trans (leq_maxr NF NG) (leq_addr i N)).
  - move=>i;exact:(@smooth_class_open_restriction R X Y NX NY hNX hNY
      setT Z (b (N+i)%N) (fun _ _=>Logic.I) hZ (hBClass (N+i)%N)).
  - exists (2*Lf+Lg);split;first exact:addr_ge0 (mulr_ge0 (ler0n R 2) (ltW hLf)) (ltW hLg).
    move=>i x hx.
    exact:(@smooth_global_lipschitz_differential_restriction R n nu (b (N+i)%N)
      (2*Lf+Lg) Z (addr_ge0 (mulr_ge0 (ler0n R 2) (ltW hLf)) (ltW hLg))
      (hBClass (N+i)%N) (@hBLip (N+i)%N) hZ x (@hKZ x hx)).
  - move=>delta hDelta;have[M hM]:=@hBUniform delta hDelta.
    exists M=>i hi x hx.
    have hValue:=@hM (N+i)%N (leq_trans hi (leq_addl N i)) x.
    by rewrite (@hGA x (@hKWG x hx)) in hValue.
have hAmbientAgree:forall x,A x->F x=G x.
  move=>x hx.
  exact:(eq_trans (@hFA x (@hKWF x (@hAK x hx)))
    (eq_trans (@hAgree x hx) (esym (@hGA x (@hKWG x (@hAK x hx)))))).
exists Z,aa,bb.
refine (@Build_is_current_support_smooth_comparison R n nu U V K f g A Z aa bb
  hZ hZU hKZ hAa hBb _).
move=>i;have[W [hW [hAW hEqual]]]:=@hNearby A hAmbientAgree (N+i)%N.
  exists (W `&` Z);split.
  + move=>x hx.
    exact:(@norm_domain_interior_neighbourhood R X NX hNX (W `&` Z) x).2
      (open_nbhs_nbhs (conj (openI hW hZOpen) hx)).
  + split;first by move=>x hx;exact:hx.2.
    split.
    * move=>x hx;exact:conj (@hAW x hx) (@hKZ x (@hAK x hx)).
    * move=>x hx;exact:(@hEqual x hx.1).
Qed.
End CurrentSupportSmoothComparisonExistence.
