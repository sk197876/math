(** Federer (1969), 4.1.14, pp. 371–372: the
    original support-only affine chain retains both
    homotopy identities. Restrict to the preceding
    open neighbourhood of spt T, apply the
    original locally Lipschitz homotopy formula, and
    recover the actual global endpoint images.
    No flat index equal to spt T and
    no affine-image condition on all U is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormClassOneUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct LipschitzUP
  OpenLocalLipschitzCompact SmoothCompactSet CurrentSpaces CurrentProperSupport CurrentBoundary
  CurrentBoundarySupport CurrentOpenRestriction CurrentOpenRestrictionBoundary
  CurrentCompactContainingProper CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyCylinder CurrentHomotopyGeometry CurrentHomotopyEndpointProper
  CurrentHomotopyBoundaryCylinder CurrentHomotopyProductSupport
  CurrentAffineHomotopyUP CurrentAffineHomotopySealed
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCompactTimeCylinder
  CurrentHomotopyTimeSegment CurrentLocallyFlatTimeCylinder
  CurrentLocallyFlatBoundary FlatCurrentsUP FlatCurrentFinite
  CurrentLipschitzCompactImage FlatCurrentScalarClosure
  CurrentFlatSupportNeighbourhoodRestriction CurrentLipschitzHomotopyUP
  CurrentLipschitzHomotopySlices CurrentLipschitzDeformationChainSealed
  CurrentLipschitzHomotopyEndpointPushforward
  CurrentLipschitzHomotopyPositiveFormula CurrentLipschitzHomotopyZeroFormula
  CurrentLipschitzPushforwardSealed CurrentLipschitzPushforwardBasic
  CurrentFlatLipschitzPushforwardSealed CurrentFlatLipschitzPushforwardBasic
  CurrentFlatLipschitzProofIndependence CurrentFlatLipschitzSourceNeighbourhood
  CurrentApproximationOpenRestriction CurrentLipschitzAffineNeighbourhood
  CurrentAffineNeighbourhoodProductFlat CurrentLipschitzAffineChainUP
  CurrentLipschitzAffineChainSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lipschitz_homotopy_compact_support_proper]:
    the original closed cylinder of a compactly
    supported current is compact, so every original
    locally Lipschitz homotopy is proper there,
    supporting Federer 4.1.14, p. 371, by
    the compact-cylinder argument of 4.1.9, p. 363. *)
Theorem current_lipschitz_homotopy_compact_support_proper
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (A:set R) (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h)
    (T:@current_space R h2 n U (current_homotopy_source_open hHomotopy.1) m):
  @compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n U (current_homotopy_source_open hHomotopy.1) m T)->
  @is_current_homotopy_proper R h2 n nu m A U V f g h hHomotopy.1 T.
Proof.
move=>hCompact.
pose hA:=current_homotopy_parameter_interval hHomotopy.1.
pose AU:=@current_homotopy_product_domain R n A U.
pose hAU:=@current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) U
  (@current_homotopy_time_domain_open R A hA)
  (current_homotopy_source_open hHomotopy.1).
pose C:=@current_homotopy_closed_cylinder R h2 n nu m A U V f g h hHomotopy.1 T.
have hCylinder:@compact (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))) C.
  exact:(@current_compact_time_cylinder_is_compact R n
    (@current_support R h2 n U (current_homotopy_source_open hHomotopy.1) m T) hCompact).
exact:(@current_compact_containing_map_proper R (1+n)%N nu AU V C
  (@current_homotopy_cylinder_in_domain R h2 n nu m
    A U V f g h hHomotopy.1 T) h (current_homotopy_image hHomotopy.1)
  (@norm_open_local_lipschitz_class_zero R (R_n R (1+n)%N) (R_n R nu)
    (inner_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm (@euclidean_inner_productP R nu))
    (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N))
    (inner_norm_real_norm (@euclidean_inner_productP R nu)) AU h hAU hHomotopy.2)
  hCylinder).
Qed.

(** Source for [current_lipschitz_affine_neighbourhood_homotopy]:
    the original affine map is a locally Lipschitz
    homotopy on the derived A times W,
    supporting Federer 4.1.14, pp. 371–372.
    This proof adapter packages the given openness
    evidence and selects no witness. Consumers align
    proposition-valued proof parameters explicitly. *)
Definition current_lipschitz_affine_neighbourhood_homotopy
    (R:realType) n nu (U:set (R_n R n)) (V:set (R_n R nu))
    (W:set (R_n R n))
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hWU:forall x,W x->U x)
    (f g:R_n R n->R_n R nu)
    (hFLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (hGLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U g)
    (A:set R) (hA:@is_homotopy_parameter_interval R A)
    (hBand:forall t x,A t->W x->V ((1-t)*:f x+t*:g x)):
    @is_locally_lipschitz_current_homotopy R n nu A W V f g
      (@CurrentAffineHomotopy.value R n nu f g):=
  conj (@Build_is_current_homotopy_geometry R n nu A W V f g
    (@CurrentAffineHomotopy.value R n nu f g) hA hW hV
    (@current_affine_neighbourhood_image R n nu A W V f g hBand)
    (fun x (_:W x)=>current_affine_homotopy_start (CurrentAffineHomotopy.laws f g) x)
    (fun x (_:W x)=>current_affine_homotopy_end (CurrentAffineHomotopy.laws f g) x))
    (@current_affine_neighbourhood_local R n nu U W hW hWU f g
      hFLocal hGLocal A hA).

Section CurrentLipschitzAffineHomotopyNeighbourhood.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variables f g:X->Y.
Hypotheses (hFLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f)
  (hGLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g).
Variable T:@current_space R h2 n U hU m.
Hypothesis hFlat:@is_flat_current R h2 n m U hU T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU m T x->
  V ((1-t)*:f x+t*:g x).
Variables (A:set R) (W:set X).
Local Notation H:=(@CurrentAffineHomotopy.value R n nu f g).
Hypothesis hHomotopy:@is_locally_lipschitz_current_homotopy R n nu
  A W V f g H.
Local Notation hW:=(current_homotopy_source_open hHomotopy.1).
Local Notation hV:=(current_homotopy_target_open hHomotopy.1).
Local Notation hA:=(current_homotopy_parameter_interval hHomotopy.1).
Hypothesis hWU:forall x,W x->U x.
Hypothesis hSupport:@current_support R h2 n U hU m T `<=` W.
Hypothesis hImage:forall t x,A t->W x->V ((1-t)*:f x+t*:g x).
Local Notation Q:=(@CurrentLipschitzAffineChain.value R h2 n nu m
  U V hU hV f g hFLocal hGLocal T hFlat hBand).

(** Source for [current_lipschitz_affine_chain_neighbourhood_homotopy]:
    every original support-neighbourhood representative
    computes the actual affine chain as the
    preceding A-open deformation chain, supporting
    Federer 4.1.14, pp. 371–372. Arbitrary
    evidence of local flatness and properness is
    accepted; the representative is the actual restriction. *)
Lemma current_lipschitz_affine_chain_neighbourhood_homotopy
    (S:@current_space R h2 n W hW m)
    (hS:@is_locally_flat_current R h2 n m W hW S)
    (hProper:@is_current_homotopy_proper R h2 n nu m A W V f g H hHomotopy.1 S):
  S=@current_open_restriction R h2 n m W U hW hU hWU T->
  Q=@CurrentLipschitzDeformationChain.value R h2 n nu m A W V f g H
    hHomotopy S hS hProper.
Proof.
move=>hEquality;subst S.
pose hProduct:=@current_affine_neighbourhood_product_flat R h2 n m A hA
  U W hU hW hWU T hFlat hSupport.
pose product:=@current_affine_neighbourhood_product R h2 n m
  A hA U W hU hW hWU T.
pose AW:=@current_homotopy_product_domain R n A W.
pose hAW:=@current_cartesian_domain_open R 1%N n
  (@current_homotopy_time_domain R A) W (@current_homotopy_time_domain_open R A hA) hW.
pose product_local:=@locally_flat_current_time_cylinder R h2 n m A W hA hW
  (@current_open_restriction R h2 n m W U hW hU hWU T) hS.
pose product_proper:=@current_homotopy_product_proper R h2 n nu m
  A W V f g H hHomotopy.1
  (@current_open_restriction R h2 n m W U hW hU hWU T) hProper.
have hChain:=(@CurrentLipschitzAffineChain.laws R h2 n nu m
  U V hU hV f g hFLocal hGLocal T hFlat hBand).2
  A hA W hW hWU hSupport hImage hProduct.
rewrite (@current_lipschitz_deformation_chain_pushforward R h2 n nu m
  A W V f g H hHomotopy _ hS hProper).
have hCompact:=@current_lipschitz_pushforward_compact R h2 (1+n)%N nu (1+m)%N
  AW V hAW hV H (current_homotopy_image hHomotopy.1) hHomotopy.2
  product product_local product_proper hProduct.
rewrite hCompact.
apply:(eq_trans hChain).
exact:(@current_flat_lipschitz_pushforward_data_independent R h2 (1+n)%N nu (1+m)%N
  AW V hAW hV H (@current_affine_neighbourhood_image R n nu A W V f g hImage)
  (current_homotopy_image hHomotopy.1)
  (@current_affine_neighbourhood_local R n nu U W hW hWU f g hFLocal hGLocal A hA)
  hHomotopy.2 product hProduct hProduct).
Qed.
End CurrentLipschitzAffineHomotopyNeighbourhood.

(** Source for [current_lipschitz_flat_neighbourhood_image]:
    the local image of the actual open restriction
    recovers the original global flat image,
    supporting the endpoint transfer in Federer
    4.1.14, pp. 371–372. All local evidence
    is arbitrary and the original support alone
    has to lie in the smaller open domain. *)
Local Lemma current_lipschitz_flat_neighbourhood_image
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U W:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hW:forall x,W x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) W x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (hWU:forall x,W x->U x) (f:R_n R n->R_n R nu)
    (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current R h2 n m U hU T)
    (hSupport:@current_support R h2 n U hU m T `<=` W)
    (hImageW:forall x,W x->V (f x))
    (hLocalW:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) W f)
    (hSFlat:@is_flat_current R h2 n m W hW
      (@current_open_restriction R h2 n m W U hW hU hWU T))
    (hS:@is_locally_flat_current R h2 n m W hW
      (@current_open_restriction R h2 n m W U hW hU hWU T))
    (hProper:@is_current_proper_on_support R h2 n nu m W hW V
      (@current_open_restriction R h2 n m W U hW hU hWU T) f hImageW):
  @CurrentLipschitzPushforward.value R h2 n nu m W V hW hV
    f hImageW hLocalW _ hS hProper=
  @CurrentFlatLipschitzPushforward.value R h2 n nu m U V hU hV
    f hImage hLocal T hFlat.
Proof.
rewrite (@current_lipschitz_pushforward_compact R h2 n nu m W V hW hV
  f hImageW hLocalW _ hS hProper hSFlat).
apply:(eq_trans (@current_flat_lipschitz_pushforward_data_independent R h2 n nu m
  W V hW hV f hImageW (fun x hx=>@hImage x (@hWU x hx)) hLocalW
  (@metric_local_lipschitz_domain_restriction R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu)))
    U W f hWU hLocal) _ hSFlat hSFlat)).
exact:esym (@current_flat_lipschitz_pushforward_open_restriction R h2 n nu m
  U W V hU hW hV hWU f hImage hLocal T hFlat hSupport hSFlat).
Qed.

Section CurrentLipschitzAffineHomotopyFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Hypotheses (hFImage:forall x,U x->V (f x)) (hGImage:forall x,U x->V (g x)).
Hypotheses (hFLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U f)
  (hGLocal:@is_locally_metric_lipschitz R
    (real_norm_metric_space hNX) (real_norm_metric_space hNY) U g).

Section Positive.
Variable j:nat.
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hFlat:@is_flat_current R h2 n j.+1 U hU T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU j.+1 T x->
  V ((1-t)*:f x+t*:g x).
Local Notation boundary:=(@current_boundary R h2 n j U hU T).
Local Notation boundary_flat:=(@flat_current_boundary R h2 n j U hU T hFlat).
Let boundary_band:forall t x,0<=t<=1->@current_support R h2 n U hU j boundary x->
    V ((1-t)*:f x+t*:g x):=
  fun t x ht hx=>@hBand t x ht (@current_boundary_support_subset R h2 n j U hU T x hx).
Local Notation Q:=(@CurrentLipschitzAffineChain.value R h2 n nu j.+1 U V hU hV
  f g hFLocal hGLocal T hFlat hBand).
Local Notation QB:=(@CurrentLipschitzAffineChain.value R h2 n nu j U V hU hV
  f g hFLocal hGLocal boundary boundary_flat boundary_band).

(** Source for [current_lipschitz_affine_homotopy_positive_formula]:
    g#T-f#T equals boundary of the actual
    affine chain plus the affine chain of
    boundary T, supporting the normal affine
    estimates of Federer 4.1.14, pp. 371–372.
    T is any flat current and only the
    segments above spt T have to lie in V. *)
Theorem current_lipschitz_affine_homotopy_positive_formula:
  @CurrentFlatLipschitzPushforward.value R h2 n nu j.+1 U V hU hV
    g hGImage hGLocal T hFlat-
  @CurrentFlatLipschitzPushforward.value R h2 n nu j.+1 U V hU hV
    f hFImage hFLocal T hFlat=
  @current_boundary R h2 nu j.+1 V hV Q+QB.
Proof.
have[A [hA [W [hW [hWU [hSupport hImage]]]]]]:=
  @current_lipschitz_affine_neighbourhood_exists R h2 n nu j.+1 U V hU hV
    f g hFLocal hGLocal T hFlat hBand.
pose H:=@CurrentAffineHomotopy.value R n nu f g.
pose hHomotopy:=@current_lipschitz_affine_neighbourhood_homotopy R n nu U V W
  hV hW hWU f g hFLocal hGLocal A hA hImage.
clearbody hHomotopy.
have hSource:hW=current_homotopy_source_open hHomotopy.1:=Prop_irrelevance _ _.
have hTarget:hV=current_homotopy_target_open hHomotopy.1:=Prop_irrelevance _ _.
have hTime:hA=current_homotopy_parameter_interval hHomotopy.1:=Prop_irrelevance _ _.
subst hW hV hA.
pose hSourceOpen:=current_homotopy_source_open hHomotopy.1.
pose hTargetOpen:=current_homotopy_target_open hHomotopy.1.
pose hTimeInterval:=current_homotopy_parameter_interval hHomotopy.1.
pose S:=@current_open_restriction R h2 n j.+1 W U hSourceOpen hU hWU T.
have[hSFlat _]:=@flat_current_support_neighbourhood_restriction R h2 n j.+1
  U W hU hSourceOpen hWU T hFlat hSupport.
pose hSLocal:=fun gamma=>@flat_current_scalar_multiplier R h2 n j.+1 W hSourceOpen
  gamma S hSFlat.
have[K hSK]:=hSFlat.
have hCompact:=@flat_supported_current_compact R h2 n j.+1 W hSourceOpen K S hSK.
pose hp:=@current_lipschitz_homotopy_compact_support_proper R h2 n nu j.+1
  A W V f g H hHomotopy S hCompact.
have hFormula:=@current_lipschitz_homotopy_positive_formula R h2 n nu j
  A W V f g H hHomotopy S hSLocal hp.
pose endImage:=current_homotopy_endpoint_images hHomotopy.1.
pose endLocal:=@current_lipschitz_homotopy_endpoints R n nu A W V f g H
  hHomotopy.1 hHomotopy.2.
have hF:=@current_lipschitz_flat_neighbourhood_image R h2 n nu j.+1
  U W V hU hSourceOpen hTargetOpen hWU f hFImage hFLocal T hFlat hSupport endImage.1 endLocal.1
  hSFlat hSLocal (@current_homotopy_start_proper R h2 n nu j.+1
    A W V f g H hHomotopy.1 S hp).
have hG:=@current_lipschitz_flat_neighbourhood_image R h2 n nu j.+1
  U W V hU hSourceOpen hTargetOpen hWU g hGImage hGLocal T hFlat hSupport endImage.2 endLocal.2
  hSFlat hSLocal (@current_homotopy_end_proper R h2 n nu j.+1
    A W V f g H hHomotopy.1 S hp).
have hQ:=@current_lipschitz_affine_chain_neighbourhood_homotopy R h2 n nu j.+1
  U V hU f g hFLocal hGLocal T hFlat hBand A W hHomotopy hWU hSupport hImage
  S hSLocal hp (erefl S).
have hBoundarySupport:@current_support R h2 n U hU j boundary `<=` W.
  move=>x hx;exact:(@hSupport x (@current_boundary_support_subset R h2 n j U hU T x hx)).
pose SB:=@current_boundary R h2 n j W hSourceOpen S.
pose hSBLocal:=@locally_flat_current_boundary R h2 n j W hSourceOpen S hSLocal.
pose hpB:=@current_homotopy_boundary_cylinder_proper R h2 n nu j
  A W V f g H hHomotopy.1 S hp.
have hSBEquality:SB=@current_open_restriction R h2 n j W U hSourceOpen hU hWU boundary.
  exact:esym (@current_open_restriction_boundary R h2 n j W U hSourceOpen hU hWU T).
have hQB:=@current_lipschitz_affine_chain_neighbourhood_homotopy R h2 n nu j
  U V hU f g hFLocal hGLocal boundary boundary_flat boundary_band
  A W hHomotopy hWU hBoundarySupport hImage SB hSBLocal hpB hSBEquality.
by rewrite hF hG -hQ -hQB in hFormula.
Qed.
End Positive.

Section Zero.
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hFlat:@is_flat_current R h2 n 0%N U hU T.
Hypothesis hBand:forall t x,0<=t<=1->@current_support R h2 n U hU 0%N T x->
  V ((1-t)*:f x+t*:g x).
Local Notation Q:=(@CurrentLipschitzAffineChain.value R h2 n nu 0%N U V hU hV
  f g hFLocal hGLocal T hFlat hBand).

(** Source for [current_lipschitz_affine_homotopy_zero_formula]:
    g#T-f#T is boundary of the actual
    affine chain for every original flat
    degree-zero T, supporting Federer 4.1.14,
    pp. 371–372. Only support segments need
    lie in V; there is no negative-degree term. *)
Theorem current_lipschitz_affine_homotopy_zero_formula:
  @CurrentFlatLipschitzPushforward.value R h2 n nu 0%N U V hU hV
    g hGImage hGLocal T hFlat-
  @CurrentFlatLipschitzPushforward.value R h2 n nu 0%N U V hU hV
    f hFImage hFLocal T hFlat=
  @current_boundary R h2 nu 0%N V hV Q.
Proof.
have[A [hA [W [hW [hWU [hSupport hImage]]]]]]:=
  @current_lipschitz_affine_neighbourhood_exists R h2 n nu 0%N U V hU hV
    f g hFLocal hGLocal T hFlat hBand.
pose H:=@CurrentAffineHomotopy.value R n nu f g.
pose hHomotopy:=@current_lipschitz_affine_neighbourhood_homotopy R n nu U V W
  hV hW hWU f g hFLocal hGLocal A hA hImage.
clearbody hHomotopy.
have hSource:hW=current_homotopy_source_open hHomotopy.1:=Prop_irrelevance _ _.
have hTarget:hV=current_homotopy_target_open hHomotopy.1:=Prop_irrelevance _ _.
have hTime:hA=current_homotopy_parameter_interval hHomotopy.1:=Prop_irrelevance _ _.
subst hW hV hA.
pose hSourceOpen:=current_homotopy_source_open hHomotopy.1.
pose hTargetOpen:=current_homotopy_target_open hHomotopy.1.
pose hTimeInterval:=current_homotopy_parameter_interval hHomotopy.1.
pose S:=@current_open_restriction R h2 n 0%N W U hSourceOpen hU hWU T.
have[hSFlat _]:=@flat_current_support_neighbourhood_restriction R h2 n 0%N
  U W hU hSourceOpen hWU T hFlat hSupport.
pose hSLocal:=fun gamma=>@flat_current_scalar_multiplier R h2 n 0%N W hSourceOpen
  gamma S hSFlat.
have[K hSK]:=hSFlat.
have hCompact:=@flat_supported_current_compact R h2 n 0%N W hSourceOpen K S hSK.
pose hp:=@current_lipschitz_homotopy_compact_support_proper R h2 n nu 0%N
  A W V f g H hHomotopy S hCompact.
have hFormula:=@current_lipschitz_homotopy_zero_formula R h2 n nu
  A W V f g H hHomotopy S hSLocal hp.
pose endImage:=current_homotopy_endpoint_images hHomotopy.1.
pose endLocal:=@current_lipschitz_homotopy_endpoints R n nu A W V f g H
  hHomotopy.1 hHomotopy.2.
have hF:=@current_lipschitz_flat_neighbourhood_image R h2 n nu 0%N
  U W V hU hSourceOpen hTargetOpen hWU f hFImage hFLocal T hFlat hSupport endImage.1 endLocal.1
  hSFlat hSLocal (@current_homotopy_start_proper R h2 n nu 0%N
    A W V f g H hHomotopy.1 S hp).
have hG:=@current_lipschitz_flat_neighbourhood_image R h2 n nu 0%N
  U W V hU hSourceOpen hTargetOpen hWU g hGImage hGLocal T hFlat hSupport endImage.2 endLocal.2
  hSFlat hSLocal (@current_homotopy_end_proper R h2 n nu 0%N
    A W V f g H hHomotopy.1 S hp).
have hQ:=@current_lipschitz_affine_chain_neighbourhood_homotopy R h2 n nu 0%N
  U V hU f g hFLocal hGLocal T hFlat hBand A W hHomotopy hWU hSupport hImage
  S hSLocal hp (erefl S).
by rewrite hF hG -hQ in hFormula.
Qed.
End Zero.
End CurrentLipschitzAffineHomotopyFormula.
