(** Federer (1969), 4.1.9, p. 364: the actual
    affine homotopy h_t=(1-t)f+tg has velocity g-f and
    spatial differential (1-t)Df+tDg. The original open
    time and space domains are retained. The hypothesis
    records the printed affine equality on that domain;
    it does not assume every affine path lies in V. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional NormDifferentialLocal NormDifferentialLinear
  NormDifferentialChain NormDifferentialArithmetic NormFiniteLinearBound NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCurveJacobian
  CurrentMapDifferential CurrentCartesianAffineSlice CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopySliceClass CurrentHomotopyTimeVelocity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentAffineHomotopyDifferential.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation W := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation slice := (@current_homotopy_slice_map R n nu h).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Local Notation P := (@euclidean_first_injection_map R 1%N n).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).
Hypothesis hAffine:forall t x,A t->U x->slice t x=(1-t)*:f x+t*:g x.
Arguments hAffine : clear implicits.

(** Source for [current_affine_homotopy_space_differential]:
    the original actual Dh_t equals (1-t)Df+tDg,
    Federer 4.1.9, p. 364. The assertion includes
    every original time in A, not only the closed unit interval. *)
Theorem current_affine_homotopy_space_differential t x:
  A t->U x->@current_map_differential R n nu U (slice t) x=
    (1-t)*:(@current_map_differential R n nu U f x)+t*:(@current_map_differential R n nu U g x).
Proof.
move=>ht hx.
have hF:=@current_map_differential_actual R n nu U f classes.1 x hx.
have hG:=@current_map_differential_actual R n nu U g classes.2 x hx.
have hScaleF:=@norm_differential_scale R X Y NX NY hNX hNY U f x _ (1-t) hF.
have hScaleG:=@norm_differential_scale R X Y NX NY hNX hNY U g x _ t hG.
have hSum:=@norm_differential_add R X Y NX NY hNY U
  (fun y=>(1-t)*:f y) (fun y=>t*:g y) x _ _ hScaleF hScaleG.
apply:(@current_map_differential_unique R n nu U (slice t) x).
apply:(@norm_differential_domain_agreement R X Y NX NY hNX U
  (fun y=>(1-t)*:f y+t*:g y) (slice t) x _ _ hSum)=>y hy.
exact:esym (hAffine t y ht hy).
Qed.

(** Source for [current_affine_homotopy_time_velocity]: the
    original actual h-dot_t(x) is g(x)-f(x), Federer
    4.1.9, p. 364. This uses the original chain
    rule and affine differential, including constant paths. *)
Theorem current_affine_homotopy_time_velocity t x:
  A t->U x->@current_homotopy_time_velocity R n nu A U h t x=g x-f x.
Proof.
move=>ht hx.
pose a:=@euclidean_one_embed R t.
have ha:AT a by rewrite /a /current_homotopy_time_domain euclidean_one_embedK.
pose inclusion:=fun s:W=>@euclidean_block_join R 1%N n (s,x).
pose L:=@euclidean_curve_linear_map R nu (g x-f x).
pose F:=fun s:W=>f x+L s.
have hImage s (hs:AT s):AU (inclusion s).
  change (AT (@euclidean_block_split R 1%N n (euclidean_block_join (s,x))).1 /\
    U (@euclidean_block_split R 1%N n (euclidean_block_join (s,x))).2).
  by rewrite euclidean_block_joinK;split.
have hD:=@current_map_differential_actual R (1+n)%N nu AU h hHomotopy.2 (inclusion a) (hImage a ha).
have hInclusion:=@current_cartesian_affine_slice_differential R 1%N n AT hAT x a ha.
have hChain:=@norm_differential_chain R W Z Y NW NZ NY hNW hNZ hNY AT AU inclusion h a P _ hInclusion hD.
have hActual:has_norm_differential NW NY AT (fun s=>h (inclusion s)) a
    (hom_comp (@current_map_differential R (1+n)%N nu AU h (inclusion a)) P).
  apply:(@norm_differential_restrict R W Y NW NY
    (fun s=>AT s /\ AU (inclusion s)) AT (fun s=>h (inclusion s)) a _).
  - move=>s hs;exact:conj hs (hImage s hs).
  - exact:(@hAT a ha).
  - exact:hChain.
have hBound:=@norm_finite_linear_bounded R W Y NW NY hNW hNY 1%N
  (@coordinate_basis R 1%N) (@coordinate_basisP R 1%N) L.
have hLinear:=@norm_differential_linear R W Y NW NY hNW hNY AT a L (@hAT a ha) hBound.
have hConstant:=@norm_differential_constant R W Y NW NY hNW hNY AT a (f x) (@hAT a ha).
have hKnown:=@norm_differential_add R W Y NW NY hNY AT (fun _=>f x) L a 0 L hConstant hLinear.
rewrite add0r in hKnown.
have hAgreement s (hs:AT s):F s=h (inclusion s).
  have hSlice:=hAffine (@euclidean_one_project R s) x hs hx.
  rewrite /current_homotopy_slice_map euclidean_one_projectK in hSlice.
  rewrite hSlice /F /L /euclidean_curve_linear_map /=.
  change (f x+(@euclidean_one_project R s)*:(g x-f x)=
    (1-@euclidean_one_project R s)*:f x+(@euclidean_one_project R s)*:g x).
  by rewrite scalerBr scalerBl scale1r addrA addrAC.
have hKnownActual:=@norm_differential_domain_agreement R W Y NW NY hNW AT
  F (fun s=>h (inclusion s)) a L hAgreement hKnown.
have hEqual:=norm_differential_unique hNW hNY hActual hKnownActual.
have hValue:=congr1 (fun M:Hom W Y=>M (@euclidean_one_embed R 1)) hEqual.
rewrite hom_compE in hValue.
change (@current_homotopy_time_velocity R n nu A U h t x=L (@euclidean_one_embed R 1)) in hValue.
rewrite /L /euclidean_curve_linear_map /= in hValue.
change (@current_homotopy_time_velocity R n nu A U h t x=
  (@euclidean_one_project R (@euclidean_one_embed R 1))*:(g x-f x)) in hValue.
by rewrite euclidean_one_embedK scale1r in hValue.
Qed.
End CurrentAffineHomotopyDifferential.
