(** Federer (1969), 4.1.15, p. 373, final paragraph:
    a fixed test one-form detects the nonconvergent slopes
    of smooth images of the finite-mass point current.
    The printed D_0 target is a degree mismatch: these
    images have degree one. The separate boundary sequence
    gives the correctly typed degree-zero counterpart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanOneNormDifferential EuclideanScalarCoordinateMaps
  EuclideanCoordinateForms OneFormIdentification AlternatingForms CurrentSpaces
  CurrentCompactPushforwardAlgebra CurrentWeakSequenceLimit
  ScalarCurrentCalibrationTest ScalarCurrentIntervalCompact SmoothCompactSet
  PointOneCurrent PointOneCurrentImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PointOneCurrentSequenceDivergence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation T:=(@point_one_current R h2).
Local Notation hT:=(@point_one_current_compact R h2).
Local Notation e:=(@coordinate_basis R 1%N ord0).
Variables u:nat->X->X.
Hypothesis hu:forall i,norm_class_all_orders hNX hNX Full (u i).
Variable D:nat->Hom X X.
Hypothesis hD:forall i,has_norm_differential NX NX Full (u i) (0:X) (D i).
Local Notation slope:=(fun i=>euclidean_one_project (D i e)).
Local Notation image:=(fun i=>@current_compact_map_pushforward R h2
  1%N 1%N Full Full hFull hFull (u i) (fun _ _=>Logic.I)
    (hu i) 1%N T hT).

(** Source for [point_one_current_image_sequence_diverges]:
    the final assertion of 4.1.15, p. 373.
    Convergence u_i(0)->0 suffices for the detecting test;
    the printed uniform convergence and differential bounds
    imply, but are stronger than, this needed premise. *)
Theorem point_one_current_image_sequence_diverges:
  (forall eps:R,0<eps->exists N,forall i,(N<=i)%N->NX (u i 0)<eps)->
  (~exists c:R,forall eps:R,0<eps->exists N,forall i,(N<=i)%N->
    `|slope i-c|<eps)->
  ~exists Q:@current_space R h2 1%N Full hFull 1%N,
    @is_current_weak_sequence_limit R h2 1%N 1%N Full hFull image Q.
Proof.
move=>hOrigin hSlope [Q hWeak].
have [phi [_ hPhi]]:=@scalar_current_calibration_test_exists R h2 (-1) 1.
have [N hN]:=hOrigin 1 ltr01.
have hAction:forall i,(N<=i)%N->
    @current_value R h2 1%N Full hFull 1%N (image i) phi=slope i.
  move=>i hi.
  rewrite (@point_one_current_smooth_image_evaluation R h2
    (u i) (hu i) (D i) (hD i) phi).
  have hAbs:`|euclidean_one_project (u i 0)|<1.
    change (`|(u i 0) ord0|<1).
    by rewrite -euclidean_one_norm_coordinate;exact:hN i hi.
  rewrite ltr_norml in hAbs.
  have hCarrier:smooth_compact_carrier
      (scalar_current_compact_interval R (-1) 1) (u i 0).
    rewrite scalar_current_compact_interval_carrier /=.
    apply/andP;split;[exact:ltW (andP hAbs).1|exact:ltW (andP hAbs).2].
  rewrite (hPhi (u i 0) hCarrier) /euclidean_coordinate_form
    one_formE /euclidean_scalar_coordinate_map /=.
  by [].
apply:hSlope;exists (@current_value R h2 1%N Full hFull 1%N Q phi).
move=>eps hEps.
have [M hM]:=hWeak phi eps hEps.
exists (maxn N M)=>i hi.
have hNi: (N<=i)%N:=leq_trans (leq_maxl N M) hi.
have hMi: (M<=i)%N:=leq_trans (leq_maxr N M) hi.
by rewrite -(hAction i hNi);exact:hM i hMi.
Qed.

(** Source for [point_one_current_uniform_image_sequence_diverges]:
    the printed global uniform convergence hypothesis of
    4.1.15, p. 373, supplies the preceding origin
    condition. No whole-line properness is required, even
    for compactly supported maps, because T has point support. *)
Theorem point_one_current_uniform_image_sequence_diverges:
  (forall eps:R,0<eps->exists N,forall i,(N<=i)%N->forall x,NX (u i x)<eps)->
  (~exists c:R,forall eps:R,0<eps->exists N,forall i,(N<=i)%N->
    `|slope i-c|<eps)->
  ~exists Q:@current_space R h2 1%N Full hFull 1%N,
    @is_current_weak_sequence_limit R h2 1%N 1%N Full hFull image Q.
Proof.
move=>hUniform hSlope;apply:point_one_current_image_sequence_diverges=>//.
move=>eps hEps;have [N hN]:=hUniform eps hEps.
exists N=>i hi;exact:hN i hi 0.
Qed.
End PointOneCurrentSequenceDivergence.
