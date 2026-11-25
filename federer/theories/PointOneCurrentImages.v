(** Federer (1969), 4.1.15, p. 373: the original
    smooth images of the actual finite-mass point one-current.
    These maps are proper only on its support, as required
    by 4.1.7; no flat-current pushforward is used here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity NormRegularityOperations
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers AlternatingForms
  AlternatingPairing AlternatingDual CurrentSpaces CurrentProperSupport
  CurrentCompactMapProper CurrentPushforwardSealed CurrentCompactPushforwardAlgebra
  CurrentCompactPushforwardTests CurrentCompactSmoothValue
  PointMultivectorCurrentSmooth PointMultivectorCurrentSupport
  SmoothFormPullbackUP SmoothFormPullbackSealed SmoothTestSpaces
  CurrentElementaryPushforwards CurrentJoinSliceMapClass PointOneCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointOneCurrentImages.
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
Local Notation unit:=(e_lambda (@coordinate_basis R 1%N) (ord_tuple 1%N)).
Local Notation DT:=(@current_test_space R h2 1%N Full hFull 1%N).
Local Notation E:=(@current_smooth_space R h2 1%N Full hFull 1%N).
Local Notation ev:=(@current_smooth_value R h2 1%N Full hFull 1%N).
Local Notation value:=(@current_test_value R h2 1%N Full hFull 1%N).
Local Notation hE:=(@current_smooth_space_laws R h2 1%N Full hFull 1%N).

(** Source for [point_one_current_smooth_image_evaluation]: the
    point action in 4.1.15, p. 373, and the original
    pullback formula of 4.1.6 give the action of f#T
    at f(0), weighted by the actual Df(0)e_1. *)
Theorem point_one_current_smooth_image_evaluation (f:X->X)
    (hf:norm_class_all_orders hNX hNX Full f)
    (D:Hom X X) (hD:has_norm_differential NX NX Full f (0:X) D)
    (phi:DT):
  @current_value R h2 1%N Full hFull 1%N
    (@current_compact_map_pushforward R h2 1%N 1%N Full Full hFull hFull
      f (fun _ _=>Logic.I) hf 1%N T hT) phi=
    (value phi (f 0)) [tuple D e].
Proof.
pose P:=@SmoothFormPullback.operator R h2 1%N 1%N 1%N
  Full Full hFull hFull f (fun _ _=>Logic.I) hf.
rewrite /current_compact_map_pushforward
  (@current_compact_pushforward_test_value R h2 1%N 1%N 1%N
    Full Full hFull hFull f (fun _ _=>Logic.I) hf T _ hT phi).
have hCompact:hT=(@point_multivector_current_compact R h2
  1%N 1%N Full hFull (0:X) Logic.I unit):=Prop_irrelevance _ _.
rewrite hCompact /point_one_current point_multivector_current_smooth_value.
have hPull:=@smooth_form_pullback_values R 1%N 1%N 1%N Full Full
  E E ev ev f P (@SmoothFormPullback.laws R h2 1%N 1%N 1%N
    Full Full hFull hFull f (fun _ _=>Logic.I) hf)
  (smooth_test_inclusion hE phi) (0:X) D Logic.I hD.
rewrite hPull point_one_current_pairing A_m_dualE.
congr ((value phi (f 0)) _);apply:eq_from_tnth=>i.
by rewrite tnth_map (ord1 i) !tnth0.
Qed.

Local Notation IdClass:=(@current_join_slice_identity_smooth R 1%N).
Local Notation ZeroClass:=(fun k=>@norm_class_constant R X X NX NX hNX hNX
  Full (0:X) k hFull).
Local Notation Image:=(fun (x:X) (_:True)=>Logic.I).

(** Source for [point_one_current_identity_image]: the literal
    g#T=T for g(x)=x in 4.1.15, p. 373.
    The old smooth theorem permits this nonflat current. *)
Theorem point_one_current_identity_image:
  @current_compact_map_pushforward R h2 1%N 1%N Full Full hFull hFull
    (fun x:X=>x) Image IdClass 1%N T hT=T.
Proof.
exact:(@current_compact_identity_pushforward R h2 1%N Full hFull
  1%N T hT Image IdClass
  (@current_compact_map_proper R h2 1%N 1%N 1%N Full Full hFull T
    (fun x:X=>x) Image (norm_class_continuous (IdClass 0%N)) hT)).
Qed.

(** Source for [point_one_current_constant_image]: the literal
    f#T=0 for f(x)=0 in 4.1.15, p. 373.
    Again only the old smooth support-proper image is used. *)
Theorem point_one_current_constant_image:
  @current_compact_map_pushforward R h2 1%N 1%N Full Full hFull hFull
    (fun _:X=>0) Image ZeroClass 1%N T hT=0.
Proof.
exact:(@current_compact_constant_positive_pushforward R h2 1%N Full hFull
  0%N Full hFull (0:X) T hT Image ZeroClass
  (@current_compact_map_proper R h2 1%N 1%N 1%N Full Full hFull T
    (fun _:X=>0) Image (norm_class_continuous (ZeroClass 0%N)) hT)).
Qed.
End PointOneCurrentImages.
