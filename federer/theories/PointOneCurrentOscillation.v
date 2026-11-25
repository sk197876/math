(** Federer (1969), 4.1.15, p. 373: a concrete actual
    sequence violates the convergence assertion that holds for
    flat chains. Each old smooth image is exactly (-1)^i T;
    each boundary image is exactly (-1)^i boundary(T).
    Thus the degree-one images and the degree-zero boundary
    images both fail to converge weakly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom TensorUP RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws NormRegularity GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm HilbertFormCompactness AlternatingForms
  OneFormIdentification OneFormLinear CurrentSpaces CurrentEvaluation CurrentPointEvaluation
  CurrentBoundary CurrentCompactBoundarySmooth CurrentCompactPushforwardAlgebra
  CurrentCompactElementaryPushforwards CurrentMassSealed CurrentMassFiniteAlgebra
  CurrentWeakSequenceLimit CurrentAlternatingSequenceDivergence
  PointOneCurrent PointOneCurrentBoundary PointOneCurrentImages
  PointOneOscillatingMapsUP PointOneOscillatingMapsSealed
  PointOneOscillatingMapsBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section PointOneCurrentOscillation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation X:=(R_n R 1%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation T:=(@point_one_current R h2).
Local Notation hT:=(@point_one_current_compact R h2).
Local Notation B:=(@current_boundary R h2 1%N 0%N Full hFull T).
Local Notation hB:=(@current_compact_boundary_compact R h2 1%N 0%N Full hFull T hT).
Local Notation u:=(@PointOneOscillatingMaps.value R).
Local Notation hU:=(@PointOneOscillatingMaps.laws R).
Local Notation hu:=(fun i=>@point_one_oscillating_smooth R u hU i).
Local Notation hD:=(fun i=>@point_one_oscillating_origin_differential R u hU i).
Local Notation Id:=(hom_of_linear (@linear_id R X)).
Local Notation e:=(@coordinate_basis R 1%N ord0).
Local Notation image1:=(fun i=>@current_compact_map_pushforward R h2
  1%N 1%N Full Full hFull hFull (u i) (fun _ _=>Logic.I) (hu i) 1%N T hT).
Local Notation image0:=(fun i=>@current_compact_map_pushforward R h2
  1%N 1%N Full Full hFull hFull (u i) (fun _ _=>Logic.I) (hu i) 0%N B hB).

(** Source for [point_one_current_oscillating_images]: the actual
    maps satisfy u_i(0)=0 and Du_i(0)=(-1)^i Id,
    so the original point action in 4.1.15, p. 373,
    gives u_i#T=(-1)^i T on every actual test. *)
Theorem point_one_current_oscillating_images i:image1 i=(-1:R)^+i*:T.
Proof.
apply:(@current_values_extensional R h2 1%N 1%N Full hFull)=>phi.
rewrite (@point_one_current_smooth_image_evaluation R h2
  (u i) (hu i) ((-1:R)^+i*:Id) (hD i) phi)
  (@point_one_oscillating_zero R u hU i)
  current_value_scale point_one_current_evaluation.
pose a:=@current_test_value R h2 1%N Full hFull 1%N phi 0.
change (a [tuple (-1:R)^+i*:e]=(-1:R)^+i*a [tuple e]).
by rewrite -!one_homE linearZ.
Qed.

(** Source for [point_one_current_boundary_nonzero]: the actual
    boundary in 4.1.15, p. 373, is nonzero; its
    already proved infinite mass excludes the zero current. *)
Theorem point_one_current_boundary_nonzero:B<>0.
Proof.
move=>hZero.
have hFinite:(@CurrentMass.value R h2 1%N 0%N Full hFull B < +oo)%E.
  rewrite hZero current_mass_zero;exact:ltry.
by rewrite (@point_one_current_boundary_mass R h2) ltxx in hFinite.
Qed.

(** Source for [point_one_current_oscillating_boundary_images]: the
    correctly typed degree-zero counterpart of the final
    observation in 4.1.15, p. 373. The old boundary
    commutation law applies without finite mass of the boundary. *)
Theorem point_one_current_oscillating_boundary_images i:
  image0 i=(-1:R)^+i*:B.
Proof.
have hBoundary:=@current_compact_map_boundary_image R h2 1%N 1%N
  Full Full hFull hFull (u i) (fun _ _=>Logic.I) (hu i)
  0%N T hT hB.
rewrite point_one_current_oscillating_images linearZ in hBoundary.
exact:esym hBoundary.
Qed.

(** Source for [point_one_current_oscillating_images_diverge]: the
    concrete actual smooth images fail to converge in the
    space of one-currents, as intended by 4.1.15, p. 373.
    Their uniformly bounded differentials and uniform-zero limit
    are separately proved from the same opaque family laws. *)
Theorem point_one_current_oscillating_images_diverge:
  ~exists Q:@current_space R h2 1%N Full hFull 1%N,
    @is_current_weak_sequence_limit R h2 1%N 1%N Full hFull image1 Q.
Proof.
have hImages:image1=(fun i=>(-1:R)^+i*:T).
  apply:funext;exact:point_one_current_oscillating_images.
rewrite hImages.
exact:(@current_alternating_sequence_diverges R h2 1%N 1%N Full hFull
  T (@point_one_current_nonzero R h2)).
Qed.

(** Source for [point_one_current_oscillating_boundary_images_diverge]:
    the degree-zero boundary images also fail to converge.
    This is a genuine D_0 assertion, unlike the incorrectly
    typed D_0 attached to the degree-one images in the
    printed last line of 4.1.15, p. 373. *)
Theorem point_one_current_oscillating_boundary_images_diverge:
  ~exists Q:@current_space R h2 1%N Full hFull 0%N,
    @is_current_weak_sequence_limit R h2 1%N 0%N Full hFull image0 Q.
Proof.
have hImages:image0=(fun i=>(-1:R)^+i*:B).
  apply:funext;exact:point_one_current_oscillating_boundary_images.
rewrite hImages.
exact:(@current_alternating_sequence_diverges R h2 1%N 0%N Full hFull
  B point_one_current_boundary_nonzero).
Qed.
End PointOneCurrentOscillation.
