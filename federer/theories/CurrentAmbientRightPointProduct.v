(** Federer (1969), 4.1.11, p. 366: the
    original right point product is the affine inclusion
    image. This supplies the zero-dimensional endpoint
    of the simplicial prism induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom AffineMaps RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanAffineSmooth
  EuclideanBlockCoordinates EuclideanCartesianMap CurrentSpaces CurrentDirac CurrentCartesianDomain
  CurrentCompactRightPointProduct CurrentCompactPushforwardAlgebra CurrentCartesianMapPullback
  CurrentJoinAffineSourcePushforward CurrentDegreeTransport CurrentDomainTransport
  CurrentDomainTransportDegree CurrentDomainTransportPushforward CurrentAmbientCartesianProduct
  CurrentPointInclusionAffine OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws OrientedSimplexCurrentAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentAmbientRightPointProduct.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation AB := (@euclidean_cartesian_set R m n (Full m) (Full n)).
Local Notation hAB := (@current_cartesian_domain_open R m n (Full m) (Full n) (hFull m) (hFull n)).
Variable b:Y.
Local Notation inclusion := (@current_cartesian_right_point_inclusion R m n b).
Local Notation hAffine := (@current_right_point_inclusion_affine R m n b).
Local Notation Image := (@current_cartesian_right_point_image R m n
  (Full m) (Full n) b Logic.I).
Local Notation FullImage := (fun (x:X) (_:True)=>Logic.I).
Local Notation Smooth := (@current_cartesian_right_point_smooth R m n
  (Full m) (Full n) (hFull m) (hFull n) b Logic.I).
Local Notation AGlobal := (@euclidean_affine_map_smooth R m (m+n)%N
  (Full m) (hFull m) inclusion hAffine).
Local Notation AClass := (@current_cartesian_factor_open_class R m (m+n)%N
  (Full m) (hFull m) inclusion AGlobal).

(** Source for [current_ambient_right_point_product]:
    T times delta_b is the original affine image
    under x mapped to (x,b), supporting Federer
    4.1.11, p. 366. The sole degree transport
    identifies j+0 with j. *)
Theorem current_ambient_right_point_product j
    (T:@current_space R h2 m (Full m) (hFull m) j)
    (hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R m)))
      (@current_support R h2 m (Full m) (hFull m) j T)):
  @current_degree_transport R h2 (m+n)%N (Full (m+n)%N) (hFull (m+n)%N)
    (j+0)%N j (addn0 j)
    (@current_ambient_cartesian_product R h2 m n j 0%N T
      (@dirac_current R h2 n (Full n) (hFull n) b))=
  @current_join_affine_current R h2 m (m+n)%N inclusion hAffine j T hT.
Proof.
have hOriginal:=@current_compact_right_point_product R h2 m n j
  (Full m) (Full n) (hFull m) (hFull n) b Logic.I T hT.
have hDomain:=@current_domain_transport_compact_pushforward R h2 m (m+n)%N
  (Full m) AB (Full (m+n)%N) (hFull m) hAB (@current_cartesian_full_domain R m n)
  (hFull (m+n)%N) inclusion Image FullImage Smooth j T hT.
rewrite /current_ambient_cartesian_product -current_domain_transport_degree hOriginal hDomain
  /current_join_affine_current.
have hClass:Smooth=AClass:=Prop_irrelevance _ _.
by rewrite hClass.
Qed.

(** Source for [current_ambient_right_point_simplex]:
    [u_0,...,u_j] times delta_b is the original
    [(u_0,b),...,(u_j,b)], supporting the base prism
    case in Federer 4.1.11, p. 366. *)
Theorem current_ambient_right_point_simplex j (v:'I_(j.+1)->X):
  @current_degree_transport R h2 (m+n)%N (Full (m+n)%N) (hFull (m+n)%N)
    (j+0)%N j (addn0 j)
    (@current_ambient_cartesian_product R h2 m n j 0%N
      (@OrientedSimplexCurrent.value R h2 m j v)
      (@dirac_current R h2 n (Full n) (hFull n) b))=
  @OrientedSimplexCurrent.value R h2 (m+n)%N j
    (fun k=>@euclidean_block_join R m n (v k,b)).
Proof.
pose hV:=@oriented_simplex_current_compact R h2 m j v.
rewrite (@current_ambient_right_point_product j (@OrientedSimplexCurrent.value R h2 m j v) hV).
have hImage:=@oriented_simplex_current_affine R h2 m (m+n)%N inclusion hAffine j v hV.
have hVertices:(fun k=>inclusion (v k))=(fun k=>@euclidean_block_join R m n (v k,b)).
  apply:funext=>k;exact:current_right_point_inclusion_values.
by rewrite hVertices in hImage.
Qed.
End CurrentAmbientRightPointProduct.
