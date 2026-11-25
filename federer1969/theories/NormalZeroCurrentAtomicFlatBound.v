(** Federer (1969), 4.1.23, p. 380:
    the individual transverse-cell estimate follows from
    the original degree-zero affine-cone estimate. Only
    the distance from the actual support to
    its tag is bounded; no larger flat
    support index is substituted for spt T. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom AffineMaps InnerConvex RealNormUP NormMetric
  NormDifferentialUP NormOpenDomainLaws NormRegularity InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanAffineSmooth CurrentSpaces CurrentDirac NormalCurrentsUP
  CurrentMassSealed CurrentMassBasic CompactRepresentedCurrentMass
  CurrentFlatNorm CurrentAffineSegmentHull CurrentNormalAffineUniformBound
  CurrentCompactMapProper CurrentCompactPushforwardAlgebra
  CurrentElementaryPushforwards CurrentOpenIdentitySmooth CurrentCompactSmoothValue
  SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normal_zero_current_atomic_flat_bound]:
    F_B(S-S(1)[b])<=d M(S), the individual
    zero-current estimate used in Federer 4.1.23,
    p. 380. It is the preceding sharp
    affine/cone inequality in degree zero, where
    the derivative factor is exactly one. Convexity
    is required only for the containing transverse
    box B; the final compact approximation index
    need not be convex. *)
Theorem normal_zero_current_atomic_flat_bound (R : realType)
    (h2 : (1+1:R)!=0) n
    (B : smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n))
      (fun _ : R_n R n => True))
    (hConvex : is_inner_convex (smooth_compact_carrier B))
    (b : R_n R n) (hB : smooth_compact_carrier B b)
    (T : @current_space R h2 n (fun _ => True)
      (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) 0%N)
    (hNormal : @is_normal_current R h2 n (fun _ => True)
      (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) 0%N T)
    (d : R) (hD : 0<=d)
    (hSupport : @current_support R h2 n (fun _ => True)
      (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) 0%N T `<=`
      smooth_compact_carrier B)
    (hDistance : forall x, @current_support R h2 n (fun _ => True)
      (fun (x : R_n R n) (_ : True) => norm_full_domain_interior
        (inner_norm (@euclidean_inner_productP R n)) x) 0%N T x ->
      inner_norm (@euclidean_inner_productP R n) (x-b)<=d) :
  let Full := fun _ : R_n R n => True in
  let hFull := fun (x : R_n R n) (_ : True) =>
    norm_full_domain_interior (inner_norm (@euclidean_inner_productP R n)) x in
  (@current_flat_norm R h2 n 0%N Full hFull B
    (T-(@current_compact_total R h2 n Full hFull T hNormal.2)*:
      (@dirac_current R h2 n Full hFull b))<=
    d%:E*@CurrentMass.value R h2 n 0%N Full hFull T)%E.
Proof.
cbn zeta.
pose Full := fun _ : R_n R n => True.
pose hFull := fun (x : R_n R n) (_ : True) => norm_full_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) x.
pose X := R_n R n.
pose NX := inner_norm (@euclidean_inner_productP R n).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
pose f := fun _ : X => b.
pose g := fun x : X => x.
pose image := fun (x : X) (_ : Full x) => Logic.I.
have hF : is_affine_map f.
  move=> x y a c hSum; by rewrite /f -scalerDl hSum scale1r.
pose hf := @euclidean_affine_map_smooth R n n Full hFull f hF.
pose hg := @current_open_identity_smooth R n Full hFull.
pose support := @current_support R h2 n Full hFull 0%N T.
pose K := @Build_smooth_compact_set R X NX hNX Full support
  (fun _ _ => Logic.I) hNormal.2.
have hHull : @current_affine_segment_hull R h2 n n 0%N Full hFull f g T
    `<=` smooth_compact_carrier B.
  move=> y [t [x [ht [hx <-]]]]; have /andP [ht0 ht1] := ht.
  exact: (@hConvex b x hB (@hSupport x hx) t ht0 ht1).
have hFinite := @compact_represented_current_finite_mass R h2 n 0%N
  Full hFull T hNormal.1.1 hNormal.2.
have [mass [_ hMass]] := @current_finite_mass_value R h2 n 0%N Full hFull T hFinite.
have hBound := @current_normal_affine_uniform_zero R h2 n n Full Full hFull hFull
  f g image image hf hg K B d hDistance T hNormal
  (fun _ hx => hx) hHull mass hMass.
have hIdentity := @current_compact_identity_pushforward R h2 n Full hFull 0%N
  T hNormal.2 image hg (@current_compact_map_proper R h2 n n 0%N Full Full
    hFull T g image (norm_class_continuous (hg 0%N)) hNormal.2).
have hConstant := @current_compact_constant_zero_pushforward R h2 n Full hFull
  Full hFull b T hNormal.2 image hf
  (@current_compact_map_proper R h2 n n 0%N Full Full hFull T f image
    (norm_class_continuous (hf 0%N)) hNormal.2).
rewrite /current_compact_map_pushforward hIdentity hConstant in hBound.
by rewrite hMass -EFinM.
Qed.
