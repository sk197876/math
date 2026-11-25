(** Federer (1969), 4.1.14, p. 370: the original
    smooth-approximation requirement determines at most one
    compact Lipschitz image. Test the two candidates on one
    existing compact-closure family and the actual open
    restriction of T. No normality of T is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct FiniteCoordinates LipschitzUP SmoothCompactSet
  SmoothCompactNeighbourhoods CurrentSpaces FlatCurrentsUP
  CurrentLipschitzCompactImage CurrentCompactLipschitzPushforwardUP
  CurrentCompactSmoothApproximationUP CurrentCompactSmoothApproximation
  CurrentCompactSmoothApproximationOriginal CurrentOpenRestriction
  CurrentFlatOpenRestriction CurrentFlatSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_compact_lipschitz_image_unique]:
    uniqueness of the original f#T, Federer 4.1.14,
    p. 370. Original fixed-K flat membership supplies
    a nonvacuous representative under inclusion; the
    chosen family is used only inside this proof. *)
Theorem current_compact_lipschitz_image_unique
    (R:realType) (h2:(1+1:R)!=0) n nu m
    (U:set (R_n R n)) (V:set (R_n R nu))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (hV:forall y,V y->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R nu)) V y)
    (f:R_n R n->R_n R nu) (hImage:forall x,U x->V (f x))
    (hLocal:@is_locally_metric_lipschitz R
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
      (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R nu))) U f)
    (K:smooth_compact_set (inner_norm_real_norm (@euclidean_inner_productP R n)) U)
    (T:@current_space R h2 n U hU m)
    (hFlat:@is_flat_current_supported_in R h2 n m U hU K T)
    (Q P:@current_space R h2 nu V hV m):
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T Q ->
  @is_current_compact_lipschitz_image R h2 n nu m U V hU hV
    f hImage hLocal K T P ->Q = P.
Proof.
move=>hQ hP.
have[L [Z [g [hLeast hApprox]]]]:=
  @current_lipschitz_compact_smooth_approximation_exists R n nu
    U V hU hV K f hLocal hImage.
pose hZ:=current_compact_smooth_domain_open hApprox.
pose hZU:=@current_compact_smooth_domain_in_domain R n nu U V K f L Z g hApprox.
pose hKZ:=current_compact_smooth_domain_contains hApprox.
pose KZ:=@current_compact_index_in_open R n U Z K hKZ.
pose S:=@current_open_restriction R h2 n m Z U hZ hU hZU T.
pose hS:=@flat_current_open_restriction R h2 n m U Z hU hZ hZU K hKZ T hFlat.
pose hCompact:=@flat_supported_current_compact R h2 n m Z hZ KZ S hS.
have hRecovery:=@flat_current_neighbourhood_inclusion_recovery R h2 n m U Z
  hU hZ hZU K hKZ T hFlat hCompact.
pose hG:=@current_compact_smooth_original_approximation R n nu U V K f L Z g hApprox.
pose fK:=@current_lipschitz_compact_image R n nu U V hU f hImage hLocal K.
have[E hE]:=@smooth_compact_neighbourhood_exists R (R_n R nu)
  (inner_norm (@euclidean_inner_productP R nu))
  (inner_norm_real_norm (@euclidean_inner_productP R nu)) nu
  (@coordinate_basis R nu) (@coordinate_basisP R nu) V hV fK.
have hInside x (hx:smooth_compact_carrier K x):
    norm_domain_interior (inner_norm (@euclidean_inner_productP R nu))
      (smooth_compact_carrier E) (f x).
  apply:hE;by exists x.
have hLimitQ:=hQ.2 E hInside Z hZ hZU hKZ S hS hRecovery g hG.
have hLimitP:=hP.2 E hInside Z hZ hZU hKZ S hS hRecovery g hG.
exact:(@current_flat_sequence_limit_unique R h2 nu m V hV E _ Q P hLimitQ hLimitP).
Qed.
