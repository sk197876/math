(** Federer (1969), 4.1.12, p. 368: every
    neighbourhood Z of spt T gives the original
    localisation T in F_(m,K intersect Clos Z)(U).
    Reuse the actual scalar cutoff inside that
    neighbourhood and the preceding exact multiplier law. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormOpenTopology NormBoundedLinearTopology NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry
  SmoothCompactSet SmoothCompactClosureIntersection SmoothTestSpaces CurrentContraction
  CurrentNeighbourhoodCutoff CurrentScalarSupportPlateau CurrentFlatScalarTestProductBound
  CurrentFlatMultiplier CurrentFlatCompactMonotone FlatCurrentsUP FlatCurrentFinite FlatCurrentScalarClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentNeighbourhoodLocalisation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation inc0 := (smooth_test_inclusion (@current_smooth_space_laws R h2 n U hU 0%N)).

(** Source for [flat_current_neighbourhood_localisation]:
    T in F_(m,K)(U) belongs to
    F_(m,K intersect Clos Z)(U) for every original
    neighbourhood Z of its support, Federer
    4.1.12, p. 368. The neighbourhood need not
    be open; its interior supplies the cutoff. *)
Theorem flat_current_neighbourhood_localisation (K:smooth_compact_set hNX U) (T:C) (Z:set X):
  @is_flat_current_supported_in R h2 n m U hU K T->
  (forall x,support T x->@nbhs _ XT x Z)->
    @is_flat_current_supported_in R h2 n m U hU
      (@smooth_compact_closure_intersection R X NX hNX U K Z) T.
Proof.
move=>hFlat hZ.
have hSupport:=@flat_current_supported_support R h2 n m U hU K T hFlat.
have hCompact:=@current_support_compact_bound R h2 n m U hU K T hSupport.
pose L:=@Build_smooth_compact_set R X NX hNX U (support T) (fun x hx=>hx.1) hCompact.
pose W:=U `&` @interior XT Z.
have hOpenU:@open XT U.
  rewrite openE=>x hx.
  exact:(@norm_domain_interior_neighbourhood R X NX hNX U x).1 (hU x hx).
have hOpenW:@open XT W:=openI hOpenU (@open_interior XT Z).
have hLW:smooth_compact_carrier L `<=` W.
  move=>x hx;split;first exact:hx.1.
  exact:hZ x hx.
have hWU:W `<=` U by move=>x hx;exact:hx.1.
have [gamma [hGamma [V [hV [hLV [hVW hOne]]]]]]:=
  @current_neighbourhood_scalar_cutoff R h2 n U hU L W hOpenW hLW hWU.
pose contract:=@current_contraction R h2 n 0%N m U hU (inc0 gamma).
have hIdentity:T=contract T.
  apply:(@current_scalar_support_plateau R h2 n m U hU T (inc0 gamma) V hV hLV).
  - move=>x hx;exact:hWU x (hVW x hx).
  - exact:hOne.
have hMultiplier:=@flat_current_scalar_multiplier_supported R h2 n m U hU K gamma T hFlat.
pose M:=@current_flat_multiplier_compact R h2 n U hU K gamma.
pose N:=@smooth_compact_closure_intersection R X NX hNX U K Z.
have hMN:smooth_compact_carrier M `<=` smooth_compact_carrier N.
  move=>x hx.
  rewrite current_flat_multiplier_compact_carrier in hx.
  rewrite smooth_compact_closure_intersection_carrier;split;first exact:hx.1.
  apply:(@subset_closure XT Z x).
  exact:(@interior_subset XT Z x (hGamma x hx.2).2).
have hTarget:=@flat_current_compact_monotone R h2 n m U hU M N hMN (contract T) hMultiplier.
by rewrite -hIdentity in hTarget.
Qed.
End FlatCurrentNeighbourhoodLocalisation.
