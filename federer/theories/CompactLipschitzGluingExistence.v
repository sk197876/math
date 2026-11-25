(** Federer (1969), 4.1.24, p. 380: construct
    a genuine common defining map for two separated
    compact source pieces. Earlier compact-neighbourhood laws
    provide disjoint compact neighbourhoods; the proved
    compact Lipschitz union theorem gives the global cap.
    Construction serves only as the independent laws'
    existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  FiniteCoordinates SmoothCompactSet SmoothCompactNeighbourhoods LipschitzUP LipschitzBasic
  CompactDisjointLipschitzUnion CompactLipschitzGluingUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

Section CompactLipschitzGluingExistence.
Variable R:realType.
Variables d n:nat.
Local Notation X:=(R_n R d).
Local Notation Y:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R d)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R d)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation YT:=(real_norm_metric_space hNY).
Variables (O0 O1:set X) (U:set Y).
Hypothesis hO0:forall x,O0 x->norm_domain_interior NX O0 x.
Hypothesis hO1:forall x,O1 x->norm_domain_interior NX O1 x.
Variable K0:smooth_compact_set hNX O0.
Variable K1:smooth_compact_set hNX O1.
Variables f0 f1:X->Y.
Hypothesis hDisjoint:forall x,smooth_compact_carrier K0 x->smooth_compact_carrier K1 x->False.
Hypothesis hF0:@is_metric_lipschitz R XT YT O0 f0.
Hypothesis hF1:@is_metric_lipschitz R XT YT O1 f1.
Hypothesis hImage0:forall x,O0 x->U (f0 x).
Hypothesis hImage1:forall x,O1 x->U (f1 x).
Arguments hO0 : clear implicits.
Arguments hO1 : clear implicits.
Arguments hDisjoint : clear implicits.
Arguments hImage0 : clear implicits.
Arguments hImage1 : clear implicits.

(** Source for [compact_lipschitz_gluing_exists]: the common
    original image witness used for addition in
    4.1.24, p. 380. Empty compacts and opens
    are included, and the target U need not be
    convex, connected or nonempty. *)
Theorem compact_lipschitz_gluing_exists:
  exists W0:set X,exists W1:set X,exists F:X->Y,
    @is_compact_lipschitz_gluing R d n O0 O1 U K0 K1 f0 f1 W0 W1 F.
Proof.
have hOpen0:@open XT O0.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX O0 x).1
    (hO0 x hx).
have hOpen1:@open XT O1.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX O1 x).1
    (hO1 x hx).
have hClosed1:@closed XT (smooth_compact_carrier K1).
  exact:compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact K1).
pose A0:set X:=O0 `\` smooth_compact_carrier K1.
have hA0Open:@open XT A0:=openI hOpen0 (closed_openC hClosed1).
have hA0:forall x,A0 x->norm_domain_interior NX A0 x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX A0 x).2.
  exact:open_nbhs_nbhs (conj hA0Open hx).
have hK0A0:smooth_compact_carrier K0 `<=` A0.
  move=>x hx;split;first exact:smooth_compact_in_domain K0 x hx.
  exact:hDisjoint x hx.
pose J0:=@Build_smooth_compact_set R X NX hNX A0
  (smooth_compact_carrier K0) hK0A0 (smooth_compact_is_compact K0).
have[E0 hK0Interior]:=@smooth_compact_neighbourhood_exists R X NX hNX d
  (@coordinate_basis R d) (@coordinate_basisP R d) A0 hA0 J0.
have hClosedE0:@closed XT (smooth_compact_carrier E0).
  exact:compact_closed (@metric_hausdorff R XT) (smooth_compact_is_compact E0).
pose A1:set X:=O1 `\` smooth_compact_carrier E0.
have hA1Open:@open XT A1:=openI hOpen1 (closed_openC hClosedE0).
have hA1:forall x,A1 x->norm_domain_interior NX A1 x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX A1 x).2.
  exact:open_nbhs_nbhs (conj hA1Open hx).
have hK1A1:smooth_compact_carrier K1 `<=` A1.
  move=>x hx;split;first exact:smooth_compact_in_domain K1 x hx.
  move=>hE;exact:(smooth_compact_in_domain E0 x hE).2 hx.
pose J1:=@Build_smooth_compact_set R X NX hNX A1
  (smooth_compact_carrier K1) hK1A1 (smooth_compact_is_compact K1).
have[E1 hK1Interior]:=@smooth_compact_neighbourhood_exists R X NX hNX d
  (@coordinate_basis R d) (@coordinate_basisP R d) A1 hA1 J1.
pose W0:set X:=@interior XT (smooth_compact_carrier E0).
pose W1:set X:=@interior XT (smooth_compact_carrier E1).
pose F:=fun x:X=>if pselect (smooth_compact_carrier E0 x) then f0 x else f1 x.
have hE0Value x:smooth_compact_carrier E0 x->F x=f0 x.
  move=>hx;rewrite /F;case:pselect=>// hNot;contradiction.
have hE1Value x:smooth_compact_carrier E1 x->F x=f1 x.
  move=>hx;rewrite /F;case:pselect=>// hE.
  exfalso;exact:(smooth_compact_in_domain E1 x hx).2 hE.
have hE0Lip:@is_metric_lipschitz R XT YT (smooth_compact_carrier E0) F.
  have[L [hL [hL0 hBound]]]:=hF0.
  exists L;split;first exact:hL.
  split;first exact:hL0.
  move=>x y hx hy;rewrite (@hE0Value x hx) (@hE0Value y hy).
  exact:(@hBound x y (smooth_compact_in_domain E0 x hx).1
    (smooth_compact_in_domain E0 y hy).1).
have hE1Lip:@is_metric_lipschitz R XT YT (smooth_compact_carrier E1) F.
  have[L [hL [hL0 hBound]]]:=hF1.
  exists L;split;first exact:hL.
  split;first exact:hL0.
  move=>x y hx hy;rewrite (@hE1Value x hx) (@hE1Value y hy).
  exact:(@hBound x y (smooth_compact_in_domain E1 x hx).1
    (smooth_compact_in_domain E1 y hy).1).
have hUnionLip:=@compact_disjoint_lipschitz_union R XT YT
  (smooth_compact_carrier E0) (smooth_compact_carrier E1) F
  (smooth_compact_is_compact E0) (smooth_compact_is_compact E1)
  (fun x hx hy=>(smooth_compact_in_domain E1 x hy).2 hx) hE0Lip hE1Lip.
have hInside0:W0 `<=` O0.
  move=>x hx;exact:(smooth_compact_in_domain E0 x (interior_subset hx)).1.
have hInside1:W1 `<=` O1.
  move=>x hx;exact:(smooth_compact_in_domain E1 x (interior_subset hx)).1.
exists W0,W1,F;constructor.
- exact:open_interior.
- exact:open_interior.
- move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX
    (smooth_compact_carrier E0) x).1 (@hK0Interior x hx).
- move=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX
    (smooth_compact_carrier E1) x).1 (@hK1Interior x hx).
- exact:hInside0.
- exact:hInside1.
- move=>x hx;exact:@hE0Value x (interior_subset hx).
- move=>x hx;exact:@hE1Value x (interior_subset hx).
- have[L [hL hBound]]:=hUnionLip.
  exists L;split;first exact:hL.
  apply:(@metric_lipschitz_bound_restrict R XT YT
    (smooth_compact_carrier E0 `|` smooth_compact_carrier E1) (W0 `|` W1) F L _ hBound).
  move=>x [hx|hx];[left|right];exact:interior_subset hx.
- move=>x [hx|hx].
  + rewrite (@hE0Value x (interior_subset hx));exact:hImage0 x (@hInside0 x hx).
  + rewrite (@hE1Value x (interior_subset hx));exact:hImage1 x (@hInside1 x hx).
Qed.
End CompactLipschitzGluingExistence.
