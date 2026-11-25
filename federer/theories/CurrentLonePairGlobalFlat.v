(** Federer (1969), 4.1.18, p. 375: every
    original compact L1 pair has an actual value in
    F_m(U). The preceding first proposition supplies
    flat membership after choosing a positive closed tube
    inside U. No finite mass of q is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet CompactSummableMultivectorAmbient
  CurrentLonePairImageUP CurrentLonePairImageSealed
  CurrentLonePairFlatMembership CurrentCompactClosedTubeInside FlatCurrentsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_lone_pair_is_flat]: q really takes
    values in the original compact-index union,
    Federer 4.1.18, p. 375. The compact index
    is proved to exist rather than included in q's definition. *)
Theorem current_lone_pair_is_flat (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (v:@current_lone_pair_space R h2 n m U hU):
  @is_flat_current R h2 n m U hU (@CurrentLonePair.map R h2 n m U hU v).
Proof.
pose X:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose A:=@compact_summable_multivector_ambient_support R h2 n m U hU v.1.
pose B:=@compact_summable_multivector_ambient_support R h2 n m.+1 U hU v.2.
have hA:=@compact_summable_multivector_ambient_support_laws R h2 n m U hU v.1.
have hB:=@compact_summable_multivector_ambient_support_laws R h2 n m.+1 U hU v.2.
have hInside:(A `|` B) `<=` U.
  move=>x [hx|hx];[exact:hA.2.1 x hx|exact:hB.2.1 x hx].
pose K:=@Build_smooth_compact_set R X NX hNX U (A `|` B) hInside (compactU hA.1 hB.1).
have[delta [hDelta hTube]]:=@current_compact_closed_tube_inside_exists R n U hU K.
have hFirst:=@current_lone_pair_flat_membership R h2 n m U hU v delta hDelta hTube.
eexists;exact:hFirst.1.
Qed.
