(** Federer (1969), 4.1.18, pp. 375–376: the
    original quantitative L1 pair representation on every
    open U. Include the flat current in all of R^n,
    apply the original downward induction there, then
    restrict both compact fields. The original support
    tube and exact cost are unchanged. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanLebesgueDimensions CurrentDomain CurrentSpaces
  CurrentBoundary CurrentOpenRestriction CurrentOpenRestrictionBoundary
  CurrentFlatNorm FlatCurrentsUP CurrentFlatLonePairRepresentation
  CompactSummableMultivectorCarrierSupport SmoothCompactSet EuclideanClosedSupportTube
  EuclideanClosedSupportTubeNorm CurrentCompactTubeIndex CurrentFlatAmbientInclusion
  CurrentFlatLonePairFullRepresentation CompactSummableMultivectors
  CompactSummableMultivectorDensity CompactSummableMultivectorAmbient
  CompactSummableMultivectorOpenRestriction CurrentLonePairImageUP
  CurrentLonePairImageSealed CurrentLonePairCost
  SmoothingKernelSealed SmoothingDilationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OriginalSupportRepresentation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation FT:=(current_domain R n Full).
Local Notation WF d:=(@compact_summable_multivector_space R h2 n d Full hFull).
Local Notation valueF d:=(@compact_summable_multivector_value R h2 n d Full hFull).
Local Notation rawF d:=(@compact_summable_multivector_ambient_value R h2 n d Full hFull).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation UT:=(current_domain R n U).
Local Notation P:=(@current_lone_pair_space R h2 n m U hU).
Local Notation q:=(@CurrentLonePair.map R h2 n m U hU).
Local Notation J:=(@current_lone_pair_cost R h2 n m U hU).
Local Notation value d:=(@compact_summable_multivector_value R h2 n d U hU).
Local Notation restriction d:=(@current_open_restriction R h2 n d U Full hU hFull
  (fun _ _=>Logic.I)).

(** Source for [current_flat_lone_pair_original_support]: the
    original second proposition with literal support containment
    and the exact original J price, Federer 4.1.18,
    pp. 375–376. Vanishing off the compact E is promoted
    to the actual closed ambient field supports. *)
Theorem current_flat_lone_pair_original_support
    (K:smooth_compact_set hNX U)
    (T:@current_space R h2 n U hU m) (delta:R)
    (hFlat:@is_flat_current_supported_in R h2 n m U hU K T)
    (hDelta:0<delta)
    (hInside:@euclidean_closed_support_tube R n (smooth_compact_carrier K) delta `<=` U):
  let E:=@current_compact_closed_tube_index R n U K delta hInside in
  exists v:P,q v=T /\
    (@compact_summable_multivector_ambient_support R h2 n m U hU v.1 `|`
      @compact_summable_multivector_ambient_support R h2 n m.+1 U hU v.2)
      `<=` smooth_compact_carrier E /\
    ((J v)%:E<=@current_flat_norm R h2 n m U hU K T+delta%:E)%E.
Proof.
move=>E.
have[v [hValue [hXiOff [hEtaOff hCost]]]]:=
  @current_flat_lone_pair_representation R h2 n m U hU K T delta hFlat hDelta hInside.
have hXi:=@compact_summable_multivector_carrier_support R h2 n m U hU v.1 E hXiOff.
have hEta:=@compact_summable_multivector_carrier_support R h2 n m.+1 U hU v.2 E hEtaOff.
exists v;split;first exact:hValue.
split;last exact:hCost.
move=>x [hx|hx];[exact:hXi x hx|exact:hEta x hx].
Qed.
End OriginalSupportRepresentation.
