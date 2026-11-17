(** Federer (1969), 3.4.8(11), pp. 334–335:
    the original D restricted by a small
    prefix ball has finitely many components.
    Use the exact component homeomorphisms and
    finite fibres of (10), then the proved
    smaller-depth ball argument for chi times Delta. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormDifferentialUP NormAnalyticUP NormAnalyticLocal NormRegularity
  NormClassZeroNonzeroLocus NormAnalyticOperations NormAnalyticScalarProducts MetricSubsetBackground HomeomorphismUP SetGermUP
  FiniteAnalyticVarietyUP GermVanishingSealed AnalyticDepthSealed NormOpenComponents RestrictedFiniteComponents
  AnalyticSmallBallComponents.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RestrictedProjection.
Variable R:realType.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R m.+1).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R m.+1)).
Local Notation TX:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation TY:=(Topological.clone (real_norm_metric_space hNY) _).
Local Notation germ:=(@set_germ TY 0).
Local Notation depth:=(@AnalyticDepth.value R Y (@euclidean_inner_product R m.+1)
  (@euclidean_inner_productP R m.+1) m.+1 (@coordinate_basis R m.+1) (@coordinate_basisP R m.+1)
  (dual_basis (@coordinate_basisP R m.+1))).
Local Notation ideal:=(@AnalyticSetIdeal.value R Y NY hNY 0).
Variables (P:Hom X Y) (Z:set X) (U A:set Y) (chi delta:Y->R^o).
Local Notation V:=[set y|U y /\delta y!=0].

(** Source for [analytic_restricted_projection_components_from_lower_depth]:
    derive the actual finite component bound for
    every sufficiently small original T,
    3.4.8(11), p. 335. The only
    induction input is local finiteness at depths
    below the original positive base dimension. *)
Theorem analytic_restricted_projection_components_from_lower_depth:
  A 0 ->A `<=` U ->
  @norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) A chi ->
  @norm_analytic R Y R^o NY (fun z:R^o=>`|z|) hNY (@scalar_absolute_value_norm R) U delta ->
  continuous (fun x:real_norm_metric_space hNX=>(P x:real_norm_metric_space hNY)) ->
  (forall x,Z x ->V (P x)) ->
  (forall x,Z x ->exists F:metric_subset [set a:real_norm_metric_space hNX|
      @connected_component (real_norm_metric_space hNX) Z x a]->
      metric_subset [set y:real_norm_metric_space hNY|
        @connected_component (real_norm_metric_space hNY) V (P x) y],
    (forall a,val (F a) = P (val a)) /\is_homeomorphism F) ->
  (forall y,finite_set [set x|Z x /\P x = y]) ->
  (forall W L:set Y,W 0 ->@is_finite_analytic_variety R Y NY hNY W L ->
    germ L<>germ set0 ->(depth (ideal (germ L))<m.+1)%N ->
    exists O:set Y,@open TY O /\O 0 /\
      finite_set (@connected_component TY L @` (L `&` O))) ->
  exists r:R,0<r /\[set y|NY y<=r] `<=` A /\
    forall s:R,0<s ->s<=r ->finite_set
      (@connected_component TX
        ([set x|Z x /\chi (P x)<>0] `&` [set x|NY (P x)<s]) @`
        ([set x|Z x /\chi (P x)<>0] `&` [set x|NY (P x)<s])).
Proof.
move=>hA0 hAU hChi hDelta hP hRange hHomeomorphisms hFibres hInduction.
have hClassZero:=norm_class_continuous (norm_analytic_class_all_orders hChi 0%N).
have hInterior y (hy:A y):norm_domain_interior NY A y:=(@hClassZero y hy).1.
have hDeltaA:=@norm_analytic_open_restriction R Y R^o NY (fun z:R^o=>`|z|) hNY
  (@scalar_absolute_value_norm R) U A delta hAU hInterior hDelta.
have hProduct:=norm_analytic_scalar_product hChi hDeltaA.
have [r [hr [hRU hFinite]]]:=@analytic_small_ball_components_from_lower_depth R m A
  (fun y=>chi y*delta y) hA0 hProduct hInduction.
have hVOpen:@open (real_norm_metric_space hNY) V.
  exact:(@norm_class_zero_nonzero_locus_open R Y R^o NY (fun z:R^o=>`|z|) hNY
    (@scalar_absolute_value_norm R) U delta
    (norm_class_continuous (norm_analytic_class_all_orders hDelta 0%N))).
exists r;split;first exact:hr.
split;first exact:hRU.
move=>s hs hSR.
pose W:set Y:=[set y|NY y<s /\chi y*delta y<>0].
have hWV:W `<=` V.
  move=>y [hy hNonzero];split.
  - apply:hAU;apply:hRU;exact:le_trans (ltW hy) hSR.
  - apply/eqP=>hZero;apply:hNonzero;by rewrite hZero mulr0.
have hFiniteW:finite_set (@connected_component (real_norm_metric_space hNY) W @` W):=hFinite s hs hSR.
have hFiniteD:=@restricted_finite_components R (real_norm_metric_space hNX) (real_norm_metric_space hNY)
  P Z V W 0 hP hWV (fun y _=>@norm_open_components_open R Y NY hNY V y hVOpen)
  hHomeomorphisms hFibres hFiniteW.
have hEqual:([set x|Z x /\chi (P x)<>0] `&` [set x|NY (P x)<s]) = Z `&` (P @^-1` W).
  apply/seteqP;split.
  - move=>x [[hx hChiX] hSmall];split;first exact:hx.
    split;first exact:hSmall.
    apply/eqP;rewrite mulf_eq0;apply/negP=>/orP [/eqP hZero|hZero].
    + exact:hChiX hZero.
    + exact:(negP (hRange x hx).2) hZero.
  - move=>x [hx [hSmall hNonzero]];split;last exact:hSmall.
    split;first exact:hx.
    move=>hZero;apply:hNonzero;by rewrite hZero mul0r.
by rewrite hEqual.
Qed.
End RestrictedProjection.
