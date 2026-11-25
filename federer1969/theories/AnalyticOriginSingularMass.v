(** Federer (1969), 3.4.10, p. 337:
    the nonregular part has locally finite H^(m-1)
    mass when m is positive. Its actual
    finite exceptional family is already constructed;
    compact germ representatives provide the mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  SetGermUP SetGermOrder AnalyticVarietyGermUP GermVanishingSealed AnalyticDepthSealed
  AnalyticRegularLocusUP AnalyticOriginSingularExceptions AnalyticGermCompactDomination
  FiniteGermLocalMass HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SingularMass.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation E:=(inner_metric_space hB).
Local Notation germ:=(@set_germ T 0).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  hB n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).

(** Source for [analytic_origin_singular_positive_mass]: the
    local positive-dimensional singular-part mass bound
    underlying 3.4.10, p. 337. All
    compact dominating sets are obtained internally
    from the proved smaller-dimensional analytic germs;
    no finite-mass conclusion is assumed. *)
Theorem analytic_origin_singular_positive_mass (U S L:set X) u:
  @open T U ->U 0 ->
  @is_analytic_variety_germ R X NX hNX 0 (germ S) ->
  (depth (ideal (germ S))<=u.+1)%N ->
  @is_analytic_regular_locus R n u.+1 U S L ->
  exists W:set X,@open T W /\W 0 /\W `<=` U /\
    (@hausdorff_measure R E u ((S `\` L) `&` W)< +oo)%E.
Proof.
move=>hU hU0 hS hDepth hL.
have [J [V [A [nu [hV [hV0 [hVU [hCover hNu]]]]]]]]:=
  @analytic_origin_singular_exceptions R n U S L u.+1 hU hU0 hS hDepth hL.
have hEach j:exists K:set X,@compact E K /\
    set_germ_subset (germ (A j)) (germ K) /\(@hausdorff_measure R E u K< +oo)%E.
  apply:(@analytic_germ_compact_domination R n (A j) u (nu j) (hNu j).1 (hNu j).2.1).
  case:(hNu j).2.2=>hDimension;first by left.
  right;by move:hDimension;rewrite ltnS.
have [K hK]:=choice hEach.
have [O [hO [hO0 hMass]]]:=@finite_germ_local_mass R T J 0
  (@hausdorff_measure R E u) A K (@hausdorff_measure_is_measure R E u)
  (fun j=>(hK j).2.1) (fun j=>(hK j).2.2).
exists (V `&` O);split;first exact:openI hV hO.
split;first by split.
split;first by move=>x hx;exact:hVU x hx.1.
apply:(le_lt_trans (@measure_mono R E (@hausdorff_measure R E u)
  (@hausdorff_measure_is_measure R E u) ((S `\` L) `&` (V `&` O))
  ((\bigcup_j A j) `&` O) _) hMass).
move=>x [hx [hxV hxO]];split;last exact:hxO.
exact:hCover x (conj hx hxV).
Qed.
End SingularMass.
