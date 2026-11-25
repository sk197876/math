(** Federer (1969), 3.4.10, p. 337:
    a zero-dimensional analytic set is regular
    at each of its actual points.
    The exceptional family has only empty germs;
    the printed negative-degree expression is unnecessary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermOrder
  SetGermBoundary SetGermCentreMember FiniteSetGermUnionOrder AnalyticVarietyGermUP
  GermVanishingSealed AnalyticDepthSealed AnalyticRegularLocusUP AnalyticOriginSingularExceptions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_origin_zero_regular]: the
    zero-dimensional endpoint of the regular-part
    assertion in 3.4.10, p. 337.
    The proved exceptional family is empty
    as a germ; an actual nonregular
    centre would give a nonempty contained germ. *)
Theorem analytic_origin_zero_regular (R:realType) n (U S L:set (R_n R n)):
  let hB:=@euclidean_inner_productP R n in
  let NX:=inner_norm hB in
  let hNX:=inner_norm_real_norm hB in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @open T U ->U 0 ->
  @is_analytic_variety_germ R (R_n R n) NX hNX 0 (@set_germ T 0 S) ->
  (@AnalyticDepth.value R (R_n R n) (@euclidean_inner_product R n) hB n
    (@coordinate_basis R n) (@coordinate_basisP R n) (dual_basis (@coordinate_basisP R n))
    (@AnalyticSetIdeal.value R (R_n R n) NX hNX 0%R (@set_germ T 0%R S))<=0)%N ->
  @is_analytic_regular_locus R n 0 U S L ->S 0 ->L 0.
Proof.
move=>hB NX hNX T hU hU0 hS hDepth hL hS0.
have [J [W [A [nu [hW [hW0 [hWU [hCover hNu]]]]]]]]:=
  @analytic_origin_singular_exceptions R n U S L 0 hU hU0 hS hDepth hL.
have hEmpty j:nu j=@set_germ T 0 set0.
  case:(hNu j).2.2=>h;first exact:h.
  by rewrite ltn0 in h.
have hAEmpty j:@set_germ T 0 (A j)=@set_germ T 0 set0.
  apply:set_germ_subset_empty;rewrite -(hEmpty j);exact:(hNu j).2.1.
have hUnion:=@finite_set_germ_empty_union T 0 J A hAEmpty.
have hSub:set_germ_subset (@set_germ T 0 (S `\` L)) (@set_germ T 0 (\bigcup_j A j)).
  apply/set_germ_subset_original;exists W;split;first exact:hW.
  split;first exact:hW0.
  move=>x hx hxW;exact:hCover x (conj hx hxW).
rewrite hUnion in hSub.
have hSingularEmpty:=set_germ_subset_empty hSub.
apply:contrapT=>hNot.
exact:(@set_germ_centre_member_nonempty T 0 (S `\` L) (conj hS0 hNot) hSingularEmpty).
Qed.
