(** Federer (1969), 4.1.9, p. 363: smooth forms may be
    localized near a compact time segment and a spatial point.
    Reuse the actual cutoff of 4.1.1, pp. 344–345, and the
    compact-product neighbourhood principle. This is a supporting
    lemma, not an extra compactness assumption on the homotopy. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormBoundedLinearTopology NormDifferentialUP InnerNorm HilbertFormCompactness
  AlternatingForms GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanCartesianMap EuclideanBlockNormTopology TopologicalProductMaps CurrentCoefficientNorms
  CurrentSpaces CurrentCartesianDomain CurrentCartesianCutoff SmoothCompactSet SmoothFunctionSpaceUP
  SmoothTestSpaces SmoothCutoffReplacement CompactProductTube.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianLocalCutoff.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n k:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (m+n))).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (m+n))).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Local Notation ZT := (real_norm_metric_space hNZ).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior NX A a.
Hypothesis hB:forall b,B b->norm_domain_interior NY B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation E := (@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation DT := (@current_test_space R h2 (m+n) AB hAB k).
Local Notation ev := (@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation tv := (@current_test_value R h2 (m+n) AB hAB k).
Local Notation hE := (@current_smooth_space_laws R h2 (m+n) AB hAB k).
Local Notation NF := (@current_form_comass R h2 (m+n) k).
Local Notation hNF := (@current_form_comass_real_norm R h2 (m+n) k).

(** Source for [current_cartesian_local_cutoff_strong]: one
    actual linear compact replacement agrees with every smooth
    form on an open neighbourhood of the original compact time
    set times the point, and along that entire time set on a
    spatial neighbourhood. This supports both the original
    smooth integral and its admissible compact-current replacement
    in Federer 4.1.9, p. 363. *)
Theorem current_cartesian_local_cutoff_strong (K:smooth_compact_set hNX A) b (hb:B b):
  exists (Q:Hom E DT) (W:set Y) (O:set Z),
    @open YT W /\ W b /\ W `<=` B /\ @open ZT O /\
    (forall a,smooth_compact_carrier K a->O (euclidean_block_join (a,b))) /\
    O `<=` AB /\
    (forall phi z,O z->tv (Q phi) z=ev phi z) /\
    forall phi a y,smooth_compact_carrier K a->W y->
      tv (Q phi) (euclidean_block_join (a,y))=ev phi (euclidean_block_join (a,y)).
Proof.
pose L:=@smooth_compact_singleton R Y NY hNY B b hb.
have[C hC]:=@current_cartesian_compact_rectangle R m n A B K L.
pose Q:=@smooth_cutoff_replacement R Z (A_m Z R^o k) NZ NF hNZ hNF (m+n)
  (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) AB hAB E ev hE C.
have[O [hO [hCO [hOAB hAgreement]]]]:=
  @smooth_cutoff_replacement_agrees_near_compact R Z (A_m Z R^o k) NZ NF hNZ hNF (m+n)
    (@coordinate_basis R (m+n)) (@coordinate_basisP R (m+n)) AB hAB E ev hE C.
pose J (p:YT*XT):ZT:=euclidean_block_join (p.2,p.1).
have hSwap:continuous (fun p:YT*XT=>(p.2,p.1):(XT*YT)%type).
  exact:(topological_pair_continuous (@second_projection_continuous YT XT)
    (@first_projection_continuous YT XT)).
have hJ:continuous J.
  move=>p;exact:(continuous_comp (@hSwap p)
    (@euclidean_block_join_norm_continuous R m n (p.2,p.1))).
have hPre:@open [the topologicalType of (YT*XT)%type] (J @^-1` O).
  exact:((@continuousP [the topologicalType of (YT*XT)%type] ZT J).1 hJ O hO).
have hAt a:smooth_compact_carrier K a->(J @^-1` O) (b,a).
  move=>ha;apply:hCO.
  change (smooth_compact_carrier C (euclidean_block_join (a,b))).
  rewrite hC.
  change (and (smooth_compact_carrier K (@euclidean_block_split R m n
      (euclidean_block_join (a,b))).1)
    (smooth_compact_carrier L (@euclidean_block_split R m n
      (euclidean_block_join (a,b))).2)).
  rewrite euclidean_block_joinK;by split=>//.
have[W [V [hW [hWb [hV [hKV hWV]]]]]]:=
  @compact_product_open_tube YT XT b (smooth_compact_carrier K) (J @^-1` O)
    (smooth_compact_is_compact K) hPre hAt.
have hOpenB:@open YT B.
  rewrite openE=>y hy.
  exact:((@norm_domain_interior_neighbourhood R Y NY hNY B y).1 (@hB y hy)).
exists Q,(W `&` B),O;split;first exact:openI hW hOpenB.
split;first by split.
split;first by move=>y [_ hy].
split;first exact:hO.
split;first by move=>a ha;exact:(@hAt a ha).
split;first exact:hOAB.
split;first exact:hAgreement.
move=>phi a y ha [hy _].
apply:hAgreement.
exact:(hWV (y,a) (conj hy (hKV a ha))).
Qed.

(** Source for [current_cartesian_local_cutoff]: one actual
    linear compact replacement agrees with every smooth form
    along the whole compact first factor and a neighbourhood
    of the given second-factor point, supporting the smooth
    form homotopy operator in Federer 4.1.9, p. 363.
    No compact support of the original smooth form is required. *)
Theorem current_cartesian_local_cutoff (K:smooth_compact_set hNX A) b (hb:B b):
  exists (Q:Hom E DT) (W:set Y),
    @open YT W /\ W b /\ W `<=` B /\
    forall phi a y,smooth_compact_carrier K a->W y->
      tv (Q phi) (euclidean_block_join (a,y))=ev phi (euclidean_block_join (a,y)).
Proof.
have[Q [W [O [hW [hWb [hWB [hO [hKO [hOAB [hAgreement hStrip]]]]]]]]]]:=
  @current_cartesian_local_cutoff_strong K b hb.
exists Q,W;by split=>//;split=>//;split.
Qed.
End CurrentCartesianLocalCutoff.
