(** Federer (1969), 4.1.9, p. 363: properness on
    the original closed cylinder implies properness
    on the product current's support. This supporting
    adapter uses the preceding compact-preimage criterion
    and relative closedness of actual current supports. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentDomain
  CurrentProperSupport CurrentProperSupportRestriction SmoothCompactSet
  ProperMapUP IsotropyGroupTopology FunctionalSupportRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperOnContainingSet.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y) (C:set X).
Hypothesis hCU:C `<=` U.
Arguments hCU : clear implicits.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.

(** Source for [current_map_on_containing_set]: the original
    map restricted to a specified set containing a
    current support, supporting the closed-cylinder
    properness in Federer 4.1.9, p. 363. Only
    the relative carriers change; the function values do not. *)
Definition current_map_on_containing_set:
    [the topologicalType of set_type (C:set XT)]->current_domain R nu V:=
  fun x=>exist _ (f (set_val x)) (mem_set (hImage (set_val x) (hCU _ (set_valP x)))).

(** Source for [current_containing_proper_compact_preimage]:
    properness on the stated containing set gives
    its exact compact inverse images, supporting the
    hypothesis in Federer 4.1.9, p. 363. No
    properness on the whole open domain is assumed. *)
Theorem current_containing_proper_compact_preimage
    (hProper:is_proper_map current_map_on_containing_set) (K:smooth_compact_set hNY V):
  @compact XT [set x|C x /\ smooth_compact_carrier K (f x)].
Proof.
pose CT:topologicalType:=[the topologicalType of set_type (C:set XT)].
pose VT:=current_domain R nu V.
have hK:@compact VT (set_val @^-1` smooth_compact_carrier K).
  exact:(@set_type_compact_preimage YT V (smooth_compact_carrier K)
    (smooth_compact_is_compact K) (smooth_compact_in_domain K)).
have hPre:=hProper (set_val @^-1` smooth_compact_carrier K) hK.
have hCompact:@compact XT
    (set_val @` (current_map_on_containing_set @^-1` (set_val @^-1` smooth_compact_carrier K))).
  apply:continuous_compact hPre.
  exact:continuous_subspaceT (@set_type_val_continuous XT C).
have hEqual:set_val @` (current_map_on_containing_set @^-1`
      (set_val @^-1` smooth_compact_carrier K))=
    [set x:XT|C x /\ smooth_compact_carrier K (f x)].
  apply:funext=>x;apply:propext;split.
  - move=>[z hz <-];split;first exact:set_valP z.
    exact:hz.
  - move=>[hx hKx];exists (exist _ x (mem_set hx));by [].
by rewrite hEqual in hCompact.
Qed.

(** Source for [current_proper_on_containing_set]: properness
    on a specified subset of U implies properness
    on every actual current support contained in it,
    supporting the original cylinder hypothesis in
    Federer 4.1.9, p. 363, by 4.1.7,
    p. 359. Relative closedness is proved, not assumed. *)
Theorem current_proper_on_containing_set (h2:(1+1:R)!=0) m
    (hU:forall x,U x->norm_domain_interior NX U x)
    (T:@current_space R h2 n U hU m):
  (@current_support R h2 n U hU m T `<=` C)->
  is_proper_map current_map_on_containing_set->
  @is_current_proper_on_support R h2 n nu m U hU V T f hImage.
Proof.
move=>hSupport hProper.
apply:(@current_proper_support_compact_loci R h2 n nu U hU V f hImage m T).2=>K.
have[D [hClosed hD]]:=@functional_support_relative_closed R X (A_m X R^o m) NX hNX U
  (@current_test_space R h2 n U hU m) (@current_test_value R h2 n U hU m)
  (@current_value R h2 n U hU m T).
have hSupportD:@current_support R h2 n U hU m T=U `&` D:=hD.
have hCompact:=@current_containing_proper_compact_preimage hProper K.
have hEqual:[set x|@current_support R h2 n U hU m T x /\ smooth_compact_carrier K (f x)]=
    [set x|C x /\ smooth_compact_carrier K (f x)] `&` D.
  apply:funext=>x;apply:propext;split.
  - move=>[hx hKx];split;first exact:conj (hSupport x hx) hKx.
    have hUD:(U `&` D) x by rewrite -hSupportD;exact:hx.
    exact:hUD.2.
  - move=>[[hx hKx] hDx];split;last exact:hKx.
    rewrite hSupportD;exact:conj (hCU x hx) hDx.
rewrite hEqual;exact:compact_closedI hCompact hClosed.
Qed.
End CurrentProperOnContainingSet.
