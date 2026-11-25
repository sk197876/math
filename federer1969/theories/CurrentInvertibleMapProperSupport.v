(** Federer (1969), 4.1.8, p. 361: the canonical
    coordinate interchanges and reassociations are proper
    on every original current support. This supporting
    lemma reuses relative support closedness and the
    original compact-image and inverse laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormClassOneUP NormClassZeroTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentDomain CurrentSpaces
  CurrentProperSupport CurrentProperSupportRestriction SmoothCompactSet IsotropyGroupTopology
  FunctionalSupportRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentInvertibleMapProperSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n m:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable T:@current_space R h2 v U hU m.
Variables (f:X->Y) (g:Y->X).
Hypothesis hImage:forall x,U x->V (f x).
Hypothesis hBack:forall y,V y->U (g y).
Hypothesis hGF:forall x,U x->g (f x)=x.
Hypothesis hFG:forall y,V y->f (g y)=y.
Hypothesis hG:norm_class_zero NY NX V g.

(** Source for [current_invertible_map_proper_on_support]:
    a map with a continuous inverse on the original
    domains is proper on each actual current support,
    supporting the canonical product coordinate identifications
    in Federer 4.1.8, p. 361. Relative closedness
    of the support is proved from its original definition. *)
Theorem current_invertible_map_proper_on_support:
  @is_current_proper_on_support R h2 v n m U hU V T f hImage.
Proof.
apply:(@current_proper_support_compact_loci R h2 v n U hU V f hImage m T).2=>K.
pose VT:=current_domain R n V.
have hK:@compact VT (set_val @^-1` smooth_compact_carrier K).
  exact:(@set_type_compact_preimage YT V (smooth_compact_carrier K)
    (smooth_compact_is_compact K) (smooth_compact_in_domain K)).
have hGC:continuous (fun y:VT=>(g (set_val y):XT)).
  exact:(@norm_class_zero_restriction_continuous R Y X NY NX hNY hNX V g hG).
have hImageCompact:@compact XT ((fun y:VT=>g (set_val y)) @`
    (set_val @^-1` smooth_compact_carrier K)).
  apply:continuous_compact hK;exact:continuous_subspaceT hGC.
have hImageEqual:((fun y:VT=>g (set_val y)) @`
    (set_val @^-1` smooth_compact_carrier K))=g @` smooth_compact_carrier K.
  apply:funext=>x;apply:propext;split.
  - move=>[y hy <-];by exists (set_val y).
  - move=>[y hy <-];exists (exist _ y (mem_set (smooth_compact_in_domain K y hy)));by [].
rewrite hImageEqual in hImageCompact.
have[C [hClosed hSupport]]:=@functional_support_relative_closed R X (A_m X R^o m) NX hNX U
  (@current_test_space R h2 v U hU m) (@current_test_value R h2 v U hU m)
  (@current_value R h2 v U hU m T).
have hCurrentSupport:@current_support R h2 v U hU m T=U `&` C:=hSupport.
have hEqual:[set x|@current_support R h2 v U hU m T x /\smooth_compact_carrier K (f x)]=
    (g @` smooth_compact_carrier K) `&` C.
  apply:funext=>x;apply:propext;split.
  - move=>[hx hKx];split.
    + exists (f x);first exact:hKx.
      exact:@hGF x hx.1.
    + have hSC:(U `&` C) x by rewrite -hCurrentSupport;exact:hx.
      exact:hSC.2.
  - move=>[[y hy hxy] hCx].
    have hVy:V y:=smooth_compact_in_domain K y hy.
    have hUx:U x.
      rewrite -hxy;exact:@hBack y hVy.
    split.
    + rewrite hCurrentSupport;exact:conj hUx hCx.
    + rewrite -hxy (@hFG y hVy);exact:hy.
rewrite hEqual;exact:compact_closedI hImageCompact hClosed.
Qed.
End CurrentInvertibleMapProperSupport.
