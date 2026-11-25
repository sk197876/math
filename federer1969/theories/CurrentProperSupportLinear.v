(** Federer (1969), 4.1.9, p. 363: the original
    current homotopy algebra preserves the support
    properness required in 4.1.7, p. 359.
    Reuse the compact inverse-image criterion and
    the preceding support inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentProperSupport
  CurrentProperSupportRestriction CurrentSupportLinearUnion FunctionalSupportRelativeClosed SmoothCompactSet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperSupportLinear.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable V:set (R_n R nu).
Variable f:R_n R n->R_n R nu.
Hypothesis hImage:forall x,U x->V (f x).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation Proper := (fun T:C=>@is_current_proper_on_support R h2 n nu m U hU V T f hImage).

(** Source for [current_proper_support_linear]: properness
    of f on spt S and spt T implies properness
    on spt(cS+T), supporting the original current
    homotopy formula in Federer 4.1.9, p. 363.
    The supports need not be compact. *)
Theorem current_proper_support_linear c (S T:C):
  Proper S->Proper T->Proper (c*:S+T).
Proof.
move=>hS hT.
apply:(@current_proper_support_compact_loci R h2 n nu U hU V f hImage m (c*:S+T)).2=>K.
have hCompactS:=@current_proper_support_compact_preimage R h2 n nu m U hU V S f hImage K hS.
have hCompactT:=@current_proper_support_compact_preimage R h2 n nu m U hU V T f hImage K hT.
have [D [hClosed hD]]:=@functional_support_relative_closed R X (A_m X R^o m) NX hNX U
  (@current_test_space R h2 n U hU m) (@current_test_value R h2 n U hU m)
  (@current_value R h2 n U hU m (c*:S+T)).
have hSupportD:support (c*:S+T)=U `&` D:=hD.
have hUnion:=@current_support_linear_union R h2 n m U hU c S T.
have hEqual:[set x|support (c*:S+T) x /\ smooth_compact_carrier K (f x)]=
    ([set x|support S x /\ smooth_compact_carrier K (f x)] `|`
     [set x|support T x /\ smooth_compact_carrier K (f x)]) `&` D.
  apply:funext=>x;apply:propext;split.
  - move=>[hx hKx];split.
    + case:(hUnion x hx)=>[hSx|hTx].
      * left;exact:conj hSx hKx.
      * right;exact:conj hTx hKx.
    + have hUD:(U `&` D) x by rewrite -hSupportD;exact:hx.
      exact:hUD.2.
  - move=>[hLocus hDx].
    have hUx:U x.
      case:hLocus=>[[hx _]|[hx _]];exact:hx.1.
    have hKx:smooth_compact_carrier K (f x).
      case:hLocus=>[[_ hx]|[_ hx]];exact:hx.
    split;last exact:hKx.
    rewrite hSupportD;exact:conj hUx hDx.
rewrite hEqual;exact:compact_closedI (compactU hCompactS hCompactT) hClosed.
Qed.
End CurrentProperSupportLinear.
