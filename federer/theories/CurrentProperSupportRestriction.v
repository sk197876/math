(** Federer (1969), 4.1.7, p. 359:
    properness on spt T passes
    to the support of every
    current with smaller support, including
    its boundary and contractions. This
    supporting statement reuses compact preimages
    and the original relative closedness
    of functional supports. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  CurrentDomain CurrentProperSupport SmoothCompactSet IsotropyGroupTopology
  FunctionalSupportRelativeClosed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperSupportRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X := (R_n R v).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R v)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Local Notation YT := (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable V:set Y.
Local Notation VT := (current_domain R n V).
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Arguments hImage : clear implicits.

(** Source for [current_proper_support_compact_loci]:
    the original properness hypothesis is
    equivalent to compactness of spt T
    intersect f inverse(K) for every
    compact K in V, supporting
    Federer 4.1.7, p. 359.
    Both directions use the actual
    relative support and target spaces. *)
Theorem current_proper_support_compact_loci m (T:@current_space R h2 v U hU m):
  @is_current_proper_on_support R h2 v n m U hU V T f hImage <->
  forall K:smooth_compact_set hNY V,@compact XT
    [set x|@current_support R h2 v U hU m T x /\smooth_compact_carrier K (f x)].
Proof.
split.
- move=>hProper K;exact:(@current_proper_support_compact_preimage R h2 v n m U hU V T f hImage K hProper).
- move=>hLoci K hK.
  pose support:=@current_support R h2 v U hU m T.
  pose ST:topologicalType:=[the topologicalType of set_type (support:set XT)].
  pose C:set Y:=set_val @` K.
  have hC:@compact YT C.
    apply:continuous_compact hK;exact:continuous_subspaceT (@set_type_val_continuous YT V).
  have hCV:C `<=` V by move=>y [z _ <-];exact:set_valP z.
  pose CK:=@Build_smooth_compact_set R Y
    (inner_norm (@euclidean_inner_productP R n)) hNY V C hCV hC.
  pose A:=[set x|support x /\C (f x)].
  have hA:@compact XT A:=hLoci CK.
  have hAS:A `<=` support by move=>x hx;exact:hx.1.
  have hPre:@compact ST (set_val @^-1` A):=@set_type_compact_preimage XT support A hA hAS.
  have hEqual:((@current_map_on_support R h2 v n m U hU V T f hImage) @^-1` K)=
      (set_val @^-1` A:set ST).
    apply:funext=>x;apply:propext;split.
    * move=>hx;split;first exact:set_valP x.
      exists (@current_map_on_support R h2 v n m U hU V T f hImage x);by [].
    * move=>[_ [z hz hzx]].
      have hSame:z=@current_map_on_support R h2 v n m U hU V T f hImage x.
        apply:val_inj;exact:hzx.
      exact (eq_ind z K hz _ hSame).
  by rewrite hEqual.
Qed.

(** Source for [current_proper_smaller_support]:
    f is proper on every
    smaller original current support, supporting
    boundary, projection and composition in
    Federer 4.1.7, p. 359.
    Relative closedness is proved from
    the support definition, not assumed. *)
Theorem current_proper_smaller_support m k
    (T:@current_space R h2 v U hU m) (S:@current_space R h2 v U hU k):
  (@current_support R h2 v U hU k S `<=` @current_support R h2 v U hU m T)->
  @is_current_proper_on_support R h2 v n m U hU V T f hImage->
  @is_current_proper_on_support R h2 v n k U hU V S f hImage.
Proof.
move=>hST hProper;apply:(current_proper_support_compact_loci S).2=>K.
have [C [hClosed hSupport]]:=@functional_support_relative_closed R X (A_m X R^o k) NX hNX U
  (@current_test_space R h2 v U hU k) (@current_test_value R h2 v U hU k)
  (@current_value R h2 v U hU k S).
have hSourceSupport:@current_support R h2 v U hU k S=U `&` C:=hSupport.
have hCompact:=@current_proper_support_compact_preimage R h2 v n m U hU V T f hImage K hProper.
have hEqual:[set x|@current_support R h2 v U hU k S x /\smooth_compact_carrier K (f x)]=
    [set x|@current_support R h2 v U hU m T x /\smooth_compact_carrier K (f x)] `&` C.
  apply:funext=>x;apply:propext;split.
  - move=>[hx hKx];split;first exact:conj (hST x hx) hKx.
    have hSC:(U `&` C) x by rewrite -hSourceSupport;exact:hx.
    exact:hSC.2.
  - move=>[[hx hKx] hCx];split;last exact:hKx.
    rewrite hSourceSupport;exact:conj hx.1 hCx.
rewrite hEqual;exact:compact_closedI hCompact hClosed.
Qed.
End CurrentProperSupportRestriction.
