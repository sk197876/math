(** Federer (1969), 4.1.9, p. 363: characterize
    the original cylinder properness by its exact
    compact inverse images. This supporting adapter
    uses the preceding subspace compactness laws
    from 2.2.17, p. 72, without a closedness
    assumption on the containing set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentDomain CurrentProperOnContainingSet
  SmoothCompactSet ProperMapUP IsotropyGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentProperContainingCriterion.
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
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Local Notation mapC := (@current_map_on_containing_set R n nu U V C hCU f hImage).

(** Source for [current_containing_proper_compact_loci]:
    the exact compact-preimage criterion for the
    original containing-set restriction, supporting
    cylinder and boundary properness in Federer
    4.1.9, p. 363. Every compact target set
    is retained, with no compactness premise on C. *)
Theorem current_containing_proper_compact_loci:
  is_proper_map mapC <->
  forall K:smooth_compact_set hNY V,@compact XT
    [set x|C x /\ smooth_compact_carrier K (f x)].
Proof.
split.
- move=>hProper K.
  exact:(@current_containing_proper_compact_preimage R n nu U V C hCU f hImage hProper K).
- move=>hLoci K hK.
  pose CT:topologicalType:=[the topologicalType of set_type (C:set XT)].
  pose VT:=current_domain R nu V.
  pose D:set Y:=set_val @` K.
  have hD:@compact YT D.
    apply:continuous_compact hK;exact:continuous_subspaceT (@set_type_val_continuous YT V).
  have hDV:D `<=` V by move=>y [z _ <-];exact:set_valP z.
  pose DK:=@Build_smooth_compact_set R Y
    (inner_norm (@euclidean_inner_productP R nu)) hNY V D hDV hD.
  pose E:set X:=[set x|C x /\ D (f x)].
  have hE:@compact XT E:=hLoci DK.
  have hEC:E `<=` C by move=>x hx;exact:hx.1.
  have hPre:@compact CT (set_val @^-1` E):=@set_type_compact_preimage XT C E hE hEC.
  have hEqual:(mapC @^-1` K)=(set_val @^-1` E:set CT).
    apply:funext=>x;apply:propext;split.
    + move=>hx;split;first exact:set_valP x.
      exists (mapC x);by [].
    + move=>[_ [z hz hzx]].
      have hSame:z=mapC x by apply:val_inj;exact:hzx.
      exact:(eq_ind z K hz (mapC x) hSame).
  by rewrite hEqual.
Qed.
End CurrentProperContainingCriterion.
