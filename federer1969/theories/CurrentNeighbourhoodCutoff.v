(** Federer (1969), 4.1.12, p. 368: choose
    a compact scalar test with support in a prescribed
    open neighbourhood and value one near a compact set.
    Reuse 4.1.7's actual cutoff on the smaller open
    domain and 4.1.1's exact test zero extension. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormOpenTopology NormBoundedLinearTopology NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  SmoothCompactSet SmoothTestSpaces CurrentSupportGeometry CurrentScalarCutoffs CurrentOpenRestriction
  CurrentOpenTestSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentNeighbourhoodCutoff.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.

(** Source for [current_neighbourhood_scalar_cutoff]:
    the cutoff in Federer 4.1.12, p. 368,
    has its entire original test support in W
    and is one on an open neighbourhood V of K.
    Empty compact sets and arbitrary open domains
    are included; no positive-dimensional premise is used. *)
Theorem current_neighbourhood_scalar_cutoff (K:smooth_compact_set hNX U) (W:set X):
  @open XT W->smooth_compact_carrier K `<=` W->W `<=` U->
  exists gamma:@current_test_space R h2 n U hU 0%N,
    @current_test_support R h2 n 0%N U hU gamma `<=` W /\
    exists V:set X,@open XT V /\ smooth_compact_carrier K `<=` V /\ V `<=` W /\
      forall x,V x->@current_test_value R h2 n U hU 0%N gamma x=@zero_form R X R^o 1.
Proof.
move=>hW hKW hWU.
have hWi:forall x,W x->norm_domain_interior NX W x.
  move=>x hx;apply:(@norm_domain_interior_neighbourhood R X NX hNX W x).2.
  exact:(@open_nbhs_nbhs XT x W (conj hW hx)).
pose KW:=@Build_smooth_compact_set R X NX hNX W (smooth_compact_carrier K)
  hKW (smooth_compact_is_compact K).
have [gamma [V [hV [hKV [hVW hOne]]]]]:=@current_compact_scalar_cutoff R h2 n W hWi KW.
pose P:=@current_open_test_extension R h2 n 0%N W U hWi hU hWU.
exists (P gamma);split.
- rewrite (@current_open_test_extension_support R h2 n 0%N W U hWi hU hWU gamma).
  by move=>x hx;exact:hx.1.
- exists V;split;first exact:hV.
  split;first exact:hKV.
  split;first exact:hVW.
  move=>x hx;rewrite (@current_open_test_extension_values R h2 n 0%N W U hWi hU hWU gamma x).
  exact:hOne x hx.
Qed.
End CurrentNeighbourhoodCutoff.
