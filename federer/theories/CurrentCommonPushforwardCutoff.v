(** Federer (1969), 4.1.9, p. 363: linearity of
    the original support-proper pushforward uses one
    compact cutoff for both current supports. Reuse
    the actual compact inverse images and scalar
    cutoff of 4.1.7, pp. 358–359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero CurrentSpaces
  CurrentSupportGeometry CurrentProperSupport CurrentScalarCutoffs SmoothCompactSet
  SmoothTestSpaces SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCommonPushforwardCutoff.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation XT := (real_norm_metric_space hNX).
Variables (U:set X) (V:set Y).
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable f:X->Y.
Hypothesis hImage:forall x,U x->V (f x).
Local Notation C := (@current_space R h2 n U hU m).
Local Notation support := (@current_support R h2 n U hU m).
Local Notation DV := (@current_test_space R h2 nu V hV m).
Local Notation D0 := (@current_test_space R h2 n U hU 0%N).
Local Notation scalar := (@current_test_value R h2 n U hU 0%N).
Local Notation Proper := (fun T:C=>@is_current_proper_on_support R h2 n nu m U hU V T f hImage).

(** Source for [current_common_pushforward_cutoff]: every
    target test has a common admissible compact scalar
    cutoff for two original support-proper currents,
    supporting the homotopy formula in Federer
    4.1.9, p. 363, through 4.1.7, p. 359.
    Properness on the whole source is unnecessary. *)
Theorem current_common_pushforward_cutoff (S T:C):
  Proper S->Proper T->forall phi:DV,
  exists gamma:D0,forall x,(support S x \/ support T x)->
    @current_test_support R h2 nu m V hV phi (f x)->
    @interior XT [set z|scalar gamma z=@zero_form R X R^o 1] x.
Proof.
move=>hS hT phi.
pose K:=@Build_smooth_compact_set R Y NY hNY V
  (@current_test_support R h2 nu m V hV phi) (fun y hy=>hy.1)
  (smooth_test_support_compact (@current_smooth_space_laws R h2 nu V hV m) phi).
pose KS:=@current_proper_support_compact_locus R h2 n nu m U hU V S f hImage hS K.
pose KT:=@current_proper_support_compact_locus R h2 n nu m U hU V T f hImage hT K.
pose L:=smooth_compact_union KS KT.
have[gamma [W [hW [hLW [hWU hOne]]]]]:=@current_compact_scalar_cutoff R h2 n U hU L.
exists gamma=>x hx hPhi.
have hWx:W x.
  apply:hLW;case:hx=>[hSx|hTx].
  - left;exact:conj hSx hPhi.
  - right;exact:conj hTx hPhi.
have hNeighbourhood:@nbhs _ XT x W:=@open_nbhs_nbhs XT x W (conj hW hWx).
change (@nbhs _ XT x [set z|scalar gamma z=@zero_form R X R^o 1]).
exact:(filterS (fun z hz=>hOne z hz) hNeighbourhood).
Qed.
End CurrentCommonPushforwardCutoff.
