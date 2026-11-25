(** Federer (1969), 4.1.9, p. 363: the original
    current homotopy formula uses linear combinations
    under support-proper pushforward. This supporting
    support inclusion follows from the original local
    annihilation definition of 4.1.1, p. 344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces
  CurrentSupportGeometry FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentSupportLinearUnion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation value := (@current_test_value R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).
Local Notation support := (@current_support R h2 n U hU m).

(** Source for [current_support_linear_union]: the support
    of cS+T lies in spt S union spt T,
    supporting the original homotopy algebra in
    Federer 4.1.9, p. 363. No compactness,
    positivity or measure representation is required. *)
Theorem current_support_linear_union c (S T:C):
  support (c*:S+T) `<=` (support S `|` support T).
Proof.
move=>x [hx hNot];apply:contrapT=>hNeither.
have hNoS:~support S x by move=>hS;apply:hNeither;left;exact:hS.
have hNoT:~support T x by move=>hT;apply:hNeither;right;exact:hT.
have [W [[hW hZeroS] hxW]]:exists W,
    smooth_functional_annihilation_open hNX U value (action S) W /\ W x.
  apply:contrapT=>hNone;apply:hNoS;exact:conj hx hNone.
have [Z [[hZ hZeroT] hxZ]]:exists Z,
    smooth_functional_annihilation_open hNX U value (action T) Z /\ Z x.
  apply:contrapT=>hNone;apply:hNoT;exact:conj hx hNone.
apply:hNot;exists (W `&` Z);split;last exact:conj hxW hxZ.
split;first exact:openI hW hZ.
move=>phi hPhi.
have hS:=hZeroS phi (fun y hy=>(hPhi y hy).1).
have hT:=hZeroT phi (fun y hy=>(hPhi y hy).2).
by rewrite (linearP action) hom_addE hom_scaleE hS hT scaler0 addr0.
Qed.
End CurrentSupportLinearUnion.
