(** Federer (1969), 4.1.24, p. 381: the
    three original local integer-current classes form
    additive groups and retain the localized inclusion
    arrows. Their literal germ condition also gives
    the already defined original local flatness through
    4.1.12's point criterion. No common compact or
    finite global mass is added. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom TopologicalGroupUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces FlatCurrentsUP LocallyFlatPointCriterion
  RectifiableCurrentApproximationUP RectifiableCurrentBasic IntegralCurrentClassesUP
  IntegralCurrentInclusions IntegralCurrentUnionGroups CurrentGermLocalGroup.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section IntegralCurrentLocalClasses.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Rect:=(@is_rectifiable_current R h2 n U hU m).
Local Notation Int:=(@is_integral_current R h2 n U hU m).
Local Notation IF:=(@is_integral_flat_current R h2 n U hU m).
Local Notation LocalRect:=(@is_locally_rectifiable_current R h2 n U hU m).
Local Notation LocalInt:=(@is_locally_integral_current R h2 n U hU m).
Local Notation LocalIF:=(@is_locally_integral_flat_current R h2 n U hU m).

(** Source for [locally_rectifiable_current_subgroup]: the original
    local rectifiable class is an additive group,
    4.1.24, p. 381. *)
Theorem locally_rectifiable_current_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 LocalRect.
Proof.
exact:(@germ_localised_current_class_subgroup R h2 n m U hU Rect
  (@rectifiable_current_union_subgroup R h2 n m U hU)).
Qed.

(** Source for [locally_integral_current_subgroup]: the original
    local integral class is an additive group,
    4.1.24, p. 381, including degree zero. *)
Theorem locally_integral_current_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 LocalInt.
Proof.
exact:(@germ_localised_current_class_subgroup R h2 n m U hU Int
  (@integral_current_union_subgroup R h2 n m U hU)).
Qed.

(** Source for [locally_integral_flat_current_subgroup]: the original
    local integral-flat class is an additive group,
    4.1.24, p. 381, without total mass assumptions. *)
Theorem locally_integral_flat_current_subgroup:
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 LocalIF.
Proof.
exact:(@germ_localised_current_class_subgroup R h2 n m U hU IF
  (@integral_flat_current_union_subgroup R h2 n m U hU)).
Qed.

(** Source for [global_rectifiable_current_is_local]: global
    rectifiable membership implies its literal local class,
    4.1.24, p. 381. *)
Theorem global_rectifiable_current_is_local (T:C):Rect T->LocalRect T.
Proof. exact:(@current_class_is_germ_localised R h2 n m U hU Rect T). Qed.

(** Source for [global_integral_current_is_local]: the original
    global-to-local integral inclusion, 4.1.24, p. 381. *)
Theorem global_integral_current_is_local (T:C):Int T->LocalInt T.
Proof. exact:(@current_class_is_germ_localised R h2 n m U hU Int T). Qed.

(** Source for [global_integral_flat_current_is_local]: the original
    global integral-flat group lies in its literal
    local class, 4.1.24, p. 381. *)
Theorem global_integral_flat_current_is_local (T:C):IF T->LocalIF T.
Proof. exact:(@current_class_is_germ_localised R h2 n m U hU IF T). Qed.

(** Source for [locally_integral_current_is_rectifiable]: localize
    the original integral-to-rectifiable arrow with the
    same germ representatives, 4.1.24, p. 381. *)
Theorem locally_integral_current_is_rectifiable (T:C):LocalInt T->LocalRect T.
Proof.
apply:(@germ_localised_current_class_monotone R h2 n m U hU Int Rect).
move=>S [K hS];exists K;exact:integral_current_is_rectifiable_supported hS.
Qed.

(** Source for [locally_rectifiable_current_is_integral_flat]: the
    original local rectifiable-to-integral-flat inclusion,
    with unchanged representatives, 4.1.24, p. 381. *)
Theorem locally_rectifiable_current_is_integral_flat (T:C):LocalRect T->LocalIF T.
Proof.
apply:(@germ_localised_current_class_monotone R h2 n m U hU Rect IF).
move=>S [K hS];exists K;exact:rectifiable_current_is_integral_flat_supported hS.
Qed.

(** Source for [locally_integral_flat_current_is_locally_flat]:
    the original local integral-flat class lies in
    Federer's already defined local flat space, 4.1.24,
    p. 381. The earlier point criterion proves
    actual compact scalar-test flatness, not just a
    restated germ property. *)
Theorem locally_integral_flat_current_is_locally_flat (T:C):
  LocalIF T->@is_locally_flat_current R h2 n m U hU T.
Proof.
move=>hT;apply:(@locally_flat_point_criterion R h2 n m U hU T).2.
move=>x hx;have[S [[K hS] hOutside]]:=hT x hx.
exists S;split;last exact:hOutside.
exists K;exact:integral_flat_current_is_flat_supported hS.
Qed.
End IntegralCurrentLocalClasses.
