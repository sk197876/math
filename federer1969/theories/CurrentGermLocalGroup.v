(** Federer (1969), 4.1.24, p. 381: localize
    the original additive current groups by agreement
    outside the support of their difference. The
    local class is again an additive group, using
    the already proved support union law. No global
    compact support, mass bound or real scalar closure
    is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom TopologicalGroupUP RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentSupportGeometry CurrentSupportLinearUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentGermLocalGroup.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation support:=(@current_support R h2 n U hU m).
Local Notation Empty:=(@smooth_compact_empty R X NX hNX U).

(** Source for [is_germ_localised_current_class]: the literal
    original local agreement condition, parameterized by
    its prescribed global current class, 4.1.24, p. 381. *)
Definition is_germ_localised_current_class (A:set C) (T:C):Prop:=
  forall x,U x->exists S:C,A S /\~support (T-S) x.

(** Source for [current_zero_has_empty_support]: the original
    zero support law used to localize all the
    groups in 4.1.24, p. 381. *)
Lemma current_zero_has_empty_support:support (0:C) `<=` set0.
Proof. exact:(@current_support_zero_subset R h2 n m U hU Empty). Qed.

(** Source for [current_class_is_germ_localised]: each original
    global representative is its own local representative,
    with zero difference, 4.1.24, p. 381. *)
Theorem current_class_is_germ_localised (A:set C) (T:C):
  A T->is_germ_localised_current_class A T.
Proof.
move=>hT x hx;exists T;split;first exact:hT.
rewrite subrr;exact:current_zero_has_empty_support.
Qed.

(** Source for [germ_localised_current_class_monotone]: any
    original inclusion of the global classes localizes
    with exactly the same representatives, 4.1.24, p. 381. *)
Theorem germ_localised_current_class_monotone (A B:set C):
  A `<=` B->is_germ_localised_current_class A `<=` is_germ_localised_current_class B.
Proof.
move=>hAB T hT x hx;have[S [hS hOutside]]:=hT x hx.
exists S;split;[exact:hAB S hS|exact:hOutside].
Qed.

(** Source for [germ_localised_current_class_subgroup]: the
    original pointwise local agreement construction preserves
    additive subgroups, as used for the three
    local groups of 4.1.24, p. 381. *)
Theorem germ_localised_current_class_subgroup (A:set C):
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 A->
  is_subgroup (fun T S:C=>T+S) (fun T=>-T) 0 (is_germ_localised_current_class A).
Proof.
move=>hA;constructor.
- apply:current_class_is_germ_localised;exact:subgroup_unit hA.
- move=>T S hT hS x hx.
  have[P [hP hTP]]:=hT x hx;have[Q [hQ hSQ]]:=hS x hx.
  exists (P+Q);split;first exact:(@TopologicalGroupUP.subgroup_mul C
    (fun T S:C=>T+S) (fun T=>-T) 0 A hA P Q hP hQ).
  have hDifference:(T+S)-(P+Q)=(T-P)+(S-Q) by rewrite opprD addrACA.
  rewrite hDifference=>hSupport.
  have hUnion:=@current_support_linear_union R h2 n m U hU 1 (T-P) (S-Q).
  rewrite scale1r in hUnion.
  have[hFirst|hSecond]:=hUnion x hSupport;[exact:hTP hFirst|exact:hSQ hSecond].
- move=>T hT x hx;have[P [hP hTP]]:=hT x hx.
  exists (-P);split;first exact:(@TopologicalGroupUP.subgroup_inv C
    (fun T S:C=>T+S) (fun T=>-T) 0 A hA P hP).
  have hDifference:(-T)-(-P)= -(T-P) by rewrite opprB opprK addrC.
  rewrite hDifference=>hSupport.
  have hUnion:=@current_support_linear_union R h2 n m U hU (-1) (T-P) 0.
  rewrite scaleN1r addr0 in hUnion.
  have[hFirst|hZero]:=hUnion x hSupport;first exact:hTP hFirst.
  exact:current_zero_has_empty_support hZero.
Qed.
End CurrentGermLocalGroup.
