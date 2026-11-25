(** Federer (1969), 4.1.12, p. 368: the
    original flat closure is exactly the norm
    closure of the original normal currents inside
    the complete finite-flat space. All comparisons
    use the actual inclusion and exact F_K values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom Bilinear ModuleQuotient RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  SmoothCompactSet CurrentFlatNorm CurrentFiniteFlatSpace CurrentFiniteFlatOperator
  CurrentFiniteFlatCompleteness LinearSubspaceRepresentationUP NormalCurrentsUP
  NormalCurrentLinear CurrentSupportGeometry NormalCurrentSpaces FlatCurrentsUP
  FlatCurrentFinite FiniteFlatNormalClosure NormClosureBalls.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section FlatCurrentClosure.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Variable K:smooth_compact_set hNX U.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation B := (@finite_flat_current_space R h2 n m U hU K).
Local Notation inc := (@finite_flat_current_inclusion R h2 n m U hU K).
Local Notation hB := (@finite_flat_current_space_laws R h2 n m U hU K).
Local Notation N := (@finite_flat_current_norm R h2 n m U hU K).
Local Notation hN := (@finite_flat_current_norm_is_norm R h2 n m U hU K).
Local Notation F := (@current_flat_norm R h2 n m U hU K).
Local Notation flatK := (@is_flat_current_supported_in R h2 n m U hU K).
Local Notation normalB := (@finite_flat_normal_subspace R h2 n m U hU K).
Local Notation closedB := (@finite_flat_normal_closure_subspace R h2 n m U hU K).

(** Source for [finite_flat_current_difference_value]: the
    original F_K distance is exactly the inherited
    norm distance on the finite-flat space, supporting
    the closure and completeness in Federer 4.1.12,
    p. 368. The actual current inclusion is linear. *)
Lemma finite_flat_current_difference_value (z w:B):
  F ((inc z-inc w)%R)=(N (z-w))%:E.
Proof. by rewrite -linearB finite_flat_current_norm_value. Qed.

(** Source for [finite_flat_normal_closure_iff]: the
    norm closure of the original normal subspace
    represents exactly the original F_K closure,
    Federer 4.1.12, p. 368. Every normal
    approximant has its prescribed support in K. *)
Theorem finite_flat_normal_closure_iff (z:B):closedB z<->flatK (inc z).
Proof.
change (@closure (real_norm_metric_space hN) normalB z<->flatK (inc z)).
have hBalls:=@norm_closure_balls R B N hN normalB z.
split.
- move=>hClosure epsilon hEpsilon.
  have [w [hNormal hError]]:=hBalls.1 hClosure epsilon hEpsilon.
  exists (inc w);split;first exact:hNormal.
  rewrite finite_flat_current_difference_value lte_fin.
  by rewrite (real_seminorm_subtract hN.1).
- move=>hFlat;apply:hBalls.2=>epsilon hEpsilon.
  have [S [hNormal hError]]:=@hFlat epsilon hEpsilon.
  have hFinite:=@supported_normal_current_flat_finite R h2 n m U hU K S hNormal.
  have [w hW]:=subspace_representation_full hB hFinite.
  rewrite -hW in hNormal hError.
  exists w;split;first exact:hNormal.
  rewrite finite_flat_current_difference_value lte_fin in hError.
  by rewrite (real_seminorm_subtract hN.1).
Qed.

(** Source for [flat_current_closure_represents]: every
    original flat current in F_(m,K)(U) is
    represented in the closed normal subspace of
    the complete finite-flat space, supporting Federer
    4.1.12, p. 368. Finiteness is proved first. *)
Theorem flat_current_closure_represents (T:C):flatK T->
  exists z:B,inc z=T /\closedB z.
Proof.
move=>hFlat.
have hFinite:=@flat_current_supported_finite R h2 n m U hU K T hFlat.
have [z hZ]:=subspace_representation_full hB hFinite.
exists z;split;first exact:hZ.
apply:(finite_flat_normal_closure_iff z).2;by rewrite hZ.
Qed.

(** Source for [flat_current_subspace]: the original
    class F_(m,K)(U) is a vector subspace of
    D_m(U), Federer 4.1.12, p. 368. Its
    carrier predicate remains exactly the independent
    original approximation condition. *)
Definition flat_current_subspace:subspace C.
Proof.
refine (@Subspace R C flatK _ _ _).
- apply:(@supported_normal_current_is_flat R h2 n m U hU K (0:C)).
  split;first exact:normal_current_zero.
  exact:current_support_zero_subset.
- move=>T S hT hS.
  have [z [hZ hz]]:=flat_current_closure_represents hT.
  have [w [hW hw]]:=flat_current_closure_represents hS.
  have h:flatK (inc (z+w)):=(finite_flat_normal_closure_iff (z+w)).1 (subspace_add hz hw).
  by rewrite (linD (hom_linear inc)) hZ hW in h.
- move=>c T hT.
  have [z [hZ hz]]:=flat_current_closure_represents hT.
  have h:flatK (inc (c*:z)):=(finite_flat_normal_closure_iff (c*:z)).1 (subspace_scale c hz).
  by rewrite (linZ (hom_linear inc)) hZ in h.
Defined.
End FlatCurrentClosure.
