(** Earlier source scope: Federer (1969), 4.1.22, p. 379,
    uses the actual simplex currents of 4.1.11, pp. 365–366.
    Their fixed-index normality gives the original inclusion
    diagram in 4.1.24, p. 381. The retained source comments
    also identify their later use in 4.1.32. These prerequisites use the original public simplex operations. *)
(** Federer (1969), 4.1.32, p. 393: the
    measurable restrictions of the polyhedral chains
    are defined on their original integration
    representations. Every original polyhedral chain is
    normal, by simplex normality and the least-group
    and real-span laws. The exact K is retained. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient TopologicalGroupUP
  RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry
  SmoothCompactSet NormalCurrentsUP NormalCurrentLinear
  GeneratedAdditiveSubgroupUP GeneratedLinearSubspaceUP PolyhedralCurrentGenerators
  PolyhedralCurrentAlgebra PolyhedralCurrentUnion OpenSimplexGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralNormal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Normal:=(@is_normal_current R h2 n U hU m).
Variable K:smooth_compact_set hNX U.
Local Notation Supported:=(fun T:C=>@current_support R h2 n U hU m T
  `<=` smooth_compact_carrier K).
Local Notation Good:=(fun T:C=>Normal T /\Supported T).

(** Source for [polyhedral_normal_zero]: the original
    zero normal current from 4.1.7, p. 358,
    has every fixed-K support constraint, supporting
    the halfspace argument in 4.1.32, p. 393. *)
Local Lemma polyhedral_normal_zero:Good 0.
Proof. split;[exact:normal_current_zero|exact:current_support_zero_subset]. Qed.

(** Source for [polyhedral_normal_linear]: the original
    normal-current linearity and common compact-support
    laws of 4.1.7, p. 358, supporting
    the generated classes in 4.1.32, p. 393. *)
Local Lemma polyhedral_normal_linear c (S T:C):
  Good S->Good T->Good (c*:S+T).
Proof.
move=>[hS hSK] [hT hTK];split.
- exact:normal_current_linear hS hT.
- exact:current_support_linear_subset hSK hTK.
Qed.

(** Source for [integral_polyhedral_current_normal_support]:
    every original fixed-K integral polyhedral current
    is normal and supported in that K, used
    for the halfspace restriction in 4.1.32,
    p. 393. Empty indices are included. *)
Theorem integral_polyhedral_current_normal_support (T:C):
  @integral_polyhedral_current_class R h2 n m U hU K T->Good T.
Proof.
have hGood:is_subgroup (fun S T:C=>S+T) (fun T=>-T) 0 Good.
  constructor;first exact:polyhedral_normal_zero.
  - move=>A B hA hB;have h:=polyhedral_normal_linear 1 hA hB.
    by rewrite scale1r in h.
  - move=>T0 hT;have h:=polyhedral_normal_linear (-1) hT polyhedral_normal_zero.
    by rewrite addr0 scaleN1r in h.
apply:(generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 n m U hU K) hGood).
move=>S [v [hHull <-]];split.
- apply:open_simplex_current_normal.
  exact:subset_trans hHull (smooth_compact_in_domain K).
- move=>x hx;exact:(hHull x (@open_simplex_current_hull_support R h2 n U hU m v x hx)).
Qed.

(** Source for [real_polyhedral_current_normal_support]:
    the original real fixed-K span has the same
    normality and support properties, required by
    Federer 4.1.32, p. 393, final paragraph. *)
Theorem real_polyhedral_current_normal_support (T:C):
  @polyhedral_current_subspace R h2 n m U hU K T->Good T.
Proof.
have hAdd:forall S T:C,Good S->Good T->Good (S+T).
  move=>A B hA hB;have h:=polyhedral_normal_linear 1 hA hB.
  by rewrite scale1r in h.
have hScale:forall (c:R) (T:C),Good T->Good (c*:T).
  move=>c T0 hT;have h:=polyhedral_normal_linear c hT polyhedral_normal_zero.
  by rewrite addr0 in h.
pose GoodSpace:=@Subspace R C Good polyhedral_normal_zero hAdd hScale.
apply:(generated_linear_subspace_least
  (@polyhedral_current_subspace_laws R h2 n m U hU K) (W:=GoodSpace)).
exact:integral_polyhedral_current_normal_support.
Qed.

End PolyhedralNormal.

Section PolyhedralUnionNormal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation Normal:=(@is_normal_current R h2 n U hU m).

(** Source for [integral_polyhedral_union_normal]: the
    full original integral compact union consists of
    normal currents, supporting 4.1.32, p. 393. *)
Theorem integral_polyhedral_union_normal (T:C):
  @is_integral_polyhedral_current R h2 n m U hU T->Normal T.
Proof.
move=>[L hL];exact:(@integral_polyhedral_current_normal_support R h2 n m U hU L T hL).1.
Qed.

(** Source for [real_polyhedral_union_normal]: the
    full original real compact union consists of
    normal currents, supporting the real versions of
    4.1.32, p. 393. *)
Theorem real_polyhedral_union_normal (T:C):
  @is_polyhedral_current R h2 n m U hU T->Normal T.
Proof.
move=>[L hL];exact:(@real_polyhedral_current_normal_support R h2 n m U hU L T hL).1.
Qed.
End PolyhedralUnionNormal.
