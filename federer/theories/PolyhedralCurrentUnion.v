(** Federer (1969), 4.1.22, p. 379: integral and real
    polyhedral chains are the unions of the corresponding fixed-K
    subgroups and vector spaces over every compact K in U.
    The compact indices are directed by their existing finite
    union. Prove the asserted group and vector-space structure;
    no compact exhaustion or closure is substituted. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet TopologicalGroupUP GeneratedLinearSubspaceUP
  PolyhedralCurrentAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralCurrentUnion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm
  (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation Index := (smooth_compact_set hNX U).
Local Notation Integral K := (@integral_polyhedral_current_class R h2 n m U hU K).
Local Notation Real K := (@polyhedral_current_subspace R h2 n m U hU K).

(** Source for [is_integral_polyhedral_current]: the original
    group P-script_m(U), the union over every compact K of the
    fixed-K integral subgroup, Federer 4.1.22, p. 379. Its
    members are the integral polyhedral m-chains in U. *)
Definition is_integral_polyhedral_current (T:C):Prop:=exists K:Index,Integral K T.

(** Source for [is_polyhedral_current]: the original real
    space P_m(U), the union over every compact K of the fixed-K
    real space, Federer 4.1.22, p. 379. Its members are
    the polyhedral m-chains in U. *)
Definition is_polyhedral_current (T:C):Prop:=exists K:Index,Real K T.

(** Source for [integral_polyhedral_union_zero]: the original
    union contains zero even when U is empty; the empty
    compact index suffices, Federer 4.1.22, p. 379. *)
Lemma integral_polyhedral_union_zero:is_integral_polyhedral_current (0:C).
Proof.
exists (@smooth_compact_empty R X NX hNX U);exact:integral_polyhedral_current_zero.
Qed.

(** Source for [integral_polyhedral_union_add]: the original
    union is closed under addition, Federer 4.1.22, p. 379.
    The union of the two compact indices is a common index. *)
Theorem integral_polyhedral_union_add (S T:C):
  is_integral_polyhedral_current S->is_integral_polyhedral_current T->
  is_integral_polyhedral_current (S+T).
Proof.
move=>[K hS] [L hT].
pose M:=smooth_compact_union K L.
have hKM:smooth_compact_carrier K `<=` smooth_compact_carrier M
  by move=>x hx;left.
have hLM:smooth_compact_carrier L `<=` smooth_compact_carrier M
  by move=>x hx;right.
exists M;apply:integral_polyhedral_current_add.
- exact:(@integral_polyhedral_current_monotone R h2 n m U hU K M hKM S hS).
- exact:(@integral_polyhedral_current_monotone R h2 n m U hU L M hLM T hT).
Qed.

(** Source for [integral_polyhedral_union_negate]: the original
    union is closed under additive inversion, Federer
    4.1.22, p. 379. The original compact index is retained. *)
Lemma integral_polyhedral_union_negate (T:C):
  is_integral_polyhedral_current T->is_integral_polyhedral_current (-T).
Proof.
move=>[K hT];exists K;exact:integral_polyhedral_current_negate hT.
Qed.

(** Source for [integral_polyhedral_union_subgroup]: the
    original union is an additive subgroup of actual currents,
    hence an abelian group, Federer 4.1.22, p. 379. *)
Theorem integral_polyhedral_union_subgroup:
  is_subgroup (fun S T:C=>S+T) (fun T=>-T) 0 is_integral_polyhedral_current.
Proof.
constructor.
- exact:integral_polyhedral_union_zero.
- exact:integral_polyhedral_union_add.
- exact:integral_polyhedral_union_negate.
Qed.

(** Source for [polyhedral_union_zero]: the original real
    union contains zero, including empty U and K,
    Federer 4.1.22, p. 379. *)
Lemma polyhedral_union_zero:is_polyhedral_current (0:C).
Proof.
exists (@smooth_compact_empty R X NX hNX U);exact:subspace_zero.
Qed.

(** Source for [polyhedral_union_linear_combination]: the
    original union is closed under every real linear
    combination, Federer 4.1.22, p. 379. The proof
    uses a common finite union of compact indices. *)
Theorem polyhedral_union_linear_combination c (S T:C):
  is_polyhedral_current S->is_polyhedral_current T->
  is_polyhedral_current (c*:S+T).
Proof.
move=>[K hS] [L hT].
pose M:=smooth_compact_union K L.
have hKM:smooth_compact_carrier K `<=` smooth_compact_carrier M
  by move=>x hx;left.
have hLM:smooth_compact_carrier L `<=` smooth_compact_carrier M
  by move=>x hx;right.
have hS':Real M S:=@polyhedral_current_monotone R h2 n m U hU K M hKM S hS.
have hT':Real M T:=@polyhedral_current_monotone R h2 n m U hU L M hLM T hT.
exists M;exact:subspace_add (subspace_scale c hS') hT'.
Qed.

(** Source for [polyhedral_current_union_subspace]: the
    literal compact union has the original vector-space
    laws, Federer 4.1.22, p. 379. This packages a
    proved predicate and does not choose a new model. *)
Definition polyhedral_current_union_subspace:subspace C.
Proof.
refine (@Subspace R C is_polyhedral_current polyhedral_union_zero _ _).
- move=>S T hS hT;have h:=polyhedral_union_linear_combination 1 hS hT.
  by rewrite scale1r in h.
- move=>c S hS;have h:=polyhedral_union_linear_combination c hS polyhedral_union_zero.
  by rewrite addr0 in h.
Defined.

(** Source for [integral_polyhedral_union_is_polyhedral]:
    every original integral polyhedral chain is a real
    polyhedral chain, Federer 4.1.22, p. 379. *)
Theorem integral_polyhedral_union_is_polyhedral:
  is_integral_polyhedral_current `<=` is_polyhedral_current.
Proof.
move=>T [K hT];exists K;exact:integral_polyhedral_current_is_polyhedral hT.
Qed.

(** Source for [polyhedral_current_union_span_laws]: the
    original real compact union is also exactly the algebraic
    real span of the original integral compact union, as
    follows from the two generation and union definitions in
    Federer 4.1.22, p. 379. No closure is added. *)
Theorem polyhedral_current_union_span_laws:
  is_generated_linear_subspace is_integral_polyhedral_current
    polyhedral_current_union_subspace.
Proof.
constructor;first exact:integral_polyhedral_union_is_polyhedral.
move=>W hW T [K hT].
have hGenerators:Integral K `<=` W.
  move=>S hS;apply:hW;exists K;exact:hS.
exact:(@generated_linear_subspace_least R C (Integral K) (Real K)
  (@polyhedral_current_subspace_laws R h2 n m U hU K) W hGenerators T hT).
Qed.
End PolyhedralCurrentUnion.
