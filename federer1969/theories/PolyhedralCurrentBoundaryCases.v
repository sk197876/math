(** Federer (1969), 4.1.22, p. 379: boundary cases
    of the original generated classes. The empty compact index
    and the empty open domain retain exactly the zero chain.
    Above the ambient dimension the earlier actual simplex
    vanishing gives the same conclusion, without changing the
    original generator condition or introducing nondegeneracy. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals.
From Federer Require Import Hom ModuleQuotient RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces SmoothCompactSet TopologicalGroupUP GeneratedAdditiveSubgroupUP
  GeneratedLinearSubspaceUP PolyhedralCurrentGenerators PolyhedralCurrentAlgebra
  PolyhedralCurrentUnion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralCurrentBoundaryCases.
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
Local Notation generators K := (@polyhedral_simplex_generators R h2 n m U hU K).
Local Notation Empty := (@smooth_compact_empty R X NX hNX U).

(** Source for [integral_polyhedral_current_zero_generators]:
    a generated integral class with only zero generators is
    the zero group, supporting the endpoint cases of the
    original definition in 4.1.22, p. 379. *)
Lemma integral_polyhedral_current_zero_generators (K:Index):
  (forall S,generators K S->S=0)->forall T,Integral K T<->T=0.
Proof.
move=>hOnly T;split;last by move=>->;exact:integral_polyhedral_current_zero.
have hZero:is_subgroup (fun S T:C=>S+T) (fun T=>-T) 0 [set T:C|T=0].
  constructor;first by [].
  - by move=>A B -> ->;rewrite addr0.
  - by move=>A ->;rewrite oppr0.
exact:(generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 n m U hU K) hZero hOnly).
Qed.

(** Source for [polyhedral_current_zero_integral_class]: the
    real span of a zero integral class is the zero subspace,
    supporting the endpoint cases of 4.1.22, p. 379. *)
Lemma polyhedral_current_zero_integral_class (K:Index):
  (forall S,Integral K S->S=0)->forall T,Real K T<->T=0.
Proof.
move=>hOnly T;split;last by move=>->;exact:subspace_zero.
have hAdd:forall S T:C,S=0->T=0->S+T=0
  by move=>A B -> ->;rewrite addr0.
have hScale:forall (a:R) (S:C),S=0->a*:S=0
  by move=>a S ->;rewrite scaler0.
pose Zero:=@Subspace R C [set T:C|T=0] erefl hAdd hScale.
apply:(generated_linear_subspace_least
  (@polyhedral_current_subspace_laws R h2 n m U hU K) (W:=Zero)).
exact:hOnly.
Qed.

(** Source for [polyhedral_current_empty_index]: empty K
    has exactly the zero real polyhedral chain, supporting
    Federer 4.1.22, p. 379. *)
Theorem polyhedral_current_empty_index (T:C):Real Empty T<->T=0.
Proof.
apply:polyhedral_current_zero_integral_class=>S hS.
exact:(@integral_polyhedral_current_empty_index R h2 n m U hU S).1 hS.
Qed.

(** Source for [integral_polyhedral_current_above_dimension]:
    the original integral class is zero above the ambient
    dimension by the existing simplex vanishing, supporting
    Federer 4.1.22, p. 379. *)
Theorem integral_polyhedral_current_above_dimension (K:Index):
  (n<m)%N->forall T,Integral K T<->T=0.
Proof.
move=>hDegree;apply:integral_polyhedral_current_zero_generators.
move=>S [v [hHull <-]].
exact:(@open_oriented_simplex_above_dimension R h2 n m U hU v hDegree).
Qed.

(** Source for [polyhedral_current_above_dimension]: the
    corresponding original real span is zero as well,
    supporting Federer 4.1.22, p. 379. *)
Theorem polyhedral_current_above_dimension (K:Index):
  (n<m)%N->forall T,Real K T<->T=0.
Proof.
move=>hDegree;apply:polyhedral_current_zero_integral_class=>S hS.
exact:(@integral_polyhedral_current_above_dimension K hDegree S).1 hS.
Qed.

(** Source for [integral_polyhedral_current_empty_domain]:
    the original integral union over an empty open source
    is exactly the zero group, supporting 4.1.22, p. 379. *)
Theorem integral_polyhedral_current_empty_domain:
  (forall x,~U x)->forall T,
    @is_integral_polyhedral_current R h2 n m U hU T<->T=0.
Proof.
move=>hEmpty T;split;last by move=>->;exact:integral_polyhedral_union_zero.
move=>[K hT].
have hKE:smooth_compact_carrier K `<=` smooth_compact_carrier Empty.
  move=>x hx;exfalso;exact:hEmpty x (smooth_compact_in_domain K x hx).
apply:(@integral_polyhedral_current_empty_index R h2 n m U hU T).1.
exact:(@integral_polyhedral_current_monotone R h2 n m U hU K Empty hKE T hT).
Qed.

(** Source for [polyhedral_current_empty_domain]: the
    original real union over an empty open source is exactly
    the zero vector space, supporting 4.1.22, p. 379. *)
Theorem polyhedral_current_empty_domain:
  (forall x,~U x)->forall T,
    @is_polyhedral_current R h2 n m U hU T<->T=0.
Proof.
move=>hEmpty T;split;last by move=>->;exact:polyhedral_union_zero.
move=>[K hT].
have hKE:smooth_compact_carrier K `<=` smooth_compact_carrier Empty.
  move=>x hx;exfalso;exact:hEmpty x (smooth_compact_in_domain K x hx).
apply:(@polyhedral_current_empty_index T).1.
exact:(@polyhedral_current_monotone R h2 n m U hU K Empty hKE T hT).
Qed.
End PolyhedralCurrentBoundaryCases.
