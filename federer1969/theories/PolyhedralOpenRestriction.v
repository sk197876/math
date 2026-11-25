(** Federer (1969), 4.1.22, p. 379: the same
    admissible polyhedral generators on a smaller open
    neighbourhood of their original compact K retain their
    original integral and real membership. This supplies the
    arbitrary-open transfers in 4.1.23 and the approximation
    witnesses of 4.1.24, pp. 379–380. Reuse actual current
    restriction and its transitivity, without a new simplex
    or compact carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals topology.
From Federer Require Import Bilinear Hom ModuleQuotient TopologicalGroupUP
  RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  SmoothCompactSet CurrentSpaces CurrentOpenRestriction CurrentOpenRestrictionTransitive
  CurrentLipschitzCompactImage PolyhedralCurrentGenerators PolyhedralCurrentAlgebra
  GeneratedAdditiveSubgroupUP GeneratedLinearSubspaceUP OrientedSimplexCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PolyhedralOpenRestriction.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variables U W:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hW:forall x,W x->norm_domain_interior NX W x.
Hypothesis hWU:W `<=` U.
Local Notation C:=(@current_space R h2 n U hU m).
Local Notation D:=(@current_space R h2 n W hW m).
Local Notation Restrict:=(@current_open_restriction R h2 n m W U hW hU hWU).

(** Source for [open_oriented_simplex_current_restriction]: the
    original simplex abbreviation of 4.1.22, p. 379,
    commutes with the existing open restriction. No hull
    containment or support premise is needed for this identity. *)
Theorem open_oriented_simplex_current_restriction (v:'I_(m.+1)->X):
  Restrict (@open_oriented_simplex_current R h2 n m U hU v)=
    @open_oriented_simplex_current R h2 n m W hW v.
Proof.
unfold open_oriented_simplex_current.
exact:(@current_open_restriction_transitive R h2 n m W U (fun _=>True)
  hW hU (fun (x:X) (_:True)=>@norm_full_domain_interior R X NX x)
  hWU (fun _ _=>Logic.I) (fun _ _=>Logic.I)
  (@OrientedSimplexCurrent.value R h2 n m v)).
Qed.

Variable K:smooth_compact_set hNX U.
Hypothesis hKW:smooth_compact_carrier K `<=` W.
Local Notation KW:=(@current_compact_index_in_open R n U W K hKW).

(** Source for [integral_polyhedral_current_open_restriction]: the
    actual same-K restriction preserves the original generated
    integral subgroup, supporting 4.1.23–4.1.24, pp. 379–380,
    by the full generator condition of 4.1.22, p. 379. *)
Theorem integral_polyhedral_current_open_restriction (T:C):
  @integral_polyhedral_current_class R h2 n m U hU K T->
  @integral_polyhedral_current_class R h2 n m W hW KW (Restrict T).
Proof.
pose Good:=fun S:C=>@integral_polyhedral_current_class R h2 n m W hW KW (Restrict S).
have hGood:is_subgroup (fun S T:C=>S+T) (fun T=>-T) 0 Good.
  constructor.
  - rewrite /Good (lin0 (hom_linear Restrict));exact:integral_polyhedral_current_zero.
  - move=>S Q hS hQ;rewrite /Good (linD (hom_linear Restrict)).
    exact:integral_polyhedral_current_add hS hQ.
  - move=>S hS;rewrite /Good -scaleN1r (linZ (hom_linear Restrict)) scaleN1r.
    exact:integral_polyhedral_current_negate hS.
apply:(generated_additive_subgroup_least
  (@integral_polyhedral_current_class_laws R h2 n m U hU K) hGood).
move=>S [v [hHull <-]];rewrite /Good open_oriented_simplex_current_restriction.
exact:(@integral_polyhedral_current_generator R h2 n m W hW KW v hHull).
Qed.

(** Source for [real_polyhedral_current_open_restriction]: the
    original real-span counterpart of the same-K restriction,
    supporting 4.1.23–4.1.24, pp. 379–380, with every
    original real coefficient retained. *)
Theorem real_polyhedral_current_open_restriction (T:C):
  @polyhedral_current_subspace R h2 n m U hU K T->
  @polyhedral_current_subspace R h2 n m W hW KW (Restrict T).
Proof.
pose Good:=fun S:C=>@polyhedral_current_subspace R h2 n m W hW KW (Restrict S).
have hZero:Good 0.
  rewrite /Good (lin0 (hom_linear Restrict));exact:subspace_zero.
have hAdd:forall S Q:C,Good S->Good Q->Good (S+Q).
  move=>S Q hS hQ;rewrite /Good (linD (hom_linear Restrict)).
  exact:subspace_add hS hQ.
have hScale:forall (a:R) (S:C),Good S->Good (a*:S).
  move=>a S hS;rewrite /Good (linZ (hom_linear Restrict)).
  exact:(@subspace_scale R D
    (@polyhedral_current_subspace R h2 n m W hW KW) a (Restrict S) hS).
pose GoodSpace:=@Subspace R C Good hZero hAdd hScale.
apply:(generated_linear_subspace_least
  (@polyhedral_current_subspace_laws R h2 n m U hU K) (W:=GoodSpace)).
move=>S hS;apply:integral_polyhedral_current_is_polyhedral.
exact:integral_polyhedral_current_open_restriction hS.
Qed.
End PolyhedralOpenRestriction.
