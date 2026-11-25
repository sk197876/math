(** Linear-algebra support for Federer (1969), 1.6.3, p. 25. Annihilators
    are defined by their vanishing property. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Annihilator.
Variable K : fieldType.
Variable V : lmodType K.
Variable S : subspace V.

(** Source for [annihilates]: Federer 1.6.3, p. 25, first display.
    Direct defining property: a functional vanishes on every vector of S. *)
Definition annihilates (a : Hom V K^o) := forall v, S v -> a v = 0.

(** Source for [annihilates_zero]: Federer 1.6.3, p. 25, annihilator;
    supporting closure verification for the zero functional. *)
Lemma annihilates_zero : annihilates 0.
Proof. by move=> v hv; rewrite hom_zeroE. Qed.

(** Source for [annihilates_add]: Federer 1.6.3, p. 25, annihilator;
    supporting closure verification for addition. *)
Lemma annihilates_add a b : annihilates a -> annihilates b -> annihilates (a+b).
Proof. by move=> ha hb v hv; rewrite hom_addE ha // hb // add0r. Qed.

(** Source for [annihilates_scale]: Federer 1.6.3, p. 25, annihilator;
    supporting closure verification for scalar multiplication. *)
Lemma annihilates_scale c a : annihilates a -> annihilates (c *: a).
Proof. by move=> ha v hv; rewrite hom_scaleE ha // scaler0. Qed.

(** Source for [annihilator]: Federer 1.6.3, p. 25, first display.
    Direct abstract subspace defined by vanishing on S; the preceding
    proofs supply all required subspace laws. *)
Definition annihilator : subspace (Hom V K^o) :=
  @Subspace K (Hom V K^o) annihilates annihilates_zero
    annihilates_add annihilates_scale.
End Annihilator.

(** Source for [annihilator_span]: Federer 1.6.3, p. 25,
    adapted-basis argument. Supporting equivalence: a functional
    annihilates a spanned subspace iff it vanishes on the generators. *)
Theorem annihilator_span (K : fieldType) (V : lmodType K)
  m (e : 'I_m -> V) (a : Hom V K^o) :
  annihilator (finite_span_subspace e) a <-> forall i, a (e i) = 0.
Proof.
split.
- move=> ha i; exact: ha _ (finite_span_generator e i).
- move=> ha v [c ->]; rewrite (big_morph a (linD (hom_linear a)) (lin0 (hom_linear a))).
  apply: big1 => i _; by rewrite (linZ (hom_linear a)) ha scaler0.
Qed.

(** Source for [basis_vector_expansion]: Federer 1.6.3, p. 25,
    adapted dual bases. Supporting expansion: a vector is the sum of
    its dual coordinates times the corresponding basis vectors. *)
Lemma basis_vector_expansion (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) v :
  v = \sum_i (dual_basis he i v : K) *: e i.
Proof.
rewrite -{1}(basis_coordinatesK he v) basis_synthesis_finiteE.
apply: eq_bigr => i _; by [].
Qed.

(** Source for [complementary_primal_span]: Federer 1.6.3, p. 25,
    duality and annihilators. Supporting dual version of the adapted
    basis calculation: the common kernel of selected coordinate
    functionals is the span of the complementary basis vectors. *)
Theorem complementary_primal_span (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) p (lambda : Lambda n p) v :
  in_finite_span (fun j => e (tnth (val (top_complement lambda)) j)) v <->
    forall i, i \in Lambda_set lambda -> dual_basis he i v = 0.
Proof.
pose nu := top_complement lambda.
have hnu i : (i \in val nu) = (i \notin Lambda_set lambda).
  have hm : (i \in Lambda_set nu) = (i \notin Lambda_set lambda).
    by rewrite /nu /top_complement nu_image Lambda_top_set in_setD in_setT andbT.
  by rewrite -hm /Lambda_set inE.
split.
- move=> [c ->] i hi.
  rewrite (big_morph (dual_basis he i) (linD (hom_linear (dual_basis he i)))
    (lin0 (hom_linear (dual_basis he i)))); apply: big1 => j _.
  rewrite (linZ (hom_linear (dual_basis he i))) dual_basisE.
  have hji : tnth (val nu) j != i.
    apply/eqP=> h; have hj := mem_tnth j (val nu).
    by rewrite h hnu hi in hj.
  by rewrite (negbTE hji) scaler0.
- move=> hv; rewrite (basis_vector_expansion he v).
  apply: big_ind; first exact: in_finite_span_zero.
  + move=> x y; exact: in_finite_span_add.
  + move=> i _; case hi: (i \in Lambda_set lambda).
    * rewrite hv // scale0r; exact: in_finite_span_zero.
    * apply: in_finite_span_scale.
      have hmem : i \in val nu by rewrite hnu hi.
      have /tnthP [j hj] := hmem.
      rewrite hj; exact: finite_span_generator.
Qed.

(** Source for [dual_basis_expansion]: Federer 1.6.3, p. 25,
    adapted-basis annihilator calculation. Supporting formula: a
    functional is the sum of its values on basis vectors times the
    corresponding dual basis functionals. *)
Lemma dual_basis_expansion (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) (a : Hom V K^o) :
  a = \sum_i (a (e i) : K) *: dual_basis he i.
Proof.
apply: hom_ext => v.
apply: (basis_linear_ext he (hom_as_linear a)
  (hom_as_linear (\sum_i (a (e i) : K) *: dual_basis he i))) v => i.
exact: esym (dual_sum_evaluate he (fun j => (a (e j) : K)) i).
Qed.

(** Source for [complementary_dual_span]: Federer 1.6.3, p. 25,
    annihilator in an adapted basis. Supporting general indexed form:
    functionals vanishing on a selected part of a basis are exactly
    the span of the complementary dual basis vectors. *)
Theorem complementary_dual_span (K : fieldType) (V : lmodType K)
  n (e : 'I_n -> V) (he : is_basis e) p (lambda : Lambda n p)
  (a : Hom V K^o) :
  in_finite_span (fun j => dual_basis he (tnth (val (top_complement lambda)) j)) a
    <-> forall i, i \in Lambda_set lambda -> a (e i) = 0.
Proof.
pose nu := top_complement lambda.
have hnu i : (i \in val nu) = (i \notin Lambda_set lambda).
  have hm : (i \in Lambda_set nu) = (i \notin Lambda_set lambda).
    by rewrite /nu /top_complement nu_image Lambda_top_set in_setD in_setT andbT.
  by rewrite -hm /Lambda_set inE.
split.
- move=> [c ->] i hi; rewrite hom_sumE; apply: big1 => j _.
  rewrite hom_scaleE dual_basisE.
  have hji : i != tnth (val nu) j.
    apply/eqP=> h; have hj := mem_tnth j (val nu).
    by rewrite hnu -h hi in hj.
  by rewrite (negbTE hji) scaler0.
- move=> ha; rewrite (dual_basis_expansion he a).
  apply: big_ind; first exact: in_finite_span_zero.
  + move=> x y; exact: in_finite_span_add.
  + move=> i _; case hi: (i \in Lambda_set lambda).
    * rewrite ha // scale0r; exact: in_finite_span_zero.
    * apply: in_finite_span_scale.
      have hmem : i \in val nu by rewrite hnu hi.
      have /tnthP [j hj] := hmem.
      rewrite hj; exact: finite_span_generator.
Qed.
