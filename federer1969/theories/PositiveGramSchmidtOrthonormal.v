(** Federer (1969), 3.2.47, p. 282: a unit first vector
    and an already orthonormal input are unchanged by the actual
    positively normalized recurrence. These facts identify the
    section and its value at the chosen sphere point. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization OrthonormalFamilies
  OrthonormalisationUP OrthonormalProjection FinitePrefixes FiniteIndependence
  PositiveGramSchmidtUP PositiveGramSchmidtUniqueness PositiveGramSchmidt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_gram_schmidt_unit_first]: f_1(u)=u
    for a unit first vector in 3.2.47, p. 282. The first
    prefix is empty; no orientation or sign assumption is added. *)
Lemma positive_gram_schmidt_unit_first (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u v:'I_n.+1->V):
  is_positive_gram_schmidt hB u v ->inner_norm hB (u ord0)= 1 ->v ord0=u ord0.
Proof.
move=>hv hUnit.
rewrite (positive_gram_schmidt_equation hv ord0)
  /positive_gram_schmidt_residual /orthonormal_projection big_ord0 subr0
  /inner_normalize hUnit invr1 scale1r; by [].
Qed.

(** Source for [orthonormal_positive_residual]: every residual
    equals its original vector for an orthonormal input, supporting
    the base-point identity of the section in 3.2.47, p. 282. *)
Lemma orthonormal_positive_residual (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V):
  orthonormal_family B u ->forall i,positive_gram_schmidt_residual hB u u i=u i.
Proof.
move=>hu i.
have hProjection:orthonormal_projection hB
    (family_prefix (ltnW (ltn_ord i)) u) (u i)=0.
  rewrite /orthonormal_projection; apply:big1=>j _.
  rewrite inner_coordinateE /family_prefix hu.
  have hDifferent:i!=widen_ord (ltnW (ltn_ord i)) j.
    apply/negP=>/eqP hEqual.
    have hNat:val i=val j:=congr1 val hEqual.
    have hLess : (val j < val i)%N := ltn_ord j.
    move: hLess; by rewrite -hNat ltnn.
  by rewrite (negbTE hDifferent) scale0r.
by rewrite /positive_gram_schmidt_residual hProjection subr0.
Qed.

(** Source for [orthonormal_positive_gram_schmidt]: the original
    chosen orthonormal basis satisfies the exact recurrence at u=c
    in 3.2.47, p. 282, with every residual nonzero. *)
Lemma orthonormal_positive_gram_schmidt (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V):
  orthonormal_family B u ->is_positive_gram_schmidt hB u u.
Proof.
move=>hu; constructor.
- constructor; first exact hu; by move=>k hk x; split.
- move=>i; rewrite (orthonormal_positive_residual hB hu i).
  by rewrite -(inner_norm_eq0 hB) (orthonormal_norm1 hB hu i) oner_eq0.
- move=>i; rewrite (orthonormal_positive_residual hB hu i)
    /inner_normalize (orthonormal_norm1 hB hu i) invr1 scale1r; by [].
Qed.

(** Source for [positive_gram_schmidt_fixes_orthonormal]: the
    sealed positive recurrence fixes an already orthonormal input,
    as used to identify F(c) with the identity in 3.2.47, p. 282. *)
Theorem positive_gram_schmidt_fixes_orthonormal (R:rcfType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n (u:'I_n->V) (hu:finite_independent u):
  orthonormal_family B u ->positive_gram_schmidt_family hB hu=1 u.
Proof.
move=>hOrthonormal.
exact (@positive_gram_schmidt_unique R V B hB n u
  (positive_gram_schmidt_family hB hu) u (positive_gram_schmidt_laws hB hu)
  (orthonormal_positive_gram_schmidt hB hOrthonormal)).
Qed.
