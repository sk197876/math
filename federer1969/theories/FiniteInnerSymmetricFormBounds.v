(** Federer (1969), 3.1.11, p. 221, and 3.1.14,
    p. 225: polynomial coefficient forms on a finite-dimensional
    source are continuous. This supporting coordinate estimate
    allows an arbitrary seminormed target; no target completeness
    or dimension hypothesis is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm InnerNormInequalities
  OrthonormalFamilies OrthonormalisationUP GramSchmidt LinearBasis
  SymmetricForms SymmetricFormIsomorphism SymmetricProductContinuity
  ContinuousSymmetricFormAdapter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_inner_symmetric_form_coordinate_bound]:
    supporting continuity of the polynomial coefficients in Federer
    3.1.14, p. 225, from the finite-coordinate expansion of 1.10.5,
    p. 48. The estimate includes degree zero and the zero source. *)
Lemma finite_inner_symmetric_form_coordinate_bound (R : realType)
    (X Y : lmodType R) (B : X->X->R) (hB : is_inner_product B)
    (NY : Y->R) (hNY : is_real_seminorm NY) n (e : 'I_n->X)
    (he : is_basis e) (ho : orthonormal_family B e) k (phi : S_m X Y k)
    (u : 'I_k->X) :
  NY (phi [tuple u i | i<k]) <=
    (\sum_(a : {ffun 'I_k->'I_n})
      (\prod_(i<k) inner_norm hB (e (a i))) *
        NY (phi [tuple e (a i) | i<k])) *
    \prod_(i<k) inner_norm hB (u i).
Proof.
have hex : phi [tuple u i | i<k] =
    \sum_(a : {ffun 'I_k->'I_n})
      (\prod_(i<k) inner_coordinate hB (e (a i)) (u i)) *:
        phi [tuple e (a i) | i<k].
  rewrite -(sform_to_hom_tuple phi).
  rewrite (@symmetric_product_coordinate_expansion R X B hB n e he ho k u)
    linear_sum.
  apply: eq_bigr=>a _; rewrite linearZ.
  change ((\prod_(i<k) inner_coordinate hB (e (a i)) (u i))*:
    (sform_to_hom phi (symmetric_tuple_component [tuple e (a i) | i<k]))=
    (\prod_(i<k) inner_coordinate hB (e (a i)) (u i))*:
      phi [tuple e (a i) | i<k]).
  by rewrite sform_to_hom_tuple.
rewrite hex; apply: le_trans (real_seminorm_sum hNY _) _.
rewrite mulr_suml; apply: ler_sum=>a _.
rewrite (real_seminorm_scale hNY) normr_prod.
have hc i : `|inner_coordinate hB (e (a i)) (u i)| <=
    inner_norm hB (u i)*inner_norm hB (e (a i)).
  rewrite inner_coordinateE; exact: inner_cauchy.
have hp : (\prod_(i<k) `|inner_coordinate hB (e (a i)) (u i)|) <=
    (\prod_(i<k) (inner_norm hB (u i)*inner_norm hB (e (a i)))).
  apply: ler_prod=>i _; apply/andP; split; [exact: normr_ge0|exact: hc].
rewrite big_split in hp.
have hh := ler_wpM2r (real_seminorm_nonnegative hNY (phi [tuple e (a i) | i<k])) hp.
apply: le_trans hh _.
change (((\prod_(i<k) inner_norm hB (u i))*(\prod_(i<k) inner_norm hB (e (a i))))*
    NY (phi [tuple e (a i) | i<k])<=
  ((\prod_(i<k) inner_norm hB (e (a i)))*NY (phi [tuple e (a i) | i<k]))*
    (\prod_(i<k) inner_norm hB (u i))).
suff -> : ((\prod_(i<k) inner_norm hB (u i))*(\prod_(i<k) inner_norm hB (e (a i))))*
    NY (phi [tuple e (a i) | i<k])=
  ((\prod_(i<k) inner_norm hB (e (a i)))*NY (phi [tuple e (a i) | i<k]))*
    (\prod_(i<k) inner_norm hB (u i)) by exact: lexx.
ring.
Qed.

(** Source for [finite_inner_symmetric_form_bounded]:
    every coefficient form of a polynomial on Euclidean space
    satisfies the continuity requirement in Federer 3.1.11,
    p. 221, as used without an extra hypothesis in 3.1.14,
    p. 225. Only the source is finite-dimensional. *)
Theorem finite_inner_symmetric_form_bounded (R : realType)
    (X Y : lmodType R) (B : X->X->R) (hB : is_inner_product B)
    (NY : Y->R) (hNY : is_real_seminorm NY) n (e : 'I_n->X)
    (he : is_basis e) k (phi : S_m X Y k) :
  norm_bounded_symmetric_form (inner_norm hB) NY phi.
Proof.
have [d [hd hod]] := orthonormal_basis_exists hB he.
have ho := orthonormalisation_orthonormal hod.
exists (\sum_(a : {ffun 'I_k->'I_n})
  (\prod_(i<k) inner_norm hB (d (a i))) *
    NY (phi [tuple d (a i) | i<k])); split.
- apply: sumr_ge0=>a _; apply: mulr_ge0.
  + apply: prodr_ge0=>i _; exact: inner_norm_nonnegative.
  + exact (real_seminorm_nonnegative hNY _).
move=>t.
have hh := @finite_inner_symmetric_form_coordinate_bound R X Y B hB
  NY hNY n d hd ho k phi (fun i=>tnth t i).
have heq : [tuple tnth t i | i<k]=t.
  apply: eq_from_tnth=>i; by rewrite tnth_mktuple.
by rewrite heq in hh.
Qed.
