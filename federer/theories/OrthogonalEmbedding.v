(** Federer (1969), 1.7.4, p. 31, final paragraph: selecting an orthogonal
    injection into a sufficiently large intersection. Supporting existence
    proof from orthonormal bases *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import reals.
From Federer Require Import InnerProductUP OrthonormalFamilies
  OrthonormalisationUP GramSchmidt OrthogonalMaps OrthogonalBasisCriteria
  BasisInterpolation LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [orthogonal_embedding_exists]: Federer 1.7.4,
    p. 31, supporting existence of an orthogonal injection from
    a space of dimension k into a space of dimension at least k. *)
Theorem orthogonal_embedding_exists (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    k (b : 'I_k -> V) (hb : is_basis b)
    n (c : 'I_n -> U) (hc : is_basis c) (hkn : (k <= n)%N) :
  exists f : {linear V -> U}, is_orthogonal_map B C f.
Proof.
have [e [he heg]] := @orthonormal_basis_exists R V B hB k b hb.
have [d [hd hdg]] := @orthonormal_basis_exists R U C hC n c hc.
have heo := orthonormalisation_orthonormal heg.
have hdo := orthonormalisation_orthonormal hdg.
pose f := basis_interpolation he (fun i => d (widen_ord hkn i)).
exists f; apply: (@orthogonal_map_basis_criterion R V U B C hB hC k e he heo f).
move=> i j; rewrite /f !basis_interpolationE hdo.
have hi : injective (@widen_ord k n hkn) by move=> x y h; apply: val_inj; exact (congr1 (fun t : 'I_n => (t : nat)) h).
by rewrite (inj_eq hi).
Qed.
