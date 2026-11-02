(** Federer (1969), 1.7.3, p. 29: orthonormal diagonalisation of symmetric
    endomorphisms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP SymmetricEndomorphisms
  EndomorphismBilinearForm PrincipalAxes PrincipalAxesUP PrincipalAxesDiagonal
  EigenbasisUP OrthonormalSingleCoordinate LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [symmetric_orthonormal_eigenbasis]: Federer
    1.7.3, p. 29, the displayed eigenvector conclusion: every
    symmetric endomorphism in finite dimension admits an orthonormal
    basis of eigenvectors with real eigenvalues. *)
Theorem symmetric_orthonormal_eigenbasis (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (f : {linear V -> V}) (hf : is_symmetric_endomorphism B f)
    n (b : 'I_n -> V) (hb : is_basis b) :
  exists e : 'I_n -> V, exists lambda : 'I_n -> R,
    is_orthonormal_eigenbasis B f e lambda.
Proof.
pose S := endomorphism_bilinear_form B f.
have hS := @endomorphism_bilinear_formP R V B hB f.
have hs := @endomorphism_form_symmetric R V B hB f hf.
have [e he] := @principal_axes_exists R V B S hB hS hs n b hb.
exists e, (fun i => S (e i) (e i)); constructor.
- exact: principal_axes_basis he.
- exact: principal_axes_orthonormal he.
- move=> i; apply: (@orthonormal_single_coordinate R V B hB n e
    (principal_axes_basis he) (principal_axes_orthonormal he) (f (e i)) i).
  move=> j hji; change (S (e i) (e j) = 0).
  apply: (@principal_axes_distinct R V B S hs n e he i j).
  by rewrite eq_sym.
Qed.
