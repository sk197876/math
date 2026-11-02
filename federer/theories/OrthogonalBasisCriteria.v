(** Federer (1969), 1.7.3, p. 30: verification of the maps prescribed on the
    adapted orthonormal basis. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP OrthonormalFamilies OrthogonalMaps
  SymmetricEndomorphisms EndomorphismBilinearForm OrthogonalImageBasis
  BilinearBasisExt Bilinear TensorUP LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_map_basis_criterion]: Federer
    1.7.3, p. 30, supporting verification: a linear map taking
    an orthonormal basis to an orthonormal family preserves the
    inner product on all vectors. *)
Theorem orthogonal_map_basis_criterion (R : realType) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (f : {linear V -> U}) :
  orthonormal_family C (fun i => f (e i)) -> is_orthogonal_map B C f.
Proof.
move=> hf; apply: (@bilinear_basis_ext R (Choice.clone 'I_n _) (Choice.clone 'I_n _)
  V V R^o e e he he (image_bilinear_form C f) B
  (@image_bilinear_formP R V U C hC f) (inner_bilinear hB)).
by move=> i j; rewrite /image_bilinear_form hf ho.
Qed.

(** Source for [symmetric_diagonal_basis_criterion]: Federer
    1.7.3, p. 30, supporting symmetry of g(e_i)=|f(e_i)|e_i:
    any real diagonal map in an orthonormal basis is symmetric. *)
Theorem symmetric_diagonal_basis_criterion (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    n (e : 'I_n -> V) (he : is_basis e) (ho : orthonormal_family B e)
    (f : {linear V -> V}) (lambda : 'I_n -> R) :
  (forall i, f (e i) = lambda i *: e i) -> is_symmetric_endomorphism B f.
Proof.
move=> hf.
pose S := endomorphism_bilinear_form B f.
have hS := @endomorphism_bilinear_formP R V B hB f.
have hT : @bilinear R V V R^o (fun x y => S y x) by split; [exact hS.2 | exact hS.1].
have hs : forall x y, S x y = S y x.
  apply: (@bilinear_basis_ext R (Choice.clone 'I_n _) (Choice.clone 'I_n _)
    V V R^o e e he he S (fun x y => S y x) hS hT).
  move=> i j; rewrite /S /endomorphism_bilinear_form !hf
    !(bilZl (inner_bilinear hB)).
  case: (eqVneq i j) => [hij|hne]; first by rewrite hij.
  have hne' : j != i by rewrite eq_sym.
  rewrite !ho (negbTE hne) (negbTE hne').
  change (lambda i * 0 = lambda j * 0).
  by rewrite !mulr0.
move=> x y; rewrite -[B x (f y)](inner_symmetric hB).
exact: hs.
Qed.
