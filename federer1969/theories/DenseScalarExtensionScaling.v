(** Federer (1969), 2.5.9, p. 100: positive homogeneity of the continuous
    extension on the positive cone. The density correction is erratum p. 2,
    book p. 100 line 22. Uniqueness identifies the rescaled extension
    without consulting its implementation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ScalarLipschitzExtensionUP DenseScalarExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_scalar_extension_positive_scaling]:
    supporting positive homogeneity in Federer 2.5.9, p. 100.
    The zero scalar is handled by agreement at zero in the application. *)
Theorem dense_scalar_extension_positive_scaling (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (F : T -> T) (A B : T -> R) (c : R) :
  is_pseudometric_on_set W d -> (forall x, D x -> W x) ->
  is_pseudometric_dense_subset W D d -> 0 < c ->
  (forall x, W x -> W (F x)) -> (forall x, D x -> D (F x)) ->
  (forall x y, W x -> W y -> d (F x) (F y) <= c*d x y) ->
  (forall x, D x -> A (F x)=c*A x) ->
  is_scalar_lipschitz_extension W D d A B ->
  forall x, W x -> B (F x)=c*B x.
Proof.
move=> hd hDW hdense hc hW hD hdist hA hB.
have hc0 : c != 0 by rewrite (gt_eqF hc).
have hC : is_scalar_lipschitz_extension W D d A (fun x => c^-1*B (F x)).
  split.
  - move=> x hx; by rewrite (hB.1 _ (hD x hx)) (hA x hx) mulrA mulVf // mul1r.
  - move=> x y hx hy; rewrite -mulrBr normrM normfV (ger0_norm (ltW hc)) mulrC.
    rewrite ler_pdivrMr //.
    have hh := le_trans (hB.2 _ _ (hW x hx) (hW y hy)) (hdist x y hx hy).
    by rewrite mulrC in hh.
move=> x hx.
have he := @dense_scalar_lipschitz_extension_unique R T W D d A _ B hd hDW hdense hC hB x hx.
have hh := congr1 (fun r => c*r) he; by rewrite mulrA mulfV // mul1r in hh.
Qed.
