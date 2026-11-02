(** Federer (1969), 2.5.9, p. 100: additivity of the continuous extension.
    Positive-lattice density is the correction in erratum p. 2, book p. 100
    line 22. This abstract proof first fixes a point in the original domain,
    then extends in the other variable; it uses uniqueness, not the witness
    construction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ScalarLipschitzExtensionUP DenseScalarExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_scalar_extension_additive]: supporting
    preservation of additivity in Federer 2.5.9, p. 100.
    A cone suffices; closure under negation is not assumed. *)
Theorem dense_scalar_extension_additive (R : realType) (T : Type)
    (W D : set T) (d : T -> T -> R) (add : T -> T -> T) (A B : T -> R) :
  is_pseudometric_on_set W d -> (forall x, D x -> W x) ->
  is_pseudometric_dense_subset W D d ->
  (forall x y, W x -> W y -> W (add x y)) ->
  (forall x y, D x -> D y -> D (add x y)) ->
  (forall x y z, W x -> W y -> W z -> d (add x z) (add y z) <= d x y) ->
  (forall x y z, W x -> W y -> W z -> d (add z x) (add z y) <= d x y) ->
  (forall x y, D x -> D y -> A (add x y)=A x+A y) ->
  is_scalar_lipschitz_extension W D d A B ->
  forall x y, W x -> W y -> B (add x y)=B x+B y.
Proof.
move=> hd hDW hdense hWadd hDadd hright hleft hA hB.
have hfirst u : D u -> forall x, W x -> B (add x u)=B x+A u.
  move=> hu x hx.
  have hC : is_scalar_lipschitz_extension W D d A (fun z => B (add z u)-A u).
    split.
    - move=> z hz; by rewrite (hB.1 _ (hDadd z u hz hu)) (hA z u hz hu) addrK.
    - move=> z w hz hw; rewrite opprB addrA subrK.
      exact: le_trans (hB.2 _ _ (hWadd z u hz (hDW u hu)) (hWadd w u hw (hDW u hu)))
        (hright z w u hz hw (hDW u hu)).
  have he := @dense_scalar_lipschitz_extension_unique R T W D d A _ B hd hDW hdense hC hB x hx.
  have hh := congr1 (fun r => r+A u) he; by rewrite subrK in hh.
move=> x y hx hy.
have hC : is_scalar_lipschitz_extension W D d A (fun z => B (add x z)-B x).
  split.
  - move=> z hz; by rewrite (hfirst z hz x hx) addrAC subrr add0r.
  - move=> z w hz hw; rewrite opprB addrA subrK.
    exact: le_trans (hB.2 _ _ (hWadd x z hx hz) (hWadd x w hx hw)) (hleft z w x hz hw hx).
have he := @dense_scalar_lipschitz_extension_unique R T W D d A _ B hd hDW hdense hC hB y hy.
have hh := congr1 (fun r => r+B x) he; by rewrite subrK addrC in hh.
Qed.
