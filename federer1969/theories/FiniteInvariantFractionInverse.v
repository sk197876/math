(** Supporting algebra for Federer (1969), 3.4.8(8),
    pp. 329–330: a finite coefficient subspace
    containing one and stable under a nonzero
    multiplier contains its inverse. Apply the
    existing finite-dimensional inverse theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier LinearBasis LinearGroupTopology RingScalarRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_invariant_coefficient_subspace_inverse]:
    fraction-field finiteness in the classical
    algebra used for 3.4.8(8), pp. 329–330.
    Multiplication is an injective endomorphism
    of the original finite subspace. Its
    surjectivity supplies the inverse of the
    original nonzero multiplier. *)
Theorem finite_invariant_coefficient_subspace_inverse (K L:fieldType) (phi:{rmorphism K->L})
  (S:subspace [the lmodType K of ring_restricted_space phi L^o]) n
  (basis:'I_n->subspace_space S) (hBasis:is_basis basis) (u:L):
  S 1 ->u<>0 ->(forall x:L,S x ->S (u*x)) ->S (u^-1).
Proof.
move=>hOne hNonzero hStable.
pose W:=[the lmodType K of subspace_space S].
pose multiply:=fun x:W=>subspace_lift (hStable (subspace_val x) (subspace_valP x)).
have hLinear:linear multiply.
  move=>a x y;apply:subspace_val_injective.
  change (u*(phi a*subspace_val x+subspace_val y) =
    phi a*(u*subspace_val x)+u*subspace_val y).
  by rewrite mulrDr mulrCA.
pose T:Hom W W:=@HomMap K W W multiply (introT (asboolP _) hLinear).
have hU:u!=0 by apply/eqP;exact:hNonzero.
have hInjective:injective (hom_as_linear T).
  move=>x y hEqual;apply:subspace_val_injective.
  have hProduct:=congr1 (@subspace_val K _ S) hEqual.
  change (u*subspace_val x = u*subspace_val y) in hProduct.
  exact:(mulfI hU hProduct).
have [v hV]:=finite_injective_surjective hBasis hInjective (subspace_lift hOne).
have hProduct:=congr1 (@subspace_val K _ S) hV.
change (u*subspace_val v = 1) in hProduct.
have hInverse:subspace_val v = u^-1.
  apply:(mulfI hU);by rewrite hProduct mulfV.
have hIn:=subspace_valP v;by rewrite hInverse in hIn.
Qed.
