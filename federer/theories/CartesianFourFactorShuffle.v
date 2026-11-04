(** Federer (1969), 3.2.48, pp. 285–286: regroup
    (K times S) times (K times T) as
    (K times K) times (S times T). Supporting
    the two independent subtraction blocks in the actual
    differential; the regrouping preserves the Cartesian inner metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom InnerProductUP ProductInner OrthogonalMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [cartesian_four_factor_shuffle]: supporting actual
    regrouping of the four linear factors in 3.2.48,
    pp. 285–286, before applying 1.7.11 twice. *)
Definition cartesian_four_factor_shuffle (R:realType) (A B C D:lmodType R)
    (x:((A*B)*(C*D))%type):((A*C)*(B*D))%type:=
  ((x.1.1,x.2.1),(x.1.2,x.2.2)).

(** Source for [cartesian_four_factor_shuffle_linear]: linearity
    of the actual regrouping supporting 3.2.48,
    pp. 285–286; no scalar field dimension is restricted. *)
Lemma cartesian_four_factor_shuffle_linear (R:realType) (A B C D:lmodType R):
  linear (@cartesian_four_factor_shuffle R A B C D).
Proof. by move=>a [[u v] [w z]] [[u' v'] [w' z']]. Qed.

(** Source for [cartesian_four_factor_shuffle_hom]: supporting
    actual linear regrouping in the tangent diagram of
    3.2.48, p. 285, with its original component values. *)
Definition cartesian_four_factor_shuffle_hom (R:realType) (A B C D:lmodType R):
    Hom [the lmodType R of ((A*B)*(C*D))%type]
      [the lmodType R of ((A*C)*(B*D))%type]:=
  @HomMap R _ _ (@cartesian_four_factor_shuffle R A B C D)
    (introT (asboolP _) (@cartesian_four_factor_shuffle_linear R A B C D)).

(** Source for [cartesian_four_factor_shuffleK]: the second
    regrouping restores all four original factors, supporting
    the actual inverse arrow in 3.2.48, p. 285. *)
Lemma cartesian_four_factor_shuffleK (R:realType) (A B C D:lmodType R):
  cancel (@cartesian_four_factor_shuffle R A B C D) (@cartesian_four_factor_shuffle R A C B D).
Proof. by move=>[[u v] [w z]]. Qed.

(** Source for [cartesian_four_factor_shuffle_orthogonal]: regrouping
    is an actual isometry for the specified Cartesian
    inner products, supporting both Jacobian blocks in
    3.2.48, p. 286. All zero spaces remain. *)
Lemma cartesian_four_factor_shuffle_orthogonal (R:realType) (A B C D:lmodType R)
    BA BB BC BD (hA:@is_inner_product R A BA) (hB:@is_inner_product R B BB)
    (hC:@is_inner_product R C BC) (hD:@is_inner_product R D BD):
  is_orthogonal_map
    (product_inner (product_inner_productP hA hB) (product_inner_productP hC hD))
    (product_inner (product_inner_productP hA hC) (product_inner_productP hB hD))
    (hom_as_linear (@cartesian_four_factor_shuffle_hom R A B C D)).
Proof.
move=>[[u v] [w z]] [[u' v'] [w' z']].
change (product_inner (product_inner_productP hA hC) (product_inner_productP hB hD)
  ((u,w),(v,z)) ((u',w'),(v',z'))=
  product_inner (product_inner_productP hA hB) (product_inner_productP hC hD)
  ((u,v),(w,z)) ((u',v'),(w',z'))).
by rewrite !product_innerE addrACA.
Qed.
