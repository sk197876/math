(** Federer (1969), 1.7.9, p. 35: existence of the bilinear tensor form with
    the prescribed pure-tensor values. This private existence proof uses two
    applications of the tensor universal property; later results take only
    the defining laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP TensorProduct TensorBilinear Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [tensor_inner_bilinear_exists]: Federer 1.7.9,
    p. 35, supporting existence of the characterising bilinear
    function, before its positive definiteness is established.
    This purely algebraic part works over any field. *)
Theorem tensor_inner_bilinear_exists (R : fieldType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : @bilinear R V V R^o B) (hC : @bilinear R W W R^o C) :
  exists D : tensor_space V W -> tensor_space V W -> R,
    @bilinear R _ _ R^o D /\ forall v w v' w',
      D (tensor_inj v w) (tensor_inj v' w') = B v v' * C w w'.
Proof.
pose h := fun v w v' w' => B v v' * C w w'.
have hab v' w' : @bilinear R V W R^o (fun v w => h v w v' w').
  split.
  - move=> w a v z; rewrite /h (proj1 hB v').
    change ((a * B v v' + B z v') * C w w' = a * (B v v' * C w w') + B z v' * C w w').
    by rewrite mulrDl mulrA.
  - move=> v a w z; rewrite /h (proj1 hC w').
    change (B v v' * (a * C w w' + C z w') = a * (B v v' * C w w') + B v v' * C z w').
    by rewrite mulrDr mulrCA.
have hcd v w : @bilinear R V W R^o (h v w).
  split.
  - move=> w' a v' z; rewrite /h (proj2 hB v).
    change ((a * B v v' + B v z) * C w w' = a * (B v v' * C w w') + B v z * C w w').
    by rewrite mulrDl mulrA.
  - move=> v' a w' z; rewrite /h (proj2 hC w).
    change (B v v' * (a * C w w' + C w z) = a * (B v v' * C w w') + B v v' * C w z).
    by rewrite mulrDr mulrCA.
exists (@tensor_bilinear_extension R V W V W R^o h hab hcd); split.
- exact: tensor_bilinear_extension_bilinear.
- move=> v w v' w'; exact (@tensor_bilinear_extensionE R V W V W R^o h hab hcd v w v' w').
Qed.
