(** Federer (1969), 1.7.9, p. 35: existence of the specified inner product
    on Hom(V,W). This witness remains behind the sealed public interface. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerDual TensorInner Hom Gamma
  LinearBasis HomInnerUP InnerProductPullback.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [hom_inner_exists]: Federer 1.7.9, p. 35,
    Gamma identifies Hom(V,W) with the tensor space of the dual
    of V and W, and hence transfers its inner product. *)
Theorem hom_inner_exists (R : rcfType) (V W : lmodType R)
    (B : V -> V -> R) (C : W -> W -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) :
  exists D, is_hom_inner_product hB hC he D.
Proof.
exists (fun f g => tensor_inner (inner_dual_productP hB he) hC
  (@Gamma R V W (Finite.clone 'I_n _) e he f) (@Gamma R V W (Finite.clone 'I_n _) e he g)).
constructor; last by [].
exact (@inner_product_linear_pullback R (Hom V W) _
  (tensor_inner (inner_dual_productP hB he) hC)
  (tensor_inner_productP (inner_dual_productP hB he) hC)
  (@Gamma R V W (Finite.clone 'I_n _) e he)
  (can_inj (@GammaK R V W (Finite.clone 'I_n _) e he))).
Qed.
