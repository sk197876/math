(** Federer (1969), 4.1.6, p. 354: divergence
    is specified by the original Hom/tensor/interior
    composite. The tensor interchange is exactly the
    already proved 1.1.2 map; no coordinate formula
    or divergence identity is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP TensorProduct TensorMaps Bilinear
  HomTensor GrassmannAbbreviations FiniteCoordinates ExteriorGrading Alternating
  OneFormIdentification LeftInterior OneCovectorInterior.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [divergence_tensor_pair_bilinear]: interior
    multiplication induces the original tensor map,
    Federer 4.1.6, p. 354. *)
Lemma divergence_tensor_pair_bilinear (R:realType) (h2:(1+1:R)!=0) n p:
  bilinear (fun (xi:exterior_power (R_n R n) p.+1) (a:Hom (R_n R n) R^o)=>
    positive_one_covector_interior h2 xi (one_form a)).
Proof.
split.
- move=>a; exact:((@positive_one_covector_interior_bilinear R h2 (R_n R n) p).1).
- move=>xi c a b; rewrite (linearP (@one_form R (R_n R n) R^o)).
  exact:((@positive_one_covector_interior_bilinear R h2 (R_n R n) p).2).
Qed.

(** Source for [divergence_tensor_map]: the original
    tensor-to-multivector map induced by contraction,
    Federer 4.1.6, p. 354. *)
Definition divergence_tensor_map (R:realType) (h2:(1+1:R)!=0) n p:
    {linear tensor_space (exterior_power (R_n R n) p.+1) (Hom (R_n R n) R^o)->
      exterior_power (R_n R n) p}:=
  tensor_lift (@divergence_tensor_pair_bilinear R h2 n p).

(** Source for [is_divergence_value]: the first
    displayed composite of Federer 4.1.6,
    p. 354, including its original tensor-factor
    interchange from 1.1.2. Input degree is p+1. *)
Definition is_divergence_value (R:realType) (h2:(1+1:R)!=0) n p
    (L:Hom (R_n R n) (exterior_power (R_n R n) p.+1))
    (b:exterior_power (R_n R n) p):Prop:=
  b=@divergence_tensor_map R h2 n p
    (@tensor_swap R (Hom (R_n R n) R^o) (exterior_power (R_n R n) p.+1) (Hom_tensor (@coordinate_basisP R n) L)).

(** Source for [divergence_value_unique]: the original
    composite specifies one value,
    Federer 4.1.6, p. 354. *)
Lemma divergence_value_unique (R:realType) (h2:(1+1:R)!=0) n p
    (L:Hom (R_n R n) (exterior_power (R_n R n) p.+1))
    (a b:exterior_power (R_n R n) p):
  is_divergence_value h2 L a->is_divergence_value h2 L b->a=b.
Proof. move=>ha hb; exact:(eq_trans ha (esym hb)). Qed.
