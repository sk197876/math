(** Public infinite product for Federer (1969), 2.6.6, p. 120. The
    implementation is sealed and uniqueness is obtained from uniform density
    of finite-coordinate functions. Source context:
    CompactProductFiniteControl.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import CompactSupportFunctionUP MonotoneDaniellIntegralUP NormalizedProductSpace
  InfiniteDaniellProductUP InfiniteDaniellProductSealed CylinderDaniellExtensionUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [infinite_daniell_product]: the product integral
    in Federer 2.6.6, p. 120, specified by its finite marginals. *)
Definition infinite_daniell_product (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) := @InfiniteDaniellProduct.value R I Y A hh hc hA hA1.

(** Source for [infinite_daniell_product_specification]: the
    normalized Daniell and finite-marginal laws, Federer 2.6.6, p. 120. *)
Lemma infinite_daniell_product_specification (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) :
  is_infinite_daniell_product hh hc hA hA1 (@infinite_daniell_product R I Y A hh hc hA hA1).
Proof. exact: (@InfiniteDaniellProduct.laws R I Y A hh hc hA hA1). Qed.

(** Source for [infinite_daniell_product_unique]: the uniqueness
    characterization in Federer 2.6.6, p. 120, on K(X).
    Ambient values outside K(X) are immaterial. *)
Theorem infinite_daniell_product_unique (R : realType) (I : choiceType) (Y : I -> topologicalType)
  (A : forall i, (Y i -> R) -> R)
  (hh : forall i, hausdorff_space (Y i)) (hc : forall i, compact (@setT (Y i)))
  (hA : forall i, is_monotone_daniell_integral (@compactly_supported_continuous_functions R (Y i)) (A i))
  (hA1 : forall i, A i (fun _=>1) = 1) (B C : (prod_topology Y -> R) -> R) :
  is_infinite_daniell_product hh hc hA hA1 B -> is_infinite_daniell_product hh hc hA hA1 C ->
  forall f, compactly_supported_continuous_functions f -> B f=C f.
Proof.
move=> hB hC; have [x0 _] := normalized_daniell_product_nonempty hA hA1.
exact: (@cylinder_daniell_extension_unique R I Y x0 _ B C (compact_factor_product_compact hc) hB hC).
Qed.
