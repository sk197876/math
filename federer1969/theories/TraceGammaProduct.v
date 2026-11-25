(** Federer (1969), 1.7.12, pp. 36-37: the degree-two trace coefficient,
    extended bilinearly from rank-one maps using the Hom-tensor
    identification in 1.4.5, pp. 20-21. The resulting identity is the
    polarised coefficient needed for the first displayed formula. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TraceTwoRankOne TraceAlgebra TraceDefinition
  TraceCyclic Gamma AlgebraUP AlgebraTensor TensorUP TensorMaps Bilinear
  Hom LinearBasis OneFormIdentification ExteriorPowers AlternatingCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [trace_gamma_product]: Federer 1.7.12,
    pp. 36-37, supporting polarised degree-two identity:
    trace(Gamma(f) Gamma(g)) equals trace(f) trace(g)-trace(f composed
    with g). Taking g=f and applying the divided-power formula
    of 1.4.5 gives the first printed identity. *)
Theorem trace_gamma_product (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) (I : finType) (e : I -> V) (he : is_basis e)
    (f g : Hom V V) :
  trace h2 V (alg_mul (A h2 V V)
    (@Gamma_A K h2 V V I e he f) (@Gamma_A K h2 V V I e he g)) =
  (@trace_Hom K h2 V I e he f : K) * (@trace_Hom K h2 V I e he g : K) -
    @trace_Hom K h2 V I e he (hom_comp f g).
Proof.
pose tr := @trace_Hom K h2 V I e he.
pose G := @Gamma_A K h2 V V I e he.
pose L (u v : Hom V V) := trace h2 V (alg_mul (A h2 V V) (G u) (G v)).
pose H (u v : Hom V V) : K^o := (tr u : K) * (tr v : K) - tr (hom_comp u v).
have hL : bilinear L.
  exact (bilinear_post (trace h2 V) (bilinear_pre G G (alg_bilinear (A h2 V V)))).
have hH : bilinear H.
  split=> [v c u w|u c v w].
  - rewrite /H (linearP tr) (proj1 (@hom_comp_bilinear K V V V)) (linearP tr).
    change ((c * tr u + tr w) * tr v - (c * tr (hom_comp u v) + tr (hom_comp w v)) =
      c * (tr u * tr v - tr (hom_comp u v)) + (tr w * tr v - tr (hom_comp w v))).
    by rewrite mulrDl mulrBr mulrA opprD addrACA.
  - rewrite /H (linearP tr) (proj2 (@hom_comp_bilinear K V V V)) (linearP tr).
    change (tr u * (c * tr v + tr w) - (c * tr (hom_comp u v) + tr (hom_comp u w)) =
      c * (tr u * tr v - tr (hom_comp u v)) + (tr u * tr w - tr (hom_comp u w))).
    by rewrite mulrDr mulrBr mulrCA opprD addrACA.
pose gi := @Gamma_inverse K V V.
have ht : forall s t, L (gi s) (gi t) = H (gi s) (gi t).
  apply (tensor_bilinear_ext (bilinear_pre gi gi hL) (bilinear_pre gi gi hH)) => a v b w.
  rewrite /L /H /gi !Gamma_inverse_pure.
  have hG alpha z : G (rank_one alpha z) =
      A_pure h2 alpha (exterior_first_inclusion V z).
    change (@Gamma_include K h2 V V (@Gamma K V V I e he (rank_one alpha z)) =
      A_pure h2 alpha (exterior_first_inclusion V z)).
    by rewrite Gamma_rank_one Gamma_includeE.
  rewrite !hG trace_two_rank_one rank_one_comp linearZ /tr !trace_Hom_rank_one.
  by [].
have hh := ht (@Gamma K V V I e he f) (@Gamma K V V I e he g).
by rewrite /gi !GammaK in hh.
Qed.
