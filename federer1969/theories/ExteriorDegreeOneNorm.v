(** Federer (1969), 3.2.13, p. 251: degree-one exterior
    projection norms are ordinary vector norms, by 1.3.1, p. 13,
    and 1.7.5, pp. 31–32. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP InnerNorm ExteriorNorm ExteriorPowers InnerExteriorLowDegrees
  InteriorOneDegree ExteriorGrading GradedComponents FiniteExteriorPowers ExteriorAlgebra ExteriorMaps ExteriorMapNormContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_first_norm]: the degree-one norm
    agrees with the vector norm, 1.7.5, pp. 31–32,
    used to identify q(g C) in Federer 3.2.13, p. 251. *)
Lemma exterior_first_norm (R:rcfType) (h2:(1+1:R)!=0) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (v:V):
  exterior_norm h2 hB (exterior_first_inclusion V v)=inner_norm hB v.
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
by rewrite inner_norm_sqr exterior_inner_first.
Qed.

(** Source for [exterior_first_word]: the exterior inclusion
    of one vector is its one-term exterior word, 1.3.1,
    p. 13, used in Federer 3.2.13, p. 251. *)
Lemma exterior_first_word (K:fieldType) (V:lmodType K) (v:V):
  exterior_first_inclusion V v=e_lambda (@idfun V) [tuple v].
Proof.
apply:val_inj; change (component_val (exterior_first_inclusion V v)=
  component_val (e_lambda (@idfun V) [tuple v])).
by rewrite first_inclusion_val e_lambdaE /= exterior_word_cons exterior_word_nil wedge_unitr.
Qed.

(** Source for [exterior_map_first_inclusion]: degree-one
    exterior naturality is the original linear map, 1.3.1,
    p. 14, used in the projection calculation of Federer 3.2.13, p. 251. *)
Lemma exterior_map_first_inclusion (K:fieldType) (V W:lmodType K)
    (f:{linear V->W}) (v:V):
  exterior_power_map f 1 (exterior_first_inclusion V v)=exterior_first_inclusion W (f v).
Proof.
rewrite !exterior_first_word exterior_power_map_e_lambda.
apply:val_inj; change (component_val (e_lambda (fun x=>f x) [tuple v])=
  component_val (e_lambda (@idfun W) [tuple f v])).
by rewrite !e_lambdaE /=.
Qed.
