(** Federer (1969), 2.9.22, p. 167: "every closed subspace of a reflexive
    space is reflexive". This supporting theorem proves the assertion
    through abstract continuous duals and biduals. Hahn–Banach extension and
    closed-subspace separation are derived from 2.4.12, pp. 86–87. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier RealNormUP NormMetric NormedSubspace
  RealFunctionalNormUP ContinuousRealFunctional ContinuousDualUP ContinuousDualNorm ContinuousBidualUP
  SubspaceDualRestrictionUP SubspaceDualRestriction ClosedSubspaceFunctionalSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [closed_subspace_reflexive]: direct supporting
    closed-subspace assertion in Federer 2.9.22, p. 167.
    Restriction of duals transposes a subspace bidual vector
    into the ambient bidual. Reflexivity represents it by y;
    Hahn–Banach separation forces y into the closed subspace.
    Every subspace functional lifts by the proved extension
    theorem, identifying the original subspace bidual vector.
    All spaces and pairings remain abstract and may have
    arbitrary dimension. *)
Theorem closed_subspace_reflexive (R : realType) (E D B F U : lmodType R)
    (N : E -> R) (hN : is_real_norm N) (Z : subspace E)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN)
    (eb : Hom B (Hom D R^o)) (BN : B -> R)
    (hB : is_continuous_dual (continuous_dual_norm_is_norm hD) eb BN)
    (tau : Hom E B)
    (ef : Hom F (Hom (subspace_space Z) R^o)) (FN : F -> R)
    (hF : is_continuous_dual (subspace_norm_laws hN Z) ef FN)
    (eu : Hom U (Hom F R^o)) (UN : U -> R)
    (hU : is_continuous_dual (continuous_dual_norm_is_norm hF) eu UN)
    (sigma : Hom (subspace_space Z) U) :
  is_bidual_embedding ed eb tau -> is_reflexive_embedding tau ->
  closed (fun y : real_norm_metric_space hN => Z y) ->
  is_bidual_embedding ef eu sigma -> is_reflexive_embedding sigma.
Proof.
move=> ht hr hZ hs u.
have [r hrestr] := @subspace_dual_restriction_exists R E D F N hN Z ed DN hD ef FN hF.
pose f := hom_comp (eu u) r.
have hUn : 0<=UN u := real_functional_norm_nonnegative (continuous_dual_norm_laws hU u).
have hbound a : `|f a|<=UN u * DN a.
  rewrite /f hom_compE.
  have hh := real_functional_norm_bound (continuous_dual_norm_laws hU u) (r a).
  exact: le_trans hh (ler_wpM2l hUn (subspace_dual_restriction_bound hrestr a)).
have hc : is_continuous_real_functional (continuous_dual_norm_is_norm hD) (hom_as_linear f).
  exact (@bounded_real_functional_continuous R D DN (continuous_dual_norm_is_norm hD)
    (hom_as_linear f) (UN u) hUn hbound).
have [b hb] := continuous_dual_surjective hB hc.
have [y hy] := hr b.
have heval a : ed a y=eu u (r a).
  by rewrite -(ht y a) hy hb hom_compE.
have hyZ : Z y.
  apply: contrapT=> hn.
  have [alpha [halpha [hzero hpos]]] := @closed_subspace_continuous_separation R E N hN Z y hZ hn.
  have [a ha] := continuous_dual_surjective hD (a:=hom_of_linear alpha) halpha.
  have hra : r a=0.
    apply: (continuous_dual_injective hF); apply: hom_ext=> z.
    rewrite (subspace_dual_restriction_evaluation hrestr) ha hom_of_linearE linear0.
    change (alpha (subspace_val z)=0).
    exact: hzero _ (subspace_valP z).
  have hz := heval a.
  rewrite ha hom_of_linearE hra linear0 in hz.
  by rewrite hz ltxx in hpos.
pose w := @subspace_lift R E Z y hyZ.
exists w; apply: (continuous_dual_injective hU); apply: hom_ext=> beta.
have [a [ha _]] := @subspace_dual_restriction_norm_lift R E D F N hN Z ed DN hD ef FN hF r hrestr beta.
rewrite hs -ha (subspace_dual_restriction_evaluation hrestr).
change (ed a y=eu u (r a)).
exact: heval.
Qed.
