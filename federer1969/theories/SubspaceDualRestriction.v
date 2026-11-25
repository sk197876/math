(** Supporting dual restriction and norm-preserving lifts for the
    closed-subspace reflexivity assertion in Federer (1969), 2.9.22, p. 167.
    Existence follows from the abstract dual specifications; surjectivity
    follows from the proved Hahn–Banach theorem, 2.4.12, pp. 86–87. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier LinearRetraction
  RealNormUP NormedSubspace RealFunctionalNormUP ContinuousRealFunctional
  ContinuousDualUP SubspaceDualRestrictionUP SubspaceFunctionalExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Restriction.
Variable R : realType.
Variables E D F : lmodType R.
Variable N : E -> R.
Hypothesis hN : is_real_norm N.
Variable Z : subspace E.
Variable ed : Hom D (Hom E R^o).
Variable DN : D -> R.
Hypothesis hD : is_continuous_dual hN ed DN.
Variable ef : Hom F (Hom (subspace_space Z) R^o).
Variable FN : F -> R.
Hypothesis hF : is_continuous_dual (subspace_norm_laws hN Z) ef FN.

(** Source for [subspace_dual_restriction_exists]: supporting
    existence of dual restriction in Federer 2.9.22, p. 167.
    Precompose each ambient functional with linear inclusion;
    the abstract subspace dual represents that continuous map.
    A linear retraction of its evaluation map gives linearity
    without exposing the dual's carrier implementation. *)
Theorem subspace_dual_restriction_exists : exists r : Hom D F,
  is_subspace_dual_restriction Z ed ef DN FN r.
Proof.
pose i := hom_of_linear (@subspace_inclusion R E Z).
have hlin : linear (fun a : D => hom_comp (ed a) i).
  move=> c a b; apply: hom_ext=> z.
  rewrite hom_addE hom_scaleE !hom_compE linearP.
  by rewrite hom_addE hom_scaleE.
pose T := @HomMap R D (Hom (subspace_space Z) R^o)
  (fun a => hom_comp (ed a) i) (introT (asboolP _) hlin).
pose q := linear_retraction (i:=hom_as_linear ef) (continuous_dual_injective hF).
pose r := hom_comp (hom_of_linear q) T.
have he a : ef (r a)=T a.
  have hc : is_continuous_real_functional (subspace_norm_laws hN Z)
      (hom_as_linear (T a)).
    apply: (@bounded_real_functional_continuous R
      [the lmodType R of subspace_space Z] (subspace_norm N Z)
      (subspace_norm_laws hN Z) (hom_as_linear (T a)) (DN a)
      (real_functional_norm_nonnegative (continuous_dual_norm_laws hD a))).
    move=> z; change (`|ed a (subspace_val z)|<=DN a * N (subspace_val z)).
    exact: real_functional_norm_bound (continuous_dual_norm_laws hD a) _.
  have [b hb] := continuous_dual_surjective hF hc.
  change (ef (q (T a))=T a).
  by rewrite -hb /q linear_retractionK hb.
exists r; constructor.
- move=> a z; rewrite he; by [].
- move=> a; apply: (real_functional_norm_least (continuous_dual_norm_laws hF (r a))
    (real_functional_norm_nonnegative (continuous_dual_norm_laws hD a))).
  move=> z; rewrite hom_as_linearE he.
  change (`|ed a (subspace_val z)|<=DN a * N (subspace_val z)).
  exact: real_functional_norm_bound (continuous_dual_norm_laws hD a) _.
Qed.

(** Source for [subspace_dual_restriction_norm_lift]: supporting
    surjectivity with preserved norm for the restriction map
    used in Federer 2.9.22, p. 167. Hahn–Banach, 2.4.12,
    p. 86, extends each subspace functional with its exact
    dual norm bound; restriction's opposite inequality then
    proves equality of norms. Closedness of the subspace is
    unnecessary for this lifting statement. *)
Theorem subspace_dual_restriction_norm_lift (r : Hom D F) :
  is_subspace_dual_restriction Z ed ef DN FN r ->
  forall b : F, exists a : D, r a=b /\ DN a=FN b.
Proof.
move=> hr b.
have hnorm := continuous_dual_norm_laws hF b.
have [f [hext [hbound hc]]] := @bounded_subspace_functional_extension R E N hN Z
  (hom_as_linear (ef b)) (FN b) (real_functional_norm_nonnegative hnorm)
  (real_functional_norm_bound hnorm).
have [a ha] := continuous_dual_surjective hD (a:=hom_of_linear f) hc.
have he : r a=b.
  apply: (continuous_dual_injective hF); apply: hom_ext=> z.
  rewrite (subspace_dual_restriction_evaluation hr) ha hom_of_linearE hext.
  by rewrite hom_as_linearE.
have hupper : DN a<=FN b.
  apply: (real_functional_norm_least (continuous_dual_norm_laws hD a)
    (real_functional_norm_nonnegative hnorm)).
  by move=> y; rewrite hom_as_linearE ha hom_of_linearE; exact: hbound.
exists a; split=> //; apply/le_anti/andP; split=> //.
have hh := subspace_dual_restriction_bound hr a; by rewrite he in hh.
Qed.

End Restriction.
