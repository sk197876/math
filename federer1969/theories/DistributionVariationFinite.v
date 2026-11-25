(** Federer (1969), 4.1.5, pp. 349–350: finite
    original gauge values are exactly finite uniform bounds
    on norm-bounded test evaluations. Positive scaling gives
    the real quantitative bound used in the extension proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP FunctionLatticeUP DistributionVariationUP
  DistributionVariationBasic DistributionVariationScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionVariationFinite.
Variable R:realType.
Variable X:choiceType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable value:Hom E (GRing.Lmodule.clone R (X->Y) _).
Variable S:Hom E R^o.

(** Source for [distribution_variation_finite_iff_bound]: the
    condition ||S||(f)<infinity in Federer 4.1.5, p. 349,
    is equivalent to a finite nonnegative absolute bound for
    all original tests with norm at most f. *)
Theorem distribution_variation_finite_iff_bound f c:
  function_nonnegative f ->is_distribution_variation_value NY value S f c ->
  ((c< +oo)%E <->exists b:R,0<=b /\ forall phi:E,
    (forall x,NY (value phi x)<=f x) ->`|S phi|<=b).
Proof.
move=>hf hC.
have hNonnegative:=@distribution_variation_nonnegative R X Y NY hNY E value S f c hf hC.
case:c hC hNonnegative=>[b| |] hC hNonnegative.
- split.
  + move=>_.
    exists b; split; first by move:hNonnegative; rewrite lee_fin.
    move=>phi hNorm.
    have h:=@distribution_variation_absolute_bound R X Y NY hNY E value S f b%:E hC phi hNorm.
    by rewrite lee_fin in h.
  + move=>_; exact:ltry.
- split.
  + by rewrite ltxx.
  + move=>[b [_ hBound]].
    have hUpper:(+oo<=b%:E)%E.
      apply:(@distribution_variation_least_finite_bound R X Y NY E value S f +oo b hC)=>phi hNorm.
      exact:(le_trans (ler_norm _) (@hBound phi hNorm)).
    by rewrite leye_eq in hUpper.
- by [].
Qed.

(** Source for [distribution_variation_finite_scaled_bound]:
    the real inequality |S(phi)|<=a ||S||(f) for finite
    gauge and norm(phi)<=a f, the quantitative estimate in
    Federer 4.1.5, p. 349. *)
Lemma distribution_variation_finite_scaled_bound f b a:
  is_distribution_variation_value NY value S f b%:E ->0<a ->forall phi:E,
  (forall x,NY (value phi x)<=a*f x) ->`|S phi|<=a*b.
Proof.
move=>hC ha phi hNorm.
have h:=@distribution_variation_scaled_absolute_bound R X Y NY hNY E value S f b%:E a hC ha phi hNorm.
by rewrite -EFinM lee_fin in h.
Qed.
End DistributionVariationFinite.
