(** Federer (1969), 4.1.1, p. 346: the
    scalar pairing of a test with a dual field
    obeys the bilinear product rule. Boundedness
    follows from the original abstract dual norm;
    no carrier construction is unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP ContinuousDualUP ContinuousDualNorm
  NormBoundedBilinearUP NormRegularity NormRegularityBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section DualEvaluationBilinear.
Variable R:realType.
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable D:lmodType R.
Variable ed:Hom D (Hom Y R^o).
Variable DN:D->R.
Hypothesis hD:is_continuous_dual hNY ed DN.

(** Source for [norm_dual_evaluation_bounded_bilinear]:
    the pairing has norm bound ||y|| ||alpha||,
    supporting the C1 product identity in
    Federer 4.1.1, p. 346. *)
Theorem norm_dual_evaluation_bounded_bilinear:
  norm_bounded_bilinear NY DN (fun t:R^o=>`|t|) (fun y a=>ed a y).
Proof.
split.
- split.
  + move=>a c y z; exact:(hom_linear (ed a) c y z).
  + move=>y c a b.
    have h:=congr1 (fun F:Hom Y R^o=>F y) (hom_linear ed c a b).
    exact h.
- exists 1; split; first exact:ler01.
  move=>y a; rewrite mul1r (mulrC (NY y) (DN a)).
  exact:(real_functional_norm_bound (continuous_dual_norm_laws hD a) y).
Qed.

(** Source for [norm_class_dual_pairing]: a Ck vector
    function paired with a Ck dual field is
    a Ck scalar function, supporting the C1
    product argument in Federer 4.1.1, p. 346. *)
Theorem norm_class_dual_pairing (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    (U:X->Prop) (f:X->Y) (g:X->D) k:
  norm_class hNX hNY U f k ->
  norm_class hNX (continuous_dual_norm_is_norm hD) U g k ->
  norm_class hNX (@scalar_absolute_value_norm R) U (fun x=>ed (g x) (f x)) k.
Proof. exact:norm_class_bilinear norm_dual_evaluation_bounded_bilinear. Qed.
End DualEvaluationBilinear.
