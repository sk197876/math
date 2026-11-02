(** Federer (1969), 3.1.11, p. 223: the coordinate
    class criterion on Euclidean space, for an arbitrary normed target. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  NormClassOneLaws GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness SymmetricMultiIndices
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearZero
  ContinuousMultilinearSealed ContinuousMultilinearEvaluationBound
  NormHigherDifferentialUP NormHigherMultiPartialUP NormHigherCoordinateReconstruction
  NormClassHigherUP NormClassHigherLaws NormClassHigherFirst NormClassHigherDerivative
  NormClassHigherFromDerivative NormClassOneFiniteAssembly.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CoordinateClasses.
Variable R : realType.
Variable n : nat.
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Let hNX := inner_norm_real_norm (@euclidean_inner_productP R n).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variables (A : X->Prop) (f : X->Y).

(** Source for [norm_multi_partial_class_one]: if f is of
    class k, D^alpha f is of class one for every
    multiindex of degree less than k, Federer 3.1.11,
    p. 223. Values are specified on the original domain. *)
Theorem norm_multi_partial_class_one k j (alpha : symmetric_indices n j) :
  (j<k)%N -> norm_class_higher NX NY ev ZN A f k ->
  exists g : X->Y,
    (forall a, A a -> has_norm_multi_partial NX ev ZN A f alpha a (g a)) /\
    norm_class_one NX NY A g.
Proof.
move=>hjk hk.
have hjk0 : (j<=k)%N := ltnW hjk.
have [_ [G [hG hcG]]] := @norm_class_higher_lower R X Y NX NY hNX hNY
  Z ev ZN hZ A f k j hjk0 hk.
have hNj := continuous_multilinear_norm_is_norm hNY (@hZ j).
pose W i := @ContinuousMultilinear.space R i X (Z j) NX (@ZN j) hNX hNj.
pose ew i := @ContinuousMultilinear.evaluation R i X (Z j) NX (@ZN j) hNX hNj.
pose WN i := @ContinuousMultilinear.norm R i X (Z j) NX (@ZN j) hNX hNj.
pose hW i := @ContinuousMultilinear.laws R i X (Z j) NX (@ZN j) hNX hNj.
have hj1 : norm_class_higher NX NY ev ZN A f (j+1)%N.
  rewrite addn1; exact (@norm_class_higher_lower R X Y NX NY hNX hNY
    Z ev ZN hZ A f k j.+1 hjk hk).
have hc := @norm_class_higher_derivative_field R j 1%N X Y NX NY hNX hNY
  Z ev ZN hZ W ew WN hW A f G hj1 hG.
have hone := (@norm_class_higher_first R X (Z j) NX (@ZN j) hNX hNj
  W ew WN hW A G).1 hc.
pose L := @ev j (norm_multi_partial_arguments R alpha).
exists (fun a=>L (G a)); split.
- move=>a ha; exists (G a); by split; first exact: hG a ha.
- exact (norm_class_one_bounded_postcompose hNX hNj hNY
    (continuous_multilinear_evaluation_bounded hNX (@hZ j)
      (norm_multi_partial_arguments R alpha)) hone).
Qed.

(** Source for [norm_multi_partial_zero_value]: the unique
    degree-zero partial is f itself, the convention used in
    the last equivalence of Federer 3.1.11, p. 223. *)
Lemma norm_multi_partial_zero_value (alpha : symmetric_indices n 0) a y :
  has_norm_multi_partial NX ev ZN A f alpha a y -> y=f a.
Proof.
move=>[z [[ha he] <-]].
by rewrite (@zero_arity_arguments_unique X (norm_multi_partial_arguments R alpha)
  [ffun i : 'I_0=>(0:X)]) he.
Qed.

(** Source for [norm_multi_partial_class_criterion]: f is
    of class k+1 if and only if all its partials of
    orders at most k are of class one, Federer 3.1.11,
    p. 223. Degree zero is included. The proof reconstructs
    the actual derivative field by finite bounded linear sums;
    it requires neither completeness nor finite dimension of Y. *)
Theorem norm_multi_partial_class_criterion k :
  norm_class_higher NX NY ev ZN A f k.+1 <->
  forall j, (j<=k)%N -> forall alpha : symmetric_indices n j,
    exists g : X->Y,
      (forall a, A a -> has_norm_multi_partial NX ev ZN A f alpha a (g a)) /\
      norm_class_one NX NY A g.
Proof.
split.
- move=>hk j hj alpha; apply: (@norm_multi_partial_class_one k.+1 j alpha _ hk).
  by rewrite ltnS.
- elim:k=>[|k IH] hp.
  + have hz : (\sum_(i<n) val ([ffun _ : 'I_n=>(ord0 : 'I_1)] i))%N==0%N.
      apply/eqP; apply: big1=>i _; by rewrite ffunE.
    pose alpha : symmetric_indices n 0 := Sub [ffun _ : 'I_n=>(ord0 : 'I_1)] hz.
    have [g [hg hc]] := hp 0%N (leqnn 0) alpha.
    apply: (@norm_class_higher_first R X Y NX NY hNX hNY Z ev ZN hZ A f).2.
    apply: (norm_class_one_domain_agreement hNX hNY _ hc)=>a ha.
    exact (norm_multi_partial_zero_value (hg a ha)).
  + have hk : norm_class_higher NX NY ev ZN A f k.+1.
      apply: IH=>j hj; exact (hp j (leq_trans hj (leqnSn k))).
    have [hf [G [hG hcG]]] := hk.
    have hNk := continuous_multilinear_norm_is_norm hNY (@hZ k.+1).
    have [L [hL hrec]] := @norm_higher_coordinate_reconstruction_exists R n Y NY hNY
      Z ev ZN hZ k.+1.
    have [g hg] := choice (hp k.+1 (leqnn k.+1)).
    have hopen a (ha : A a) : norm_domain_interior NX A a := (hf a ha).1.
    have hs : norm_class_one NX (@ZN k.+1) A
        (fun x=>\sum_alpha L alpha (g alpha x)).
      apply: (@norm_class_one_finite_sum R X (Z k.+1) NX (@ZN k.+1)
        hNX hNk A hopen (Finite.clone (symmetric_indices n k.+1) _)
        (fun alpha x=>L alpha (g alpha x))).
      move=>alpha; exact (norm_class_one_bounded_postcompose hNX hNY hNk
        (hL alpha) (hg alpha).2).
    have hone : norm_class_one NX (@ZN k.+1) A G.
      apply: (norm_class_one_domain_agreement hNX hNk _ hs)=>a ha.
      symmetry; apply: (hrec A f a (G a) (fun alpha=>g alpha a) (hG a ha))=>alpha.
      exact: (hg alpha).1 a ha.
    pose W i := @ContinuousMultilinear.space R i X (Z k.+1) NX (@ZN k.+1) hNX hNk.
    pose ew i := @ContinuousMultilinear.evaluation R i X (Z k.+1) NX (@ZN k.+1) hNX hNk.
    pose WN i := @ContinuousMultilinear.norm R i X (Z k.+1) NX (@ZN k.+1) hNX hNk.
    pose hW i := @ContinuousMultilinear.laws R i X (Z k.+1) NX (@ZN k.+1) hNX hNk.
    have hc := (@norm_class_higher_first R X (Z k.+1) NX (@ZN k.+1) hNX hNk
      W ew WN hW A G).2 hone.
    rewrite -addn1.
    exact (@norm_class_higher_from_derivative_field R k.+1 1%N X Y NX NY hNX hNY
      Z ev ZN hZ W ew WN hW A f G hf hG hc).
Qed.
End CoordinateClasses.
