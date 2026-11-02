(** Federer (1969), 3.1.11, p. 220:
    exact equivalence between higher differentials on
    the real line and recursively defined ordinary derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialScalar
  NormDifferentialFiniteCalculus NormedCurveDerivativeUP ContinuousMultilinearUP
  ContinuousMultilinearZero ContinuousMultilinearScalar NormHigherDifferentialUP
  NormDifferentialIsometricEvaluation NormHigherCurveDerivativeUP
  MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section RealSource.
Variable R : realType.
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->R^o}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space
  (fun t : R^o=>`|t|) NY (@evaluation k) (@ZN k).
Variable A : R->Prop.
Variable f : R->Y.
Local Notation HD := (has_norm_higher_differential (fun t : R^o=>`|t|)
  evaluation ZN A f).
Local Notation HC := (has_norm_higher_curve_derivative NY A f).
Local Notation ones k := ([ffun i : 'I_k=>(1:R^o)]).

(** Source for [norm_higher_differential_real_source]:
    f is k times differentiable if and only if its
    kth ordinary derivative exists, with the stated
    coefficient identification, Federer 3.1.11, p. 220.
    The equivalence is pointwise and uses the exact
    preceding domains on both sides. *)
Theorem norm_higher_differential_real_source k a (z : Z k) :
  HD k a z <-> HC k a (@evaluation k (ones k) z).
Proof.
elim: k a z=> [a z|k ih a z].
- change ((A a /\ @evaluation 0%N [ffun i : 'I_0=>(0:R^o)] z=f a)<->
    (A a /\ @evaluation 0%N (ones 0%N) z=f a)).
  by rewrite (zero_arity_arguments_unique [ffun i : 'I_0=>(0:R^o)] (ones 0%N)).
- have hdom x : (exists w, HD k x w)<->exists v, HC k x v.
    split.
    + move=> [w hw]; exists (@evaluation k (ones k) w); exact: (ih x w).1 hw.
    + move=> [v hv].
      have [w hw] := @continuous_multilinear_scalar_surjective R k Y (Z k)
        NY hNY (@evaluation k) (@ZN k) (@hZ k) v.
      exists w; apply: (ih x w).2; by rewrite hw.
  split.
  + move=> [g [hg [L [hL he]]]].
    pose q x := @evaluation k (ones k) (g x).
    exists q; split.
    * move=> x v hv.
      have [w hw] := @continuous_multilinear_scalar_surjective R k Y (Z k)
        NY hNY (@evaluation k) (@ZN k) (@hZ k) v.
      have hDw : HD k x w by apply: (ih x w).2; rewrite hw.
      by rewrite /q (hg x w hDw) hw.
    * split.
      -- have [r [hr hball]] := norm_differential_interior hL.
         exists r; split=> // h hh; exact: (hdom _).1 (hball h hh).
      -- have heval := (@norm_differential_isometric_evaluation R R^o (Z k) Y
           (fun t : R^o=>`|t|) (@ZN k) NY (@evaluation k (ones k))
           (continuous_multilinear_scalar_norm hNY (@hZ k))
           (fun x=>exists w, HD k x w) g a L).1 hL.
         have hh := (@norm_differential_real_source R Y NY hNY
           (fun x=>exists w, HD k x w) q a
           (hom_comp (@evaluation k (ones k)) L)).1 heval.
         have hcoeff : (hom_comp (@evaluation k (ones k)) L) 1=
             @evaluation k.+1 (ones k.+1) z.
           by rewrite hom_compE he multilinear_successor_constant_arguments.
         rewrite hcoeff in hh; exact: hh.2.
  + move=> [q [hq [hint hcurve]]].
    have [J [hJ [hJinv hJN]]] := @continuous_multilinear_scalar_identification
      R k Y (Z k) NY hNY (@evaluation k) (@ZN k) (@hZ k).
    pose g x := J (q x).
    pose v := @evaluation k.+1 (ones k.+1) z.
    pose M := scalar_coefficient_linear_map v.
    have hiD : norm_domain_interior (fun t : R^o=>`|t|)
        (fun x=>exists w, HD k x w) a.
      have [r [hr hball]] := hint.
      exists r; split=> // h hh; exact: (hdom _).2 (hball h hh).
    have hqD : has_norm_differential (fun t : R^o=>`|t|) NY
        (fun x=>exists w, HD k x w) q a M.
      apply: (@norm_differential_real_source R Y NY hNY
        (fun x=>exists w, HD k x w) q a M).2; split; first exact hiD.
      change (has_normed_curve_derivative NY q a (1*:v)).
      by rewrite scale1r.
    have hJb : norm_bounded_linear NY (@ZN k) J.
      exists 1; split; first exact: ler01.
      by move=> y; rewrite hJN mul1r.
    exists g; split.
    * move=> x w hw; rewrite /g (hq x _ ((ih x w).1 hw)).
      exact: hJinv.
    * exists (hom_comp J M); split.
      -- exact (norm_differential_postcompose (@scalar_absolute_value_norm R) hqD hJb).
      -- move=> u t; rewrite hom_compE
           (continuous_multilinear_scalar_evaluation (@hZ k)) hJ.
         change ((\prod_(i<k) u i)*:(t*:v)=
           @evaluation k.+1 (multilinear_successor_arguments u t) z).
         by rewrite (continuous_multilinear_scalar_evaluation (@hZ k.+1))
           multilinear_successor_product scalerA.
Qed.

(** Source for [norm_higher_curve_derivative_exists]:
    the existence version of the real-source equivalence
    in Federer 3.1.11, p. 220, without
    a restriction on the dimension of the target. *)
Corollary norm_higher_curve_derivative_exists k a :
  (exists z, HD k a z)<->exists v, HC k a v.
Proof.
split.
- move=> [z hz]; exists (@evaluation k (ones k) z).
  exact: (@norm_higher_differential_real_source k a z).1 hz.
- move=> [v hv].
  have [z hz] := @continuous_multilinear_scalar_surjective R k Y (Z k)
    NY hNY (@evaluation k) (@ZN k) (@hZ k) v.
  exists z; apply: (@norm_higher_differential_real_source k a z).2.
  by rewrite hz.
Qed.
End RealSource.
