(** Federer (1969), 3.4.12, p. 339: equality of original
    Taylor jets determines a complex-valued analytic germ. Expose
    the normed-target connection already used for real scalar
    germs, reusing actual Taylor convergence and norm-limit uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormClassZeroTopology
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialLocal
  NormAnalyticUP NormAnalyticDiagonal NormAnalyticTaylor NormSequenceLimitUnique.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Equality.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Local Notation Z:=(fun m=>@ContinuousMultilinear.space R m X Y NX NY hNX hNY).
Local Notation ev:=(fun m=>@ContinuousMultilinear.evaluation R m X Y NX NY hNX hNY).
Local Notation ZN:=(fun m=>@ContinuousMultilinear.norm R m X Y NX NY hNX hNY).
Local Notation hZ:=(fun m=>@ContinuousMultilinear.laws R m X Y NX NY hNX hNY).

(** Source for [norm_analytic_equal_jets_local]: actual equal
    Taylor jets give equality on one neighbourhood, extending
    the germ separation argument of 3.4.5, p. 319, to
    the original complex-valued functions of 3.4.12, p. 339. *)
Theorem norm_analytic_equal_jets_local (f g:X->Y) a:
  @norm_analytic_at R X Y NX NY hNX hNY setT f a ->
  @norm_analytic_at R X Y NX NY hNX hNY setT g a ->
  (forall m (z w:Z m),has_norm_higher_differential NX ev ZN setT f m a z ->
    has_norm_higher_differential NX ev ZN setT g m a w ->z=w) ->
  exists U:set X,open (U:set (real_norm_metric_space hNX)) /\U a /\forall x,U x ->f x=g x.
Proof.
move=>hf hg hEqual.
have [U [haU [hUT [hClassF [F [hF hLimitF]]]]]]:=
  norm_diagonal_analytic_taylor (norm_analytic_diagonal hf).
have [V [haV [hVT [hClassG [G [hG hLimitG]]]]]]:=
  norm_diagonal_analytic_taylor (norm_analytic_diagonal hg).
have hU x (hx:U x):norm_domain_interior NX U x:=((hClassF 0%N).1 x hx).1.
have hV x (hx:V x):norm_domain_interior NX V x:=((hClassG 0%N).1 x hx).1.
have hCoefficient m:F m=G m.
  apply:(hEqual m).
  - exact:((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
      m setT U f hUT hU a haU (F m)).2 (hF m)).
  - exact:((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ
      m setT V g hVT hV a haV (G m)).2 (hG m)).
exists (U `&` V);split.
- apply:openI.
  + exact:(@norm_class_zero_domain_open R X Y NX NY hNX U f
      (norm_class_continuous (hClassF 0%N))).
  + exact:(@norm_class_zero_domain_open R X Y NX NY hNX V g
      (norm_class_continuous (hClassG 0%N))).
- split;first by split.
  move=>x [hx hy].
  apply:(@norm_sequence_limit_unique R Y NY hNY
    (fun N=>\sum_(m<N.+1) (m`!)%:R^-1*:ev m [ffun _:'I_m=>x-a] (F m))).
  + move=>eps heps;have [n hn]:=hLimitF eps heps.
    exists n=>N hN;rewrite (real_seminorm_subtract hNY.1);exact:hn N hN x hx.
  + move=>eps heps;have [n hn]:=hLimitG eps heps.
    exists n=>N hN;rewrite (real_seminorm_subtract hNY.1).
    have hSum:(\sum_(m<N.+1) (m`!)%:R^-1*:ev m [ffun _:'I_m=>x-a] (F m))=
        \sum_(m<N.+1) (m`!)%:R^-1*:ev m [ffun _:'I_m=>x-a] (G m).
      apply:eq_bigr=>m _;by rewrite hCoefficient.
    rewrite hSum;exact:hn N hN x hy.
Qed.
End Equality.
