(** Federer (1969), 3.1.24, p. 240: analytic
    sums and constant scalar multiples, supporting the displayed
    formula for the inverse of the scalar majorant. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearNorm NormRegularity NormRegularityOperations NormHigherDifferentialUP
  NormHigherDifferentialLocal NormHigherDifferentialArithmetic NormHigherDifferentialUnique NormLinearDomainLaws
  NormAnalyticUP NormSmoothFields NormAnalyticBoundNonnegative AnalyticArithmeticBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_at_add]: supporting the sum
    of analytic terms in the quadratic scalar inverse formula,
    Federer 3.1.24, p. 240. Intersect the two
    actual analytic neighbourhoods; the sum of the derivative
    bounds c^m m! and d^m m! is at most
    (c+d)^m m! in every positive order. *)
Theorem norm_analytic_at_add (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A B:set X) (f g:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY B g a ->
  @norm_analytic_at R X Y NX NY hNX hNY (fun x=>A x /\ B x) (fun x=>f x+g x) a.
Proof.
move=>[U [c [ha [hUA [hf hbF]]]]] [V [d [hga [hVB [hg hbG]]]]].
have hc:=norm_analytic_operator_witness_nonnegative ha hf hbF.
have hd:=norm_analytic_operator_witness_nonnegative hga hg hbG.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have [F hF]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY U f hf.
have [G hG]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY V g hg.
pose C:=fun x=>U x /\ V x.
have hopen x (hx:C x):NormDifferentialUP.norm_domain_interior NX C x.
  exact (norm_domain_intersection_interior ((hf 0%N).1 x hx.1).1 ((hg 0%N).1 x hx.2).1).
have hfC k:norm_class hNX hNY C f k.
  exact (@norm_class_open_restriction R X Y NX NY hNX hNY U C f k (fun x hx=>hx.1) hopen (hf k)).
have hgC k:norm_class hNX hNY C g k.
  exact (@norm_class_open_restriction R X Y NX NY hNX hNY V C g k (fun x hx=>hx.2) hopen (hg k)).
exists C,(c+d); split; first by split.
split; first by move=>x hx; split; [exact (hUA x hx.1)|exact (hVB x hx.2)].
split.
- move=>k; exact (@norm_class_add R X Y NX NY hNX hNY C f g k (hfC k) (hgC k)).
- move=>m hm x hx z hz.
  have hFloc y (hy:C y):has_norm_higher_differential NX ev ZN C f m y (F m y).
    exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ m
      U C f (fun x hx=>hx.1) hopen y hy (F m y)).1 ((hF m).1 y hy.1)).
  have hGloc y (hy:C y):has_norm_higher_differential NX ev ZN C g m y (G m y).
    exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY Z ev ZN hZ m
      V C g (fun x hx=>hx.2) hopen y hy (G m y)).1 ((hG m).1 y hy.2)).
  have hs:=@norm_higher_differential_field_add R X Y NX NY hNX hNY Z ev ZN hZ C m
    f g (F m) (G m) hFloc hGloc x hx.
  have heq:z= F m x+G m x:=@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ
    C (fun y=>f y+g y) m x z (F m x+G m x) hz hs.
  rewrite heq.
  have hN:=continuous_multilinear_norm_is_norm hNY (hZ m).
  have h1:=hbF m hm x hx.1 (F m x) ((hF m).1 x hx.1).
  have h2:=hbG m hm x hx.2 (G m x) ((hG m).1 x hx.2).
  have ht:=le_trans (real_seminorm_triangle hN.1 (F m x) (G m x)) (lerD h1 h2).
  rewrite -mulrDl in ht.
  exact (le_trans ht (ler_wpM2r (ler0n R (m`!))
    (@analytic_positive_power_sum_bound R c d m hc hd hm))).
Qed.

(** Source for [norm_analytic_at_scale]: supporting the
    constant prefactors in the inverse-majorant expression,
    Federer 3.1.24, p. 240. Multiplication by a
    scalar b multiplies derivative norms by |b|; absorb
    this factor using the analytic bound (|b|+1)c. *)
Theorem norm_analytic_at_scale (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a b :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  @norm_analytic_at R X Y NX NY hNX hNY A (fun x=>b*:f x) a.
Proof.
move=>[U [c [ha [hUA [hf hb]]]]].
have hc:=norm_analytic_operator_witness_nonnegative ha hf hb.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
have [F hF]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY U f hf.
exists U,((`|b|+1)*c); split; first exact ha.
split; first exact hUA.
split.
- move=>k; exact (@norm_class_scale R X Y NX NY hNX hNY U f b k (hf k)).
- move=>m hm x hx z hz.
  have hs:=@norm_higher_differential_field_scale R X Y NX NY hNX hNY Z ev ZN hZ U m f
    (F m) b (hF m).1 x hx.
  have heq:z= b*:F m x:=@norm_higher_differential_unique R X Y NX NY hNX hNY Z ev ZN hZ U
    (fun y=>b*:f y) m x z (b*:F m x) hz hs.
  rewrite heq (real_seminorm_scale (continuous_multilinear_norm_is_norm hNY (hZ m)).1).
  have ht:=ler_wpM2l (normr_ge0 b) (hb m hm x hx (F m x) ((hF m).1 x hx)).
  rewrite mulrA in ht.
  exact (le_trans ht (ler_wpM2r (ler0n R (m`!))
    (@analytic_scalar_factor_bound R `|b| c m (normr_ge0 b) hc hm))).
Qed.
