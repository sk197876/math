(** Federer (1969), 3.1.1, p. 209: the sharp upper and lower limits
    of image/source increment ratios in a nonzero normed source space. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOperatorNormUP NormOperatorNorm NormMinimumModulusUP NormMinimumModulus
  NormUnitSphereBounds NormRatioLimitUP NormDifferentialRayEstimate
  NormDifferentialEstimates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_ratio_bounds]: dividing the local
    increment estimates in Federer 3.1.1, p. 209, by a positive source
    increment norm. Both bounds hold in one neighbourhood. *)
Lemma norm_differential_ratio_bounds (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNY : is_real_norm NY)
    (A : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y) (n m : R) :
  has_norm_differential NX NY A f a L ->
  is_norm_operator_norm NX NY L n ->
  is_norm_minimum_modulus NX NY L m ->
  forall e : R, 0 < e -> exists d : R, 0 < d /\
    forall h, A (a+h) -> 0 < NX h < d ->
      m-e < norm_increment_ratio NX NY f a h /\
      norm_increment_ratio NX NY f a h < n+e.
Proof.
move=> hf hn hm e he.
have he2 : 0 < e/2 by lra.
have [d [hd hb]] := @norm_differential_norm_bounds R X Y NX NY hNY
  A f a L n m hf hn (norm_minimum_bound hm) (e/2) he2.
exists d; split=> // h ha /andP [hh hs].
have [hl hu] := hb h ha hs.
pose q := norm_increment_ratio NX NY f a h.
have hq : q*NX h = NY (f (a+h)-f a).
  by rewrite /q /norm_increment_ratio divfK // gt_eqF.
change (is_true ((m-e/2)*NX h <= NY (f (a+h)-f a))) in hl.
change (is_true (NY (f (a+h)-f a) <= (n+e/2)*NX h)) in hu.
change (m-e < q /\ q < n+e); split; by nra.
Qed.

(** Source for [norm_differential_sharp_limits]: the two displayed
    limsup/liminf identities in Federer 3.1.1, p. 209. Approximate unit
    extrema followed by sufficiently short rays prove sharpness, without
    compactness or attainment. A nonzero source is required for the
    finite limits: Federer's empty-set conventions are in 2.1.1, p. 51. *)
Theorem norm_differential_sharp_limits (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f : X -> Y)
    (a : X) (L : Hom X Y) (n m : R) :
  (exists x : X, x != 0) -> has_norm_differential NX NY A f a L ->
  is_norm_operator_norm NX NY L n -> is_norm_minimum_modulus NX NY L m ->
  is_norm_ratio_limsup NX NY A f a n /\ is_norm_ratio_liminf NX NY A f a m.
Proof.
move=> hX hf hn hm.
have hb := @norm_differential_ratio_bounds R X Y NX NY hNY A f a L n m hf hn hm.
split; constructor.
- move=> e he; have [d [hd h]] := hb e he.
  exists d; split=> // v ha hv; exact: (h v ha hv).2.
- move=> e d he hd; have he2 : 0 < e/2 by lra.
  have [v [hv hl]] := @norm_operator_unit_approximation R X Y NX NY hNX hNY L n hX hn (e/2) he2.
  have [h [ha [hh hq]]] := @norm_differential_unit_probe R X Y NX NY hNX hNY A f a L hf v hv (e/2) d he2 hd.
  exists h; split=> //; split=> //.
  move: hq; rewrite ler_norml=> /andP [hq _]; by lra.
- move=> e he; have [d [hd h]] := hb e he.
  exists d; split=> // v ha hv; exact: (h v ha hv).1.
- move=> e d he hd; have he2 : 0 < e/2 by lra.
  have [v [hv hl]] := @norm_minimum_unit_approximation R X Y NX NY hNX hNY L m hm (e/2) he2.
  have [h [ha [hh hq]]] := @norm_differential_unit_probe R X Y NX NY hNX hNY A f a L hf v hv (e/2) d he2 hd.
  exists h; split=> //; split=> //.
  move: hq; rewrite ler_norml=> /andP [_ hq]; by lra.
Qed.

(** Source for [norm_ratio_zero_source_exception]: zero-dimensional
    qualification of the finite-limit formulas of Federer 3.1.1, p. 209.
    There are no positive-norm increments in a zero source; hence no
    finite limit satisfies the sharpness law. This is a local clarification,
    not an entry in Federer's erratum; see 2.1.1, p. 51, for empty extrema. *)
Lemma norm_ratio_zero_source_exception (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (A : X -> Prop) (f : X -> Y) (a : X) (l : R) :
  (forall x : X, x = 0) ->
  ~ is_norm_ratio_limsup NX NY A f a l /\
  ~ is_norm_ratio_liminf NX NY A f a l.
Proof.
move=> hzero; have h1 : (0 : R) < 1 by exact: ltr01.
split=> hl.
- have [h [_ [hh _]]] := norm_ratio_sharp_upper hl h1 h1.
  by rewrite (hzero h) (real_seminorm_zero hNX.1) ltxx in hh.
- have [h [_ [hh _]]] := norm_ratio_sharp_lower hl h1 h1.
  by rewrite (hzero h) (real_seminorm_zero hNX.1) ltxx in hh.
Qed.

(** Source for [norm_differential_ratio_limits]: the displayed limits
    in Federer 3.1.1, p. 209, with the opaque operator norm and minimum
    modulus as their actual values. Their private extrema witnesses do
    not enter this proof. The source is nonzero, as required for finite
    sharp limits of punctured increment ratios. *)
Theorem norm_differential_ratio_limits (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (hX : exists x : X, x != 0)
    (A : X -> Prop) (f : X -> Y) (a : X) (L : Hom X Y)
    (hf : has_norm_differential NX NY A f a L) :
  is_norm_ratio_limsup NX NY A f a
    (norm_operator_norm hNX hNY (norm_differential_bounded hf)) /\
  is_norm_ratio_liminf NX NY A f a (norm_minimum_modulus hNX hNY hX L).
Proof.
exact: (@norm_differential_sharp_limits R X Y NX NY hNX hNY A f a L
  _ _ hX hf (norm_operator_norm_specification hNX hNY (norm_differential_bounded hf))
  (norm_minimum_modulus_specification hNX hNY hX L)).
Qed.
