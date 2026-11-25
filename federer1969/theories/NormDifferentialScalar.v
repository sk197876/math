(** Federer (1969), 3.1.1, p. 209: for a real one-dimensional source,
    differentiability is equivalent to existence of the curve derivative,
    and L(v)=v f'(a). The interior-domain requirement is retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialDirectional NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [real_source_linear_evaluation]: supporting algebra for
    the real-source case of Federer 3.1.1, p. 209: a linear map on the
    real line is determined by its value at one. *)
Lemma real_source_linear_evaluation (R : realType) (Y : lmodType R)
    (L : Hom R^o Y) (t : R) : L t = t *: L 1.
Proof.
have ht : t *: (1 : R^o) = t by change (t*1=t); rewrite mulr1.
by rewrite -{1}ht linearZ.
Qed.

(** Source for [norm_differential_real_source]: Federer 3.1.1, p. 209,
    the first special case. At an interior domain point the differential
    is equivalent to the existing two-sided curve derivative, and that
    derivative is L(1). No finite dimension of the target is required. *)
Theorem norm_differential_real_source (R : realType) (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R -> Prop)
    (f : R -> Y) (a : R) (L : Hom R^o Y) :
  has_norm_differential (fun t : R^o => `|t|) NY A f a L <->
  norm_domain_interior (fun t : R^o => `|t|) A a /\
    has_normed_curve_derivative NY f a (L 1).
Proof.
split.
- move=> hf; split; first exact: norm_differential_interior hf.
  have hd := norm_differential_directional_limit
    (@scalar_absolute_value_norm R) hNY hf (1 : R^o).
  move=> e he; have [d [hd0 hb]] := hd e he.
  exists d; split=> // t ht.
  have hscale : t *: (1 : R^o) = t by change (t*1=t); rewrite mulr1.
  have hh := hb t ht; by rewrite hscale in hh.
- move=> [ha hd]; split=> //.
  + exists (NY (L 1)); split; first exact: real_seminorm_nonnegative hNY.1 _.
    by move=> h; rewrite [L h]real_source_linear_evaluation
      (real_seminorm_scale hNY.1) mulrC.
  + move=> e he; have [d [hd0 hb]] := hd e he.
    exists d; split=> // h _ hs.
    have [->|hh] := eqVneq h 0.
      by rewrite addr0 subrr linear0 subrr (real_seminorm_zero hNY.1) normr0 mulr0.
    have hn : 0 < `|h| by rewrite normr_gt0.
    have hsmall : 0 < `|h| < d by apply/andP; split.
    have hbound := hb h hsmall.
    have heq : f (a+h)-f a-L h = h *: (h^-1 *: (f (a+h)-f a)-L 1).
      by rewrite [RHS]scalerBr scalerA mulfV // scale1r [L h]real_source_linear_evaluation.
    rewrite heq (real_seminorm_scale hNY.1).
    apply: ltW; rewrite mulrC ltr_pM2r //.
Qed.

(** Source for [norm_differentiable_real_source]: Federer 3.1.1, p. 209,
    first special case, with existence on both sides. The interior-domain
    condition belongs to the opening definition. A curve derivative v
    supplies the linear approximation t maps to t times v. *)
Theorem norm_differentiable_real_source (R : realType) (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (A : R -> Prop)
    (f : R -> Y) (a : R) :
  norm_differentiable_at (fun t : R^o => `|t|) NY A f a <->
  norm_domain_interior (fun t : R^o => `|t|) A a /\
    exists v : Y, has_normed_curve_derivative NY f a v.
Proof.
split.
- move=> [L hf].
  have [ha hd] := proj1 (@norm_differential_real_source R Y NY hNY A f a L) hf.
  split=> //; by exists (L 1).
- move=> [ha [v hv]].
  have hl : linear (fun t : R^o => t *: v).
    by move=> c t s; rewrite /= scalerDl scalerA.
  pose L := @HomMap R R^o Y (fun t => t *: v) (introT (asboolP _) hl).
  exists L; apply: (proj2 (@norm_differential_real_source R Y NY hNY A f a L)).
  split=> //; change (has_normed_curve_derivative NY f a (1 *: v)).
  by rewrite scale1r.
Qed.
