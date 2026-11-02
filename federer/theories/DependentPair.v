(** Federer (1969), 1.7.5, p. 33: linear dependence in the equality case of
    the pairing inequality. Supporting two-vector algebra. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import IndependentPair FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [independent_pair_iff_not_scaled]: Federer
    1.7.5, p. 33, supporting criterion: with y nonzero,
    x and y are independent exactly when x is no multiple of y. *)
Lemma independent_pair_iff_not_scaled (R : fieldType) (V : lmodType R)
    (x y : V) (hy : y != 0) :
  independent_pair x y <-> forall a : R, x != a *: y.
Proof.
split; first exact: independent_pair_not_scaled.
move=> hn c hc i; rewrite big_bool /= in hc.
case hct : (c true == 0).
- have hcz : c true = 0 by apply/eqP.
  rewrite hcz scale0r add0r in hc.
  have hcf : c false = 0.
    move/eqP: hc; rewrite scaler_eq0 (negbTE hy) orbF; exact/eqP.
  by case: i; [exact hcz | exact hcf].
- have hcn : c true != 0 by rewrite hct.
  have hh : c true *: x = -(c false *: y).
    by apply/eqP; rewrite -addr_eq0 hc eqxx.
  have hh' := congr1 (fun z => (c true)^-1 *: z) hh.
  rewrite scalerA mulVf // scale1r scalerN scalerA in hh'.
  have he : x = (-c false / c true) *: y.
    rewrite hh' mulNr scaleNr; congr (-(_ *: y)); exact: mulrC.
  by move: (hn (-c false / c true)); rewrite -he eqxx.
Qed.

(** Source for [dependent_pair_cases]: Federer 1.7.5,
    p. 33, supporting classification of dependent pairs, including
    the zero vector, for the complete equality criterion. *)
Theorem dependent_pair_cases (R : fieldType) (V : lmodType R) (x y : V) :
  ~ independent_pair x y <-> y = 0 \/ exists a : R, x = a *: y.
Proof.
split.
- move=> hn; case: (eqVneq y 0) => [->|hy]; first by left.
  right; apply: contrapT => hnone; apply: hn.
  apply: (proj2 (independent_pair_iff_not_scaled x hy)) => a.
  apply/eqP=> ha; apply: hnone; by exists a.
- move=> [hy|[a ha]] hi.
  + by move: (independent_pair_right_nonzero hi); rewrite hy eqxx.
  + by move: (independent_pair_not_scaled hi a); rewrite -ha eqxx.
Qed.
