(** Federer (1969), 2.5.7, p. 99: maximality forces the separating set S to
    be null after the improvement k+r*s is shown admissible. The original
    measure and the auxiliary negative measure are kept distinct throughout. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic CharacteristicFunctionUP
  LpDominatedDensityFamily.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_density_patch_strict_locus]: identity {k<k+r*s}=S
    in Federer 2.5.7, p. 99 It follows from r>0 on S and the exact
    characteristic laws, independently of measures. *)
Lemma positive_density_patch_strict_locus (R : realType) (X : Type)
    (S : set X) (s k r : X -> R) :
  is_characteristic_function S s -> (forall x, S x -> (0 < r x)%R) ->
  [set x | (k x < k x+r x*s x)%R]=S.
Proof.
move=> hs hr; apply/seteqP; split=> x hx.
- case: (pselect (S x))=> // hn.
  change (is_true (k x < k x+r x*s x)%R) in hx.
  by rewrite (characteristic_off_set hs hn) mulr0 addr0 ltxx in hx.
- change (is_true (k x < k x+r x*s x)%R).
  rewrite (characteristic_on_set hs hx) mulr1 ltrDl; exact: hr x hx.
Qed.

(** Source for [maximal_density_admissible_patch_null]: the original measure
    of S vanishes by maximality in Federer 2.5.7, p. 99 Admissibility of the
    improved density is a separate, proved premise; it does not follow
    merely from maximality. *)
Theorem maximal_density_admissible_patch_null (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) p q (P : (X -> R) -> R)
    (S : set X) (s k r : X -> R) :
  is_characteristic_function S s -> (forall x, (0 <= r x)%R) ->
  (forall x, S x -> (0 < r x)%R) ->
  (forall u, lp_dominated_density_family mu p q P u ->
    measure_almost_everywhere mu [set x | (k x <= u x)%R] ->
    ~ (0 < mu [set x | (k x < u x)%R])) ->
  lp_dominated_density_family mu p q P (fun x => (k x+r x*s x)%R) -> mu S=0.
Proof.
move=> hs hr0 hr hmax hpatch.
have hle : measure_almost_everywhere mu [set x | (k x <= k x+r x*s x)%R].
  apply: (@measure_almost_everywhere_mono R X mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  change (is_true (k x <= k x+r x*s x)%R); rewrite lerDl.
  case: (pselect (S x))=> hx.
  - by rewrite (characteristic_on_set hs hx) mulr1; exact: hr0.
  - by rewrite (characteristic_off_set hs hx) mulr0.
have hn := hmax _ hpatch hle.
rewrite (@positive_density_patch_strict_locus R X S s k r hs hr) in hn.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt.
exact/negP.
Qed.
