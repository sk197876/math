(** Federer (1969), 4.1.8, p. 362: the
    original affine scalar parameter has the original
    Lebesgue image measure. Reuse the all-set affine
    volume law proved from 2.7.16, pp. 134–135;
    only the inverse-image presentation is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground LebesgueScalarMeasure ScalarAffineLebesgue
  MeasureUP MeasurePushforward MeasureRestriction MeasureScaleIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_affine_pushforward_measure]: the
    original affine map t to r t+u pushes
    scalar Lebesgue measure to |r|^{-1} times
    that measure, supporting the interval formula in
    Federer 4.1.8, p. 362, by 2.7.16,
    pp. 134–135. Every target set is retained. *)
Lemma scalar_affine_pushforward_measure (R:realType) (r u:R):r!=0 ->
  measure_pushforward (fun t:real_line_metric R=>r*t+u) (@lebesgue_scalar_measure R)=
    measure_scale `|r|^-1 (@lebesgue_scalar_measure R).
Proof.
move=>hr.
pose F t:=r*t+u.
pose G s:=r^-1*(s-u).
have hGF:cancel F G by move=>t;rewrite /F /G addrK mulrA mulVf // mul1r.
have hFG:cancel G F by move=>s;rewrite /F /G mulrA mulfV // mul1r subrK.
apply:funext=>A.
have hPre:F @^-1` A=G @` A.
  apply/seteqP;split.
  - move=>t ht;exists (F t)=>//;exact:hGF.
  - move=>s [t ht <-];change (A (F (G t)));by rewrite hFG.
have hFormula:G=(fun s=>r^-1*s+ -(r^-1*u)).
  apply:funext=>s;by rewrite /G mulrBr.
have hInverse:r^-1!=0 by rewrite invr_eq0.
have hVolume:=@scalar_affine_lebesgue_image R r^-1 (-(r^-1*u)) A hInverse.
rewrite -hFormula in hVolume.
by rewrite /measure_pushforward /measure_scale hPre hVolume normfV.
Qed.

(** Source for [scalar_affine_restricted_pushforward]: the
    same original affine image measure restricted to
    a source set is its original target restriction
    with factor |r|^{-1}, supporting Federer 4.1.8,
    p. 362. No measurability of the source set
    is required for this outer-measure identity. *)
Lemma scalar_affine_restricted_pushforward (R:realType) (r u:R) (S:set (real_line_metric R)):
  r!=0->measure_pushforward (fun t:real_line_metric R=>r*t+u)
    (measure_restrict (@lebesgue_scalar_measure R) S)=
    measure_scale `|r|^-1 (measure_restrict (@lebesgue_scalar_measure R)
      ((fun t:real_line_metric R=>r*t+u) @` S)).
Proof.
move=>hr;pose F t:=r*t+u.
have hInj:injective F.
  move=>s t h;have h':r*s=r*t:=addIr u h.
  exact:(mulfI hr h').
apply:funext=>T.
have hSets:S `&` (F @^-1` T)=F @^-1` ((F @` S) `&` T).
  apply/seteqP;split=>t.
  - move=>[ht hT];split=>//;by exists t.
  - move=>[[s hs hEq] hT];split=>//;by rewrite -(hInj _ _ hEq).
rewrite /measure_pushforward /measure_restrict /measure_scale hSets.
have hPush:=congr1 (fun mu=>mu ((F @` S) `&` T)) (@scalar_affine_pushforward_measure R r u hr).
exact:hPush.
Qed.
