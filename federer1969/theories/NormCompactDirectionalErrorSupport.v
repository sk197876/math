(** Federer (1969), 4.1.1, p. 346: C1
    quotient errors and their actual directional
    derivative have one compact support bound.
    This supplies the vanishing integral argument
    with exactly first-order regularity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis SmoothCompactSet
  SmoothCompactTranslationTube NormClassOneDirectionalField.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_compact_directional_error_support]:
    one compact C contains all directional
    quotient errors of a C1 compactly supported
    function for |t|<=1, supporting the derivative
    integral in Federer 4.1.1, p. 346. *)
Theorem norm_compact_directional_error_support (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    d (b:'I_d->X) (hb:is_basis b) (K:smooth_compact_set hNX (fun _=>True))
    (f:X->Y) (D:X->Hom X Y) (v:X):
  (forall x,~smooth_compact_carrier K x ->f x=0) ->
  (forall x,has_norm_differential NX NY (fun _=>True) f x (D x)) ->
  exists C:smooth_compact_set hNX (fun _=>True),forall t:R,`|t|<=1 ->forall x,
    ~smooth_compact_carrier C x ->t^-1*:(f (x+t*:v)-f x)-D x v=0.
Proof.
move=>hZero hD.
have [C [hKC hShift]]:=@smooth_compact_translation_tube R X NX hNX d b hb K v.
exists C=>t ht x hx.
have hNoK:~smooth_compact_carrier K x by move=>hk; exact:hx (hKC x hk).
have hNoShift:~smooth_compact_carrier K (x+t*:v) by move=>hk; exact:hx (hShift t ht x hk).
rewrite (hZero _ hNoK) (hZero _ hNoShift)
  (@norm_differential_zero_off_compact R X Y NX NY hNX hNY K f D hZero hD x hNoK)
  hom_zeroE subrr scaler0 subrr; reflexivity.
Qed.
