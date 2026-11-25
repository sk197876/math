(** Federer (1969), 4.1.6, pp. 352–355:
    the norm-bounded coefficient functionals separate
    arbitrary normed vector coefficients. Reuse the
    original Hahn–Banach norming functional of
    2.4.12; neither completeness nor separability is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP ContinuousRealFunctional Alternating FormCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [unit_bounded_functionals_separate]: the
    original normed coefficients are determined by
    their bounded real evaluations, supporting the
    vector-coefficient extension of Federer 4.1.6,
    pp. 352–355. *)
Lemma unit_bounded_functionals_separate (R:realType) (W:lmodType R)
    (NW:W->R) (hNW:is_real_norm NW) (y z:W):
  (forall M:Hom W R^o,(forall w,`|M w|<=NW w)->M y=M z)->y=z.
Proof.
move=>hValues.
have [g [_ [hBound hNorm]]]:=continuous_norming_real_functional hNW (y-z).
have hEqual:=hValues (hom_of_linear g) hBound.
change (g y=g z) in hEqual.
have hZero:NW (y-z)=0 by rewrite -hNorm linearB hEqual subrr.
have hVector:=hNW.2 _ hZero; by move/eqP:hVector; rewrite subr_eq0=>/eqP.
Qed.

(** Source for [unit_coefficient_maps_separate_forms]:
    bounded scalar coefficient projections determine
    the original vector-valued form,
    supporting Federer 4.1.6, p. 355. *)
Lemma unit_coefficient_maps_separate_forms (R:realType) (V W:lmodType R)
    (NW:W->R) (hNW:is_real_norm NW) m (a b:A_m V W m):
  (forall M:Hom W R^o,(forall w,`|M w|<=NW w)->
    form_coefficients (hom_as_linear M) a=form_coefficients (hom_as_linear M) b)->a=b.
Proof.
move=>hValues; apply:form_ext=>t.
apply:(unit_bounded_functionals_separate hNW)=>M hBound.
have hEqual:=congr1 (fun phi:A_m V R^o m=>phi t) (hValues M hBound).
by rewrite !form_coefficientsE in hEqual.
Qed.
