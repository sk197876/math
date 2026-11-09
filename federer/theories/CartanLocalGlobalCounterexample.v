(** Federer (1969), 3.4.5, p. 321: an analytic
    set in an open ambient domain need not be a variety
    defined by finitely many global analytic equations.
    The adapted real surface follows Cartan (1957), pp. 97–99. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetric NormAnalyticUP FiniteAnalyticVarietyUP AnalyticVarietyGermUP CartanSurfaceUP CartanSurfaceSealed
  CartanSurfaceGeometry CartanSurfaceLocalAnalytic CartanGlobalAnalyticRigidity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [cartan_surface_not_global_variety]: every
    actual global analytic defining function would be zero
    everywhere, contradicting the proved properness of the
    actual surface; this proves the converse failure in
    3.4.5, p. 321, with no additional hypothesis. *)
Theorem cartan_surface_not_global_variety (R:realType):
  ~is_finite_analytic_variety (inner_norm_real_norm (@euclidean_inner_productP R 3))
    setT (@CartanSurface.set R).
Proof.
move=>[_ [I [f [hAnalytic hMembership]]]].
have hZero i v:f i v=0.
  apply:(cartan_global_analytic_vanisher_zero (hAnalytic i))=>w hw.
  exact:((hMembership w).1 hw).2 i.
have [v hOutside]:=@cartan_surface_is_proper R.
apply:hOutside;apply:(hMembership v).2;split;first exact:Logic.I.
exact:(fun i=>hZero i v).
Qed.

(** Source for [analytic_set_need_not_be_global_variety]: the
    actual closed, proper analytic set in the open domain
    R^3 fails to be a global analytic variety, as
    asserted in 3.4.5, p. 321. The same
    opaque surface satisfies every displayed property. *)
Theorem analytic_set_need_not_be_global_variety (R:realType):
  exists S:set (R_n R 3),
    @closed (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R 3))) S /\
    (exists v,~S v) /\
    is_analytic_set_in (inner_norm_real_norm (@euclidean_inner_productP R 3)) setT S /\
    ~is_finite_analytic_variety (inner_norm_real_norm (@euclidean_inner_productP R 3)) setT S.
Proof.
exists (@CartanSurface.set R).
have [hClosed [hProper hAnalytic]]:=@cartan_surface_closed_proper_locally_analytic R.
split;first exact:hClosed.
split;first exact:hProper.
split;[exact:hAnalytic|exact:cartan_surface_not_global_variety].
Qed.
