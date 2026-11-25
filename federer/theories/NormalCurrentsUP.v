(** Federer (1969), 4.1.7, p. 358: local
    normality, normality, normal mass and the
    original normal-current classes. Degree zero
    retains the explicit printed exception; no
    negative-degree boundary is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct SmoothCompactSet CurrentSpaces CurrentBoundary
  CurrentIntegrationCriterion CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section NormalCurrentsUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT := (real_norm_metric_space hNX).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation C := (fun m=>@current_space R h2 n U hU m).
Local Notation M := (fun m=>@CurrentMass.value R h2 n m U hU).

(** Source for [has_representable_current_boundary]:
    either the positive-degree boundary is representable
    by integration or the current degree is zero,
    Federer 4.1.7, p. 358, normality paragraph. *)
Definition has_representable_current_boundary m:C m->Prop:=
  match m as d return C d->Prop with
  |0%N=>fun _=>True
  |d.+1=>fun T=>@is_integration_representable_current R h2 n d U hU
    (@current_boundary R h2 n d U hU T)
  end.

(** Source for [is_locally_normal_current]: the
    original local normality definition, Federer
    4.1.7, p. 358. Both the current
    and its positive-degree boundary are represented
    by integration. *)
Definition is_locally_normal_current m (T:C m):Prop:=
  @is_integration_representable_current R h2 n m U hU T /\
    has_representable_current_boundary T.

(** Source for [is_normal_current]: local normality
    and compact support in U define a
    normal current, Federer 4.1.7, p. 358. *)
Definition is_normal_current m (T:C m):Prop:=
  is_locally_normal_current T /\compact [set x:XT|@current_support R h2 n U hU m T x].

(** Source for [current_normal_mass]: N(T)=M(T)
    in degree zero and N(T)=M(T)+M(boundary T)
    in positive degree, Federer 4.1.7,
    p. 358, displayed definition. *)
Definition current_normal_mass m:C m->\bar R:=
  match m as d return C d->\bar R with
  |0%N=>M 0
  |d.+1=>fun T=>(M d.+1 T+M d (@current_boundary R h2 n d U hU T))%E
  end.

(** Source for [normal_currents]: the original
    class N_m(U), Federer 4.1.7,
    p. 358. Vector-space closure is proved
    separately for this independently specified set. *)
Definition normal_currents m:set (C m):=[set T|is_normal_current T].

(** Source for [locally_normal_currents]: the original
    class N_m^loc(U), Federer 4.1.7,
    p. 358. No compact-support premise
    is imposed on this class. *)
Definition locally_normal_currents m:set (C m):=[set T|is_locally_normal_current T].

(** Source for [normal_currents_supported_in]: the
    original N_(m,K)(U) consists of normal
    currents supported in the prescribed compact
    subset K of U, Federer 4.1.7,
    p. 358. *)
Definition normal_currents_supported_in m (K:smooth_compact_set hNX U):set (C m):=
  [set T|is_normal_current T /\@current_support R h2 n U hU m T `<=` smooth_compact_carrier K].
End NormalCurrentsUP.
