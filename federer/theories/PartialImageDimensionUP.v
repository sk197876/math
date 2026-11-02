(** Federer (1969), 3.2.32, p. 269: the dimension bound
    on the image of the actual partial approximate differential.
    Specify its image as a vector space with a finite basis
    dimension bounded by mu; no plane or rank is selected. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ModuleQuotient SubspaceCarrier GrassmannAbbreviations GrassmannSubspaces PartialFunctionUP PartialMetricLipschitz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_partial_image_dimension_at_most]: the condition
    dim im ap Df(x)<=mu defining X in Federer 3.2.32,
    p. 269. An actual r-dimensional vector space is the exact
    range of the partial graph, and r<=mu. This uses the
    existing independent Grassmann basis laws; it neither extends
    the partial domain nor introduces a chosen image plane. *)
Definition is_partial_image_dimension_at_most (R:realType) n v mu
    (d:partial_function (R_n R n) (R_n R v)):Prop:=
  exists r (P:GrassmannSubspaces.G (R_n R v) r),
    (r<=mu)%N /\partial_function_range d=[set y|grassmann_val P y].
