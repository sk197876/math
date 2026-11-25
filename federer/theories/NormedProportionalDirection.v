(** Federer (1969), 4.1.25, p. 383, last displayed
    formula: proportional vectors have the same direction
    up to sign after normalization. This supporting
    computation uses absolute homogeneity from 2.4.12,
    p. 86, and the associated-space criterion of 1.6.1,
    p. 24. The supplied norm remains abstract. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import ModuleQuotient SubspaceCarrier RealNormUP ExteriorGrading SimpleVectors.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_proportional_direction]: the signed
    norm-and-unit-direction identity used in Federer 4.1.25,
    p. 383. A zero first vector is allowed; normalization
    is applied only to the nonzero second vector. No
    inner product, completeness or dimension is assumed. *)
Theorem normed_proportional_direction (R : realType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (xi eta : V) (c : R) :
  eta != 0 -> xi = c *: eta ->
  exists s : R, (s = 1 \/ s = -1) /\
    xi = (s * N xi) *: ((N eta)^-1 *: eta).
Proof.
move=> hEta hValue.
have hPositive : 0 < N eta.
  by rewrite (@real_norm_positive R V N hN.1 hN.2 eta) hEta.
have hCancel : N eta * (N eta)^-1 = 1.
  by rewrite mulfV ?gt_eqF.
have hCoefficient s (hSign : c = s * `|c|) :
    (s * N xi) * (N eta)^-1 = c.
  rewrite hValue (real_seminorm_scale hN.1).
  have hAssociate : (s * (`|c| * N eta)) * (N eta)^-1 =
      (s * `|c|) * (N eta * (N eta)^-1) by ring.
  by rewrite hAssociate hCancel mulr1 -hSign.
have hDirection s (hSign : c = s * `|c|) :
    xi = (s * N xi) *: ((N eta)^-1 *: eta).
  by rewrite scalerA (hCoefficient s hSign) -hValue.
have [hC | hC] := lerP 0 c.
- exists 1; split; first by left.
  apply: hDirection; by rewrite mul1r (ger0_norm hC).
- exists (-1); split; first by right.
  apply: hDirection.
  by rewrite (ler0_norm (ltW hC)) mulN1r opprK.
Qed.

(** Source for [simple_common_plane_signed_direction]: the
    same signed relation for the nonzero terms associated
    with one plane in Federer 4.1.25, p. 383. The earlier
    1.6.1 associated-space criterion supplies proportionality;
    no new choice of frame or exterior algebra is used. *)
Theorem simple_common_plane_signed_direction (R : realType)
    (h2 : (1+1 : R) != 0) (V : lmodType R) m
    (N : exterior_power V m -> R) (hN : is_real_norm N)
    (xi eta : exterior_power V m) :
  xi != 0 -> eta != 0 -> simple eta ->
  (forall v, FedererSimple.T xi v <-> FedererSimple.T eta v) ->
  exists s : R, (s = 1 \/ s = -1) /\
    xi = (s * N xi) *: ((N eta)^-1 *: eta).
Proof.
move=> hXi hEta hSimple hPlane.
have [c [_ hValue]] := (proj1 (@simple_associated_equal R h2 V m
  xi eta hXi hEta hSimple)) hPlane.
exact: (@normed_proportional_direction R (exterior_power V m) N hN
  xi eta c hEta hValue).
Qed.
