(** Federer (1969), 3.2.23, p. 260: Borel regularity under
    the usual Cartesian coordinate identification. This supporting
    general-topology consequence uses only Borel preimages and the
    equal-mass Borel hull law of 2.2.3, pp. 61–62. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import MeasureUP MeasurePushforward PushforwardMeasurableSets
  BorelRegularMeasureUP TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [borel_regular_homeomorphic_pushforward]: supporting
    coordinate change in the final Borel-regularity argument of
    Federer 3.2.23, p. 260. A homeomorphism transports equal-mass
    Borel hulls by its inverse preimages. No finite mass, local
    compactness or properness premise is needed. *)
Theorem borel_regular_homeomorphic_pushforward (R:realType) (X Y:topologicalType)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->Y) (g:Y->X):
  cancel f g ->cancel g f ->continuous f ->continuous g ->
  is_borel_regular_measure mu ->is_borel_regular_measure (measure_pushforward f mu).
Proof.
move=>hFG hGF hF hG hRegular; constructor.
- move=>U hU; apply:pushforward_measurable_from_preimage.
  exact:(borel_regular_borel_measurable hm hRegular
    (@continuous_borel_preimage X Y f hF U (open_borel_set hU))).
- move=>A; have [B [hCover [hB hValue]]]:=borel_regular_cover hRegular (f @^-1` A).
  exists (g @^-1` B); split.
  + move=>y hy; apply:hCover; change (A (f (g y))); by rewrite hGF.
  + split; first exact:(@continuous_borel_preimage Y X g hG B hB).
    have hPre:f @^-1` (g @^-1` B)=B.
      apply/seteqP; split=>x hx.
      - have h:B (g (f x)):=hx; by rewrite hFG in h.
      - change (B (g (f x))); by rewrite hFG.
    by rewrite /measure_pushforward hPre.
Qed.
