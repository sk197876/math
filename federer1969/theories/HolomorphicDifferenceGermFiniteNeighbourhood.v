(** Federer (1969), 3.4.12, p. 339: the real-case
    component theorem supplies the final neighbourhood for any
    actual representative of a holomorphic difference germ. First
    restrict inside its original germ-agreement neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteCoordinates RealNormUP NormMetric ScalarRestriction ComplexScalarSealed ComplexNormUP
  HolomorphicCoordinateNorm HolomorphicVarietyGermUP HolomorphicDifferenceFiniteNeighbourhood SetGermUP SetGermExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
(** Source for [holomorphic_difference_germ_finite_neighbourhood]:
    choose the finite-component regular neighbourhood after the
    exceptional strata, extending 3.4.8(11), p. 335, under
    3.4.12, p. 339. Count components after restricting the
    actual representative, rather than restricting a previous count. *)
Theorem holomorphic_difference_germ_finite_neighbourhood (R:realType) n
    (S E D:set (coordinate_space (ComplexScalars.C R) n)):
  let X:=coordinate_space (ComplexScalars.C R) n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  let T:=Topological.clone (real_norm_metric_space hNX) _ in
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0 S) ->
  @is_holomorphic_variety_germ R X NX hNX 0 (@set_germ T 0 E) ->
  @set_germ T 0 D = @set_germ T 0 (S `\` E) ->
  forall N:set X,@open T N ->N 0 ->
    exists O:set X,@open T O /\O 0 /\O `<=` N /\
      finite_set (@connected_component T (O `&` D) @` (O `&` D)).
Proof.
move=>X NX hNX T hS hE hDifference N hN hN0.
have [W [hW [hW0 hEqual]]]:=(@set_germ_equality_original T 0 D (S `\` E)).1 hDifference.
have [O [hO [hO0 [hONW hFinite]]]]:=@holomorphic_difference_finite_neighbourhood R n S E hS hE
  (N `&` W) (openI hN hW) (conj hN0 hW0).
have hSame:O `&` D = O `&` (S `\` E).
  apply/seteqP;split=>x [hOx hx];split;first exact:hOx.
  - have h:((S `\` E) `&` W) x by rewrite -hEqual;split;[exact:hx|exact:(hONW x hOx).2].
    exact:h.1.
  - exact:hOx.
  - have h:(D `&` W) x by rewrite hEqual;split;[exact:hx|exact:(hONW x hOx).2].
    exact:h.1.
exists O;split;first exact:hO.
split;first exact:hO0.
split;first by move=>x hx;exact:(hONW x hx).1.
by rewrite hSame.
Qed.
