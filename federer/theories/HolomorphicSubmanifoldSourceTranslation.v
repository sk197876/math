(** Federer (1969), 3.4.12, p. 339: open restrictions
    of original holomorphic manifolds preserve their complex dimension.
    Restrict the existing chart and retain its original complex plane. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import NormBoundedLinearTopology FiniteCoordinates ComplexNormUP HolomorphicCoordinateNorm Hom HolomorphicDiffeomorphismOperations NormClosureLaws RealNormUP ScalarRestriction ComplexScalarSealed NormMetric NormDifferentialUP
  NormAnalyticLocal NormAnalyticUP HolomorphicUP HolomorphicDiffeomorphismUP
  HolomorphicDiffeomorphismRestriction HolomorphicSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.


(** Source for [holomorphic_submanifold_source_translation]: translate
    the original holomorphic manifold charts to any prescribed centre,
    extending 3.4.10, p. 337, under 3.4.12, p. 339.
    Retain the same actual complex plane and dimension. *)
Theorem holomorphic_submanifold_source_translation (R:realType) n m
    (S:set (coordinate_space (ComplexScalars.C R) n)) (c:coordinate_space (ComplexScalars.C R) n):
  let X:=coordinate_space (ComplexScalars.C R) n in
  let NX:=@holomorphic_coordinate_norm R n in
  let hNX:=complex_norm_real (@holomorphic_coordinate_norm_laws R n) in
  @is_holomorphic_submanifold R X NX hNX m S ->
  @is_holomorphic_submanifold R X NX hNX m [set x|S (x-c)].
Proof.
move=>X NX hNX hS b hb.
pose M:=Topological.clone (real_norm_metric_space hNX) _.
pose u:=fun x:M=>(x-c:M).
pose v:=fun x:M=>(x+c:M).
have hUContinuous:continuous u.
  have hSame:u=(fun x:X=>-c+x) by apply:funext=>x;rewrite /u addrC.
  rewrite hSame;exact:real_norm_metric_translate_continuous.
have hUV:cancel v u by move=>x;rewrite /u /v addrK.
have hVU:cancel u v by move=>x;rewrite /u /v subrK.
have [T [C [sigma [tau [Z [hTb [hD hImage]]]]]]]:=hS (u b) hb.
pose W:set X:=u @^-1` T.
have hTInterior x (hx:T x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX T x.
  have hOpen:=norm_analytic_domain_open (holomorphic_diffeomorphism_forward hD).1;rewrite openE in hOpen.
  exact:(@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX T x).2 (hOpen x hx).
have hWOpen:@open M W:=@open_comp M M u T (fun x _=>hUContinuous x)
  (norm_analytic_domain_open (holomorphic_diffeomorphism_forward hD).1).
have hWInterior x (hx:W x):@norm_domain_interior R (restricted_space (ComplexScalars.embed R) X) NX W x.
  apply:(@norm_domain_interior_neighbourhood R (restricted_space (ComplexScalars.embed R) X) NX hNX W x).2.
  have h:=hWOpen;rewrite openE in h;exact:h x hx.
have hSame:(fun x:X=>True /\T (u x))=W.
  apply:funext=>x;apply:propext;split;[by case|by move=>hx;split].
have hTranslation:=@holomorphic_translation_diffeomorphism R X NX hNX c.
have hRestricted:=holomorphic_diffeomorphism_target_restriction hTranslation (fun _ _=>Logic.I) hTInterior.
change (is_holomorphic_diffeomorphism hNX (fun x:X=>True /\T (u x)) T u v) in hRestricted.
rewrite hSame in hRestricted.
have hComposite:=holomorphic_diffeomorphism_composition hRestricted hD.
exists W,C,(fun x=>sigma (u x)),(fun y=>v (tau y)),Z;split.
- have hbT:T (u b):=norm_domain_interior_member hNX hTb.
  exact:hWInterior b hbT.
split;first exact:hComposite.
rewrite -hImage;apply/seteqP;split.
- move=>y [x [hxS hxW] hXY];exists (u x);last exact:hXY;by split.
- move=>y [x [hxS hxT] hXY];exists (v x).
  + split;[change (S (u (v x)))|change (T (u (v x)))];by rewrite hUV.
  + by rewrite hUV.
Qed.
